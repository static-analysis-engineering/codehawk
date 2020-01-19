{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Monad
import Development.Shake
import Development.Shake.Classes
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import Data.Char
import Data.List
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import System.IO.Unsafe
import System.Directory

ignoredOriginalFiles :: [String] -> [String]
ignoredOriginalFiles inList =
    let nonBuild = filter (\file -> not $ elem "_build" $ splitDirectories file) inList in
    let nonChCil = filter (\file -> not $ elem "cchcil" $ splitDirectories file) nonBuild in
    let nonCil = filter (\file -> not $ elem "cil-1.7.3-develop" $ splitDirectories file) nonChCil in
    let nonGui = filter (\file -> not $ elem "cchgui" $ splitDirectories file) nonCil in
    let nonGui2 = filter (\file -> not $ elem "CH_gui" $ splitDirectories file) nonGui in
    let nonparser = filter (\file -> not $ elem "chifparser" $ splitDirectories file) nonGui2 in
    nonparser

moduleToFile :: String -> String
moduleToFile modul =
    if modul == "IO" then "IO" else
        let firstChar : rest = modul in
        (toLower firstChar) : rest

dropLibraryModules :: [String] -> [String]
dropLibraryModules modules =
    let knownLibraryModules = HashSet.fromList ["Big_int_Z", "Array", "Str", "Hashtbl", "Q", "Int64", "Int32", "Unix", "Printf", "List", "Seq", "Bytes", "Map", "Scanf", "String", "Stdlib", "Buffer", "Set", "Pervasives", "Arg", "LargeFile", "Char", "SymbolCollections", "Filename", "Obj", "LanguageFactory", "IntCollections", "StringCollections", "Char", "VariableCollections", "Lexing", "Sys", "Printexc", "FactorCollections", "Callback", "ParseError", "Gc", "StringMap", "Stack", "Digest"] in
    filter (\modul -> not $ HashSet.member modul knownLibraryModules) modules

main :: IO ()
main = do
    ver <- getHashedShakeVersion ["Shakefile.hs"]
    let defaultShakeOptions = shakeOptions {
        shakeFiles="_build",
        shakeProgress = progressSimple,
        shakeLint = Just LintBasic,
        shakeVersion = ver,
        shakeThreads = 0 -- Use the number of cpus
    }
    runBuild defaultShakeOptions

newtype ModuleDependencies = ModuleDependencies String deriving (Show,Typeable,Eq,Hashable,Binary,NFData)
type instance RuleResult ModuleDependencies = [String]

runBuild :: ShakeOptions -> IO ()
runBuild options = shakeArgs options $ do

    originalToMap <- liftIO $ unsafeInterleaveIO $ do
        mlis <- getDirectoryFilesIO "" ["CH_extern//*.mli", "CH//*.mli", "CHC//*.mli", "CHB//*.mli"]
        mls <- getDirectoryFilesIO "" ["CH_extern//*.ml", "CH//*.ml", "CHC//*.ml", "CHB//*.ml"]
        let inputs = ignoredOriginalFiles $ mlis ++ mls
        let pairs = [(takeFileName file, file) | file <- inputs]
        return $ Map.fromList pairs

    phony "clean" $ do
        putNormal "Cleaning files in _bin, _build"
        removeFilesAfter "_bin" ["//*"]
        removeFilesAfter "_build" ["//*"]

    "_build/*.mli" %> \out ->
        case originalToMap !? dropDirectory1 out of
             Just original -> copyFileChanged original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)

    getModuleDeps <- addOracleCache $ \(ModuleDependencies file) -> do
        need [file]
        Stdout dependencies_str <- cmd "ocamldep -modules" file
        let [(_, modules)] = parseMakefile dependencies_str
        return $ dropLibraryModules modules

    "_build/*.cmi" %> \out -> do
        let mli = out -<.> "mli"
        mli_dependencies <- getModuleDeps $ ModuleDependencies mli
        need $ [mli] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        cmd_ (Cwd "_build") "ocamlfind ocamlopt -opaque -package zarith" (takeFileName mli) "-o" (takeFileName out)

    "_build/*.ml" %> \out ->
        case originalToMap !? dropDirectory1 out of
             Just original -> copyFileChanged original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)

    "_build/*.cmx" %> \out -> do
        let ml = out -<.> "ml"
        mli_dependencies <- getModuleDeps $ ModuleDependencies ml
        need $ [ml, out -<.> "cmi"] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        cmd_ (Cwd "_build") "ocamlfind ocamlopt -c -package zarith" (takeFileName ml) "-o" (takeFileName out)
        produces [out -<.> "o"]

    "_build/zlibstubs.o" %> \out -> do
        need ["CH_extern/camlzip/zlibstubs.c"]
        -- ocamlc doesn't respect "-o" here, and needs its CWD in the target directory.
        cmd_ (Cwd "_build") "ocamlfind ocamlc ../CH_extern/camlzip/zlibstubs.c"

    let implDeps file alreadySeen stack = do
        let fileAsCmx = "_build" </> takeFileName file -<.> "cmx"
        --putError $ "file: " ++ fileAsCmx
        --putError $ "already seen: " ++ (intercalate " " alreadySeen)
        if elem file stack then do
            error $ "Cycle detected: " ++ (intercalate " " stack) ++ " " ++ file
        else if elem fileAsCmx alreadySeen then do
            --putError "skipping"
            return alreadySeen
        else do
            --putError "continuing"
            modules <- getModuleDeps $ ModuleDependencies ("_build" </> takeFileName file -<.> "ml")
            let modules2 = ["_build" </> moduleToFile modul -<.> "cmx" | modul <- modules]
            let unseen = filter (\dep -> not $ elem (dep -<.> "cmx") alreadySeen) modules2
            let depsMl = ["_build" </> dep -<.> "ml" | dep <- unseen]
            --putError $ "Unseen: " ++ intercalate " " depsMl
            let mystack = stack ++ [file]
            recursiveDeps <- foldM (\seen newfile -> do
                recDeps <- implDeps newfile seen mystack
                return recDeps) alreadySeen depsMl
            return $ recursiveDeps ++ [fileAsCmx]

    let makeExecutable name main_file = do
        "_bin" </> name %> \out -> do
            let main_ml = "_build" </> main_file -<.> "ml"
            let main_cmx = "_build" </> main_file -<.> "cmx"
            absolute_out <- liftIO $ makeAbsolute out
            deps <- implDeps main_ml [] []
            let reldeps = [takeFileName dep | dep <- deps]
            need $ [main_cmx, "_build/zlibstubs.o"] ++ deps
            cmd_ (Cwd "_build") "ocamlfind ocamlopt -linkpkg -package str,unix,zarith zlibstubs.o -cclib -lz" reldeps "-o" absolute_out
        return ()

    let exes = [("chx86_make_lib_summary", "bCHXMakeLibSummary.ml"),
                ("chx86_make_app_summary", "bCHXMakeAppSummary.ml"),
                ("chx86_make_const_summary", "bCHXMakeConstSummary.ml"),
                ("chx86_make_class_summary", "bCHXMakeClassSummary.ml"),
                ("chx86_make_structdef", "bCHXMakeStructDefinition.ml"),
                ("chx86_inspect_summaries", "bCHXInspectSummaries.ml"),
                ("xanalyzer", "bCHXBinaryAnalyzer.ml"),
                ("canalyzer", "cCHXCAnalyzer.ml")]

    forM_ exes (\pair -> do
        let (name, main_file) = pair
        makeExecutable name main_file)

    phony "binaries" $ do
        -- warm ModuleDependencies cache
        let files = [name | (name, original) <- Map.toList originalToMap]
        let mls = filter (\file -> isInfixOf ".ml" file) files
        askOracles [ModuleDependencies $ "_build" </> file | file <- mls]
        -- actual dependencies
        need ["_bin/" </> name | (name, _) <- exes]
    
    want ["binaries"]
