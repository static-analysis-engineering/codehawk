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
import System.Console.GetOpt
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

copyFileChangedWithAnnotation :: String -> String -> Action ()
copyFileChangedWithAnnotation oldPath newPath = do
    contents <- readFile' oldPath
    let newContents = "# 1 \"" ++ oldPath ++ "\"\n" ++ contents
    writeFileChanged newPath newContents

-- https://stackoverflow.com/a/7569301
splitBy delimiter = foldr f [[]] 
            where f c l@(x:xs) | c == delimiter = []:l
                               | otherwise = (c:x):xs

parseSExp :: String -> [(String, String)]
parseSExp sExp =
    let varLines = [line | line <- lines sExp, isInfixOf "\"" line] in
    let splitLines = [splitBy '"' line | line <- varLines] in
    -- should be in the format ... "VAR" ... "VALUE" ...
    [(varName, varValue) | [_, varName, _, varValue, _] <- splitLines]

defaultOcaml = "4.07.1"
defaultSwitch = "codehawk-" ++ defaultOcaml

data Flags = Opam String | Ocaml String
    deriving Eq
flagDefs = [Option "" ["opam"] (OptArg (\x -> Right $ Opam (fromMaybe defaultSwitch x)) defaultSwitch) "opam switch name",
            Option "" ["ocaml"] (OptArg (\x -> Right $ Ocaml (fromMaybe defaultOcaml x)) defaultOcaml) "ocaml version"]

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
    shakeArgsWith defaultShakeOptions flagDefs $ \flagValues targets -> return $ Just $ do
        let rules = runBuild flagValues
        if null targets then rules else want targets >> withoutActions rules

newtype ModuleDependencies = ModuleDependencies String deriving (Show,Typeable,Eq,Hashable,Binary,NFData)
type instance RuleResult ModuleDependencies = [String]

newtype OcamlEnv = OcamlEnv () deriving (Show,Typeable,Eq,Hashable,Binary,NFData)
type instance RuleResult OcamlEnv = [(String, String)]

libraries = ["zarith"]

runBuild :: [Flags] -> Rules ()
runBuild flags = do
    
    addOracle $ \(OcamlEnv _) -> do
        let Opam switchFlag = fromMaybe (Opam "") $ listToMaybe [x | x@(Opam _) <- flags]
        let Ocaml ocaml = fromMaybe (Ocaml "") $ listToMaybe [x | x@(Ocaml _) <- flags]
        let ocamlSwitch = if ocaml == "" then "" else ("codehawk-" ++ ocaml)
        let switch = if switchFlag == "" then ocamlSwitch else switchFlag
        if switch == "" then return [] else do
        cmd_ "opam init --bare --disable-shell-hook"
        Stdout existingSwitches <- cmd "opam switch list -s"
        if not (switch `isInfixOf` existingSwitches) then do
            cmd_ "opam switch create" switch ocaml "--no-switch"
        else return ()
        cmd_ "opam install ocamlfind " (intercalate " " libraries) " -y" ("--switch=" ++ switch)
        Stdout sExp <- cmd "opam config env" ("--switch=" ++ switch) "--set-switch --sexp"
        return $ parseSExp sExp

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
             Just original -> copyFileChangedWithAnnotation original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)

    getModuleDeps <- addOracleCache $ \(ModuleDependencies file) -> do
        need [file]
        envMembers <- askOracle $ OcamlEnv ()
        let env = [AddEnv x y | (x, y) <- envMembers]
        Stdout dependencies_str <- cmd env "ocamldep -modules" file
        let [(_, modules)] = parseMakefile dependencies_str
        return $ dropLibraryModules modules

    "_build/*.cmi" %> \out -> do
        let mli = out -<.> "mli"
        mli_dependencies <- getModuleDeps $ ModuleDependencies mli
        need $ [mli] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        envMembers <- askOracle $ OcamlEnv ()
        let env = [AddEnv x y | (x, y) <- envMembers]
        cmd_ (Cwd "_build") env "ocamlfind ocamlopt -opaque -package " (intercalate "," libraries) (takeFileName mli) "-o" (takeFileName out)

    "_build/*.ml" %> \out ->
        case originalToMap !? dropDirectory1 out of
             Just original -> copyFileChangedWithAnnotation original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)

    ["_build/*.cmx", "_build/*.o"] &%> \[out, obj] -> do
        let ml = out -<.> "ml"
        mli_dependencies <- getModuleDeps $ ModuleDependencies ml
        need $ [ml, out -<.> "cmi"] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        envMembers <- askOracle $ OcamlEnv ()
        let env = [AddEnv x y | (x, y) <- envMembers]
        cmd_ (Cwd "_build") env "ocamlfind ocamlopt -c -package" (intercalate "," libraries) (takeFileName ml) "-o" (takeFileName out)

    "_build/zlibstubs.o" %> \out -> do
        need ["CH_extern/camlzip/zlibstubs.c"]
        envMembers <- askOracle $ OcamlEnv ()
        let env = [AddEnv x y | (x, y) <- envMembers]
        -- ocamlc doesn't respect "-o" here, and needs its CWD in the target directory.
        cmd_ (Cwd "_build") env "ocamlfind ocamlc ../CH_extern/camlzip/zlibstubs.c"

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
            let objs = [dep -<.> "o" | dep <- deps]
            let reldeps = [takeFileName dep | dep <- deps]
            need $ [main_cmx, "_build/zlibstubs.o"] ++ deps ++ objs
            envMembers <- askOracle $ OcamlEnv ()
            let env = [AddEnv x y | (x, y) <- envMembers]
            cmd_ (Cwd "_build") env "ocamlfind ocamlopt -linkpkg -package" (intercalate "," $ libraries ++ ["str", "unix"]) "zlibstubs.o -cclib -lz" reldeps "-o" absolute_out
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
