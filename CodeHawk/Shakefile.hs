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
import Data.Map (Map)
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
    let nonparser = filter (\file -> not $ elem "chifparser" $ splitDirectories file) nonBuild in
    nonparser

moduleToFile :: String -> String
moduleToFile modul =
    let firstChar : rest = modul in
    (toLower firstChar) : rest

fileToModule :: String -> String
fileToModule modul =
    let firstChar : rest = modul in
    (toUpper firstChar) : rest

dropLibraryModules :: [String] -> [String] -> [String]
dropLibraryModules libraryModules modules =
    let knownLibraryModules = HashSet.fromList libraryModules in
    filter (\modul -> not $ HashSet.member modul knownLibraryModules) modules

copyFileChangedWithAnnotation :: String -> String -> Action ()
copyFileChangedWithAnnotation oldPath newPath = do
    contents <- readFile' oldPath
    let newContents = "# 1 \"" ++ oldPath ++ "\"\n" ++ contents
    writeFileChanged newPath newContents

data Flags = Warnings deriving Eq
flagDefs = [Option "" ["warnings"] (NoArg $ Right Warnings) "Fail on warnings"]

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

newtype NonFileModules = NonFileModules () deriving (Show,Typeable,Eq,Hashable,Binary,NFData)
type instance RuleResult NonFileModules = [String]

newtype ExtraFlags = ExtraFlags () deriving (Show,Typeable,Eq,Hashable,Binary,NFData)
type instance RuleResult ExtraFlags = [String]

ocamlfind_libraries = ["zarith", "extlib", "camlzip", "goblint-cil"]

runBuild :: [Flags] -> Rules ()
runBuild flags = do

    addOracle $ \(ExtraFlags _) -> do
        return $ if Warnings `elem` flags then ["-warn-error", "A"] else []

    originalToMap <- liftIO $ unsafeInterleaveIO $ do
        mlis <- getDirectoryFilesIO "" ["CH//*.mli", "CHC//*.mli", "CHB//*.mli", "CHJ//*.mli", "CH_gui//*.mli"]
        mls <- getDirectoryFilesIO "" ["CH//*.ml", "CHC//*.ml", "CHB//*.ml", "CHJ//*.ml", "CH_gui//*.ml"]
        let inputs = ignoredOriginalFiles $ mlis ++ mls
        let pairs = [(takeFileName file, file) | file <- inputs]
        return $ Map.fromList pairs

    phony "clean" $ do
        putNormal "Cleaning files in _bin, _build, _docs_private, _docs_public"
        removeFilesAfter "_bin" ["//*"]
        removeFilesAfter "_build" ["//*"]
        removeFilesAfter "_odoc" ["//*"]
        removeFilesAfter "_docs_private" ["//*"]
        removeFilesAfter "_docs_public" ["//*"]

    "_build/*.mli" %> \out ->
        case Map.lookup (dropDirectory1 out) originalToMap of
             Just original -> copyFileChangedWithAnnotation original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)
    
    getLibraryModules <- addOracle $ \NonFileModules{} -> do
        file <- readFile' "non_file_modules.txt"
        return $ lines file

    getModuleDeps <- addOracleCache $ \(ModuleDependencies file) -> do
        need [file]
        Stdout dependencies_str <- cmd "ocamldep -modules" file
        let [(_, modules)] = parseMakefile dependencies_str
        libraryModules <- getLibraryModules $ NonFileModules ()
        return $ dropLibraryModules libraryModules modules

    let documentDir directory = do
        "_build" </> takeBaseName directory -<.> "mld" %> \out -> do
            mlis_full_path <- getDirectoryFiles directory ["*.mli"]
            let children = unwords [takeBaseName mli | mli <- mlis_full_path]
            let contents = "{0 " ++ takeBaseName directory ++ "}\n\n{!modules: " ++ children ++ "}"
            writeFileChanged out contents

        "_build" </> "page-" ++ takeBaseName directory -<.> "odoc" %> \out -> do
            need ["_build/page-_odoc.odoc"]
            need ["_build" </> takeBaseName directory -<.> "mld"]
            mlis_full_path <- getDirectoryFiles directory ["*.mli"]
            let children = ["--child=" ++ takeBaseName mli | mli <- mlis_full_path]
            cmd_ (Cwd "_build") "odoc compile" (takeBaseName directory -<.> "mld") children "-I . --parent=_odoc"

        "_build" </> "page-" ++ takeBaseName directory -<.> "odocl" %> \out -> do
            need [out -<.> "odoc"]
            need ["_build" </> takeBaseName directory -<.> "mld"]
            mlis_full_path <- getDirectoryFiles directory ["*.mli"]
            need ["_build" </> takeBaseName mli -<.> "odoc" | mli <- mlis_full_path]
            cmd_ (Cwd "_build") "odoc link" ("page-" ++ takeBaseName directory -<.> "odoc") "-I ."

        "_odoc" </> takeBaseName directory </> "index.html" %> \out -> do
            let odocl = "_build" </> "page-" ++ takeBaseName directory -<.> "odocl"
            need [odocl]
            mlis_full_path <- getDirectoryFiles directory ["*.mli"]
            need ["_odoc" </> takeBaseName directory </> fileToModule (takeBaseName mli) </> "index.html" | mli <- mlis_full_path]
            cmd_ "odoc html-generate" odocl "--output-dir . --support-uri=_odoc --theme-uri=_odoc"

    "_odoc" </> "*" </> "*" </> "index.html" %> \out -> do
        let modul = moduleToFile $ takeBaseName $ takeDirectory out
        let odocl = "_build" </> modul -<.> "odocl"
        need [odocl]
        cmd_ "odoc html-generate" odocl "--output-dir . --support-uri=_odoc --theme-uri=_odoc"

    let docDirectories = [
                            "CH/xprlib",
                            "CH/chutil",
                            "CH/chlib",
                            "CHB/bchlib",
                            "CHB/bchlibx86",
                            "CHB/bchlibpower32",
                            "CHB/bchcil",
                            "CHB/bchlibarm32",
                            "CHB/bchlibpe",
                            "CHB/bchlibmips32",
                            "CHB/bchanalyze",
                            "CHB/bchcmdline",
                            "CHB/bchlibelf",
                            "CHC/cchcmdline",
                            "CHC/cchlib",
                            "CHC/cchcil",
                            "CHC/cchpre",
                            "CHC/cchanalyze",
                            "CHJ/jchpre",
                            "CHJ/jchmuse",
                            "CHJ/jchstac",
                            "CHJ/jchlib",
                            "CHJ/jchpoly",
                            "CHJ/jchcost",
                            "CHJ/jchfeatures",
                            "CHJ/jchsys"
                         ]
    forM_ docDirectories documentDir

    "_build" </> "_odoc.mld" %> \out -> do
        let children = intercalate "\n" ["- {!page-" ++ takeBaseName dir ++ "}" | dir <- docDirectories]
        let contents = "{0 CodeHawk}\n\n" ++ children
        writeFileChanged out contents

    "_build" </> "page-_odoc.odoc" %> \out -> do
        need ["_build/_odoc.mld"]
        let children = ["--child=" ++ takeBaseName dir | dir <- docDirectories]
        cmd_ (Cwd "_build") "odoc compile _odoc.mld" children "-I ."

    "_build" </> "page-_odoc.odocl" %> \out -> do
        need ["_build/page-_odoc.odoc"]
        need ["_build/page-" ++ takeBaseName dir ++ ".odoc" | dir <- docDirectories]
        cmd_ (Cwd "_build") "odoc link page-_odoc.odoc -I ."

    "_odoc" </> "index.html" %> \out -> do
        need ["_build/page-_odoc.odocl"]
        cmd_ "odoc html-generate _build/page-_odoc.odocl --output-dir . --support-uri=_odoc --theme-uri=_odoc"
        cmd_ "odoc support-files --output-dir _odoc"

    phony "odoc" $ do
        need ["_odoc/index.html"]
        need ["_odoc" </> takeBaseName dir </> "index.html" | dir <- docDirectories]

    "_build/*.odoc" %> \out -> do
        let cmti = takeFileName out -<.> "cmti"
        need ["_build" </> cmti]
        let mli = takeFileName out -<.> "mli"
        let parent = "page-" ++ case Map.lookup mli originalToMap of
             Just original -> takeFileName $ takeDirectory original
             Nothing -> error $ "No file matching \"" ++ mli ++ "\""
        need ["_build" </> parent -<.> "odoc"]
        cmd_ (Cwd "_build") "odoc compile" cmti ("--parent=" ++ parent) "-I ."

    "_build/*.odocl" %> \out -> do
        let mli = out -<.> "mli"
        need [out -<.> "odoc"]
        dep_mlis <- getModuleDeps $ ModuleDependencies mli
        need ["_build" </> moduleToFile mli -<.> ".odoc" | mli <- dep_mlis]
        cmd_ (Cwd "_build") "odoc link" (takeFileName out -<.> "odoc") "-I ."

    ["_build/*.cmi", "_build/*.cmti"] &%> \[out, annot] -> do
        let mli = out -<.> "mli"
        mli_dependencies <- getModuleDeps $ ModuleDependencies mli
        need $ [mli] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        cmd_ (Cwd "_build") "ocamlfind ocamlopt -bin-annot -color=always -opaque -package " (intercalate "," ocamlfind_libraries) (takeFileName mli) "-o" (takeFileName out)

    "_build/*.ml" %> \out ->
        case Map.lookup (dropDirectory1 out) originalToMap of
             Just original -> copyFileChangedWithAnnotation original out
             Nothing -> error $ "No file matching " ++ (dropDirectory1 out)

    ["_build/*.cmx", "_build/*.o"] &%> \[out, obj] -> do
        let ml = out -<.> "ml"
        mli_dependencies <- getModuleDeps $ ModuleDependencies ml
        need $ [ml, out -<.> "cmi"] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        extra_flags <- askOracle $ ExtraFlags ()
        cmd_ (Cwd "_build") "ocamlfind ocamlopt -color=always -c -package" (intercalate "," ocamlfind_libraries) (takeFileName ml) "-o" (takeFileName out) extra_flags

    "_build/*.cmo" %> \out -> do
        let ml = out -<.> "ml"
        mli_dependencies <- getModuleDeps $ ModuleDependencies ml
        need $ [ml, out -<.> "cmi"] ++ ["_build" </> moduleToFile modul <.> "cmi" | modul <- mli_dependencies]
        extra_flags <- askOracle $ ExtraFlags ()
        cmd_ (Cwd "_build") "ocamlfind ocamlc -color=always -c -package" (intercalate "," ocamlfind_libraries) (takeFileName ml) "-o" (takeFileName out) extra_flags

    let implDeps file alreadySeen stack ext = do
        let fileAsCmx = "_build" </> takeFileName file -<.> ext
        if elem file stack then do
            error $ "Cycle detected: " ++ (intercalate " " stack) ++ " " ++ file
        else if elem fileAsCmx alreadySeen then do
            return alreadySeen
        else do
            modules <- getModuleDeps $ ModuleDependencies ("_build" </> takeFileName file -<.> "ml")
            let modules2 = ["_build" </> moduleToFile modul -<.> ext | modul <- modules]
            let unseen = filter (\dep -> not $ elem (dep -<.> ext) alreadySeen) modules2
            let depsMl = ["_build" </> dep -<.> "ml" | dep <- unseen]
            let mystack = stack ++ [file]
            recursiveDeps <- foldM (\seen newfile -> do
                recDeps <- implDeps newfile seen mystack ext
                return recDeps) alreadySeen depsMl
            return $ recursiveDeps ++ [fileAsCmx]

    let makeExecutable name main_file = do
        "_bin" </> name %> \out -> do
            let main_ml = "_build" </> main_file -<.> "ml"
            let main_cmx = "_build" </> main_file -<.> "cmx"
            absolute_out <- liftIO $ makeAbsolute out
            deps <- implDeps main_ml [] [] "cmx"
            let objs = [dep -<.> "o" | dep <- deps]
            let reldeps = [takeFileName dep | dep <- deps]
            need $ [main_cmx] ++ deps ++ objs
            extra_flags <- askOracle $ ExtraFlags ()
            cmd_ (Cwd "_build") "ocamlfind ocamlopt -color=always -linkpkg -package" (intercalate "," $ ocamlfind_libraries ++ ["str", "unix"]) reldeps "-o" absolute_out extra_flags
        return ()
        "_bin" </> name -<.> "byte" %> \out -> do
            let main_ml = "_build" </> main_file -<.> "ml"
            let main_cmx = "_build" </> main_file -<.> "cmo"
            absolute_out <- liftIO $ makeAbsolute out
            deps <- implDeps main_ml [] [] "cmo"
            let reldeps = [takeFileName dep | dep <- deps]
            need $ [main_cmx] ++ deps
            extra_flags <- askOracle $ ExtraFlags ()
            cmd_ (Cwd "_build") "ocamlfind ocamlc -color=always -linkpkg -package" (intercalate "," $ ocamlfind_libraries ++ ["str", "unix"]) reldeps "-o" absolute_out extra_flags
        return ()

    let exes = [("chx86_make_lib_summary", "bCHXMakeLibSummary.ml"),
                ("chx86_make_app_summary", "bCHXMakeAppSummary.ml"),
                ("chx86_make_const_summary", "bCHXMakeConstSummary.ml"),
                ("chx86_make_class_summary", "bCHXMakeClassSummary.ml"),
                ("chx86_make_structdef", "bCHXMakeStructDefinition.ml"),
                ("chx86_inspect_summaries", "bCHXInspectSummaries.ml"),
                ("xanalyzer", "bCHXBinaryAnalyzer.ml"),
                ("canalyzer", "cCHXCAnalyzer.ml"),
		("parseFile", "cCHXParseFile.ml"),
                ("classinvariants", "jCHXClassInvariants.ml"),
                ("translateclass", "jCHXTranslateClass.ml"),
                ("usertemplate", "jCHXTemplate.ml"),
                ("initialize", "jCHXInitializeAnalysis.ml"),
                ("experiment", "jCHXClassExperiment.ml"),
                ("template", "jCHXTemplate.ml"),
                ("integrate", "jCHXIntegrateSummaries.ml"),
                ("inspect", "jCHXInspectSummaries"),
                ("native", "jCHXNativeMethodSignatures.ml"),
                ("features", "jCHXExtractFeatures.ml"),
                ("exprfeatures", "jCHXExtractExprFeatures.ml"),
                ("poly", "jCHXClassPoly.ml"),
                ("pattern", "jCHXCollectPatterns.ml")]

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
    
    phony "bytecodes" $ do
        -- warm ModuleDependencies cache
        --let files = [name | (name, original) <- Map.toList originalToMap]
        --let mls = filter (\file -> isInfixOf ".ml" file) files
        --askOracles [ModuleDependencies $ "_build" </> file | file <- mls]
        -- actual dependencies
        need [("_bin/" </> name -<.> "byte") | (name, _) <- exes]
    
    let makeDocs dir private = do
        -- warm ModuleDependencies cache
        let files = [name | (name, original) <- Map.toList originalToMap]
        let mls = filter (\file -> isInfixOf ".ml" file) files
        askOracles [ModuleDependencies $ "_build" </> file | file <- mls]
        -- actual dependencies
        let exe_files = ["_build" </> filename | (_, filename) <- exes]
        let foldCall accum file = do
            recCall <- implDeps file (Set.toList accum) [] "cmx"
            return $ Set.union accum $ Set.fromList recCall
        allFiles <- foldM foldCall Set.empty exe_files 
        let relFiles = [takeFileName file | file <- Set.toList allFiles]
        let full_mls = ["_build" </> file -<.> "ml" | file <- relFiles]
        let full_mlis = ["_build" </> file -<.> "mli" | file <- relFiles]
        let full_cmis = ["_build" </> file -<.> "cmi" | file <- relFiles]
        let full_cmxs = ["_build" </> file -<.> "cmx" | file <- relFiles]
        need (full_mls ++ full_mlis ++ full_cmis ++ full_cmxs)
        let rel_mls = [file -<.> "ml" | file <- relFiles]
        let rel_mlis = [file -<.> "mli" | file <- relFiles]
        liftIO $ removeFiles dir ["//*"]
        writeFile' (dir </> ".file") "q"
        let filesToDoc = if private then rel_mls else (rel_mls ++ rel_mlis)
        let workaround = [file | file <- filesToDoc, file /= "cCHReturnsite.ml", file /= "cCHCallsite.ml"]
        cmd_ (Cwd "_build") "ocamlfind ocamldoc -keep-code -html -d " ("../" ++ dir) "-package" (intercalate "," $ ocamlfind_libraries ++ ["str","unix"]) workaround
    
    phony "docs_public" $ makeDocs "_docs_public" False
    phony "docs_private" $ makeDocs "_docs_private" True
    
    want ["binaries"]
