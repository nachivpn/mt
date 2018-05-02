module Main where

import System.Directory (listDirectory, copyFile, removeFile, withCurrentDirectory, getCurrentDirectory)
import System.FilePath.Posix (replaceDirectory, (</>))
import System.Process (readProcessWithExitCode)
import System.Exit (exitFailure, ExitCode(..))
import Data.List

goodDir = "good"
badDir = "bad"
etcDir = "../etc"

runTests :: [FilePath] -> ExitCode -> IO ()
runTests [] allowedEc = putStrLn "\x1b[0m" >> return ()
runTests (x:xs) allowedEc = do
    putStr $  "\x1b[32m" ++ "Compiling " ++ show x ++ ".."
    (ec, stdout, stderr) <- readProcessWithExitCode "./erly" [x] ""
    if ec /= allowedEc 
        then do
            putStrLn "\x1b[31mFAILED! STDOUT:"
            putStrLn stdout
            putStrLn "\x1b[31m STDERR:"
            putStrLn stderr
        else putStrLn "PASSED!"
    runTests xs allowedEc

main :: IO ()
main = do
    let erlFiles = filter (isSuffixOf ".erl")
        erly = etcDir </> "erly"
        build = readProcessWithExitCode "rebar3" ["escriptize"] ""
    goodTests <- erlFiles <$> listDirectory goodDir
    badTests <- erlFiles <$> listDirectory badDir
    withCurrentDirectory etcDir build
    copyFile erly (goodDir </> "erly")
    copyFile erly (badDir </> "erly")
    withCurrentDirectory goodDir (runTests goodTests ExitSuccess)
    withCurrentDirectory badDir (runTests badTests (ExitFailure 1))


