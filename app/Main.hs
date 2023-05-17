module Main (main) where

import System.Environment (getArgs)
import Parser
import Analysis

main :: IO ()
main = do
  args <- getArgs
  case args of
    [name] -> compileFile name False
    [name, v] -> compileFile name (isVerbose v)
    _ -> do
      putStrLn "Expected filename"
      putStrLn "Usage: stack run -- filename"

isVerbose :: String -> Bool
isVerbose v = v == "-v" || v == "--verbose"

compileFile :: String -> Bool -> IO ()
compileFile file verbose = do
  code <- readFile file
  case parse file code of
    Left err -> do
      putStrLn "Parse error:"
      print err
    Right ast -> do
      putStrLn "Input:"
      print ast
      putStrLn ""
      putStrLn "Analysis output:"
      if verbose then
        handleErr (analyseVerbose ast) printVerbose
      else
        handleErr (analyse ast) print
  where
    handleErr res prfn = case res of
      Left e -> putStrLn ("Error: " ++ e)
      Right r -> prfn r
    printVerbose (tp, c, lm, tpf) = do
      putStrLn "Initial type inference:"
      print tp
      putStrLn "Constraints:"
      print c
      putStrLn "Label Mapping:"
      print lm
      putStrLn "Final analysis result:"
      print tpf
