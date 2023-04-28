module Main (main) where

import System.Environment (getArgs)
import Parser
import Analysis

main :: IO ()
main = do
  args <- getArgs
  case args of
    [name] -> compileFile name
    _ -> do
      putStrLn "Expected filename"
      putStrLn "Usage: stack run -- filename"

compileFile :: String -> IO ()
compileFile file = do
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
      let res = analyse ast
      case res of
        Left err2 -> putStrLn ("Error: " ++ err2)
        Right tp -> print tp
