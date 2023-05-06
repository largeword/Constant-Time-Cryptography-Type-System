import Test.Tasty
import System.Environment
import InferenceTest (testInference)

main :: IO ()
main = do
  setEnv "TASTY_NUM_THREADS" "4"
  defaultMain $ testGroup "CTC Test" [testInference]
