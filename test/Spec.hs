import Test.Tasty
import System.Environment
import InferenceTest (testInference)
import ConstantTimeTest (testCT)

main :: IO ()
main = do
  setEnv "TASTY_NUM_THREADS" "4"
  defaultMain $ testGroup "CTC Test" [
      testInference,
      testCT
    ]
