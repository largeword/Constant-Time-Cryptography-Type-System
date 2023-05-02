import Test.Tasty
import InferenceTest (testInference)

main :: IO ()
main = defaultMain $ testGroup "CTC Test" [
    testInference
  ]
