module Main where

import Beaver
import Relude

aggregateResults :: Foldable t => t SimResult -> String
aggregateResults rs = case foldr count (0,0,0) rs of
  (u,s,c) -> show s <> " machines halted, " <> show c <> " machines did not halt, "
    <> show u <> " machines hit an unknown edge"
  where
  count :: SimResult -> (Int, Int, Int) -> (Int, Int, Int)
  count (Unknown _) (a,b,c) = (a+1, b, c)
  count (Stop _) (a,b,c) = (a,b+1,c)
  count (Continue _) (a,b,c) = (a,b,c+1)


main :: IO ()
main = do
  let machines = uniTuring 3
      simSteps = 25
      results = simulate simSteps initState <$> machines
  --for_ results (print . dispResult)
  print $ aggregateResults results
