module Main (main) where

import Data.IORef
import qualified Data.Map as Map
import Library

main :: IO ()
main = do
  putStrLn "Testing distillation algorithm..."

  let defs =
        Map.fromList
          [ ( "fact",
              Lambda
                "n"
                ( Case
                    (Var "n")
                    [ (Pattern "Zero" [], CCall "One" []),
                      (Pattern "Succ" ["m"], CCall "Mult" [Var "n", Apply (Unfold "fact") (Var "m")])
                    ]
                )
            )
          ]

  let testTerm = Apply (Unfold "fact") (CCall "Succ" [CCall "Zero" []])

  let lts = drive defs testTerm
  gensym <- newIORef 0
  transformedLts <- transformLts defs gensym lts
  epsilonRef <- newIORef Map.empty
  term <- residualizeLts gensym epsilonRef transformedLts
  epsilon <- readIORef epsilonRef
  print term
  print epsilon
