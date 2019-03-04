module Main
  ( main
  )
where

import Test.DocTest

main :: IO ()
main = doctest $ ["src"] <> ghcArgs

ghcArgs :: [String]
ghcArgs =
  [ "-XDataKinds"
  , "-XGADTs"
  , "-XTypeApplications"
  , "-XTypeOperators"
  ]

