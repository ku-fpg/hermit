module Main where

import Data.Generics
import Language.Haskell.Syntax

-- For all the RULEs and imports necessary for the optimization.
import HERMIT.Optimization.SYB.Prelude

--------------------------------------------------

mapInt :: (Int -> Int) -> [Int] -> [Int]
mapInt f = everywhere (mkT f)

everywhereInt :: (Int -> Int) -> Int -> Int
everywhereInt f = everywhere (mkT f)

listInt :: [Int] -> (Int -> [Int]) -> ([Int] -> [Int] -> [Int]) -> [Int] -> [Int]
listInt z u p = everything p (mkQ z u)

mapIntM :: (Monad m) => (Int -> m Int) -> [Int] -> m [Int]
mapIntM f = everywhereM (mkM f)

map_Int_AST :: (Int -> Int) -> HsModule -> HsModule
map_Int_AST f = everywhere (mkT f)

main :: IO ()
main = putStrLn (show (mapInt (+1) [])) >> return ()

