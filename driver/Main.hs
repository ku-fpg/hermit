module Main where

import HERMIT.Driver

import System.Environment

main :: IO ()
main = getArgs >>= hermitDriver
