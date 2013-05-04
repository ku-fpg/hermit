{-# LANGUAGE ScopedTypeVariables #-}

module Main where


-- ParseArgs library
import System.Console.ParseArgs

import System.CPUTime (cpuTimePrecision)
import Data.List (groupBy, sortBy, intersperse, transpose)
import System.FilePath ((</>), takeExtension)
import System.Directory (getDirectoryContents, removeFile)
import System.Cmd (system)
import System.IO ( hPutStrLn, hPutStr, Handle, IOMode(..), stdout, hFlush
                 , hIsEOF, hGetChar, hClose, openFile, hFileSize)
import System.Exit (ExitCode(..))
import System.Info (os, arch, compilerVersion)
import Control.Monad (when)
import Data.List (intercalate, isInfixOf, sort)

import Tests
import Util

--------------------------------------------------------------------------------
-- Printing results
--------------------------------------------------------------------------------

--printGroupStats :: Handle -> IO [(Int, Test, Int, (Double,Double))] -> IO ()
printGroupStats h l = do
  l' <- l
  let groupThread = groupBy g (sortBy f l') where
        f (nT1,_,_,_) (nT2,_,_,_) = compare nT1 nT2
        g (nT1,_,_,_) (nT2,_,_,_) = nT1 == nT2

      groupTest = groupBy g . sortBy f where
        f (_,t1,_,_) (_,t2,_,_) = compare t1 t2
        g (_,t1,_,_) (_,t2,_,_) = t1 == t2

      -- myFilter :: [(Int, Test, Int, (a,a))]
      myFilter = id
      {-
      myFilter l | length l < 5 = l -- Do not do anything if there are few tests
                 | otherwise    = dropExtremes l
      dropExtremes = init . tail . sortBy (\x y -> fou4 x `compare` fou4 y)
      -}
      fou4 (_,_,_,a) = a

      --calcAvgStdDev :: [(Int, Test, Int, (a,a))] -> (Test, (a,a), (a,a))
      calcAvgStdDev x = (fst4 (head x), snd4 (head x), avg x, stddev $ avg x)
        where
          double :: (a -> b) -> (a,a) -> (b,b)
          double f (a,b) = (f a, f b)
          avg  l = double (div1 l) $ sum' l
          div1 l y = y / toEnum (length l)
          div2 l y = y / (toEnum (length l) - 1)
          avg' l = double (div2 l) $ sum' l -- sample standard deviation
          stddev (a,b) = double sqrt $ (avg' [ (nT,t,d,((y-a)^2,(z-b)^2))
                                             | (nT,t,d,(y,z)) <- x ])
          fst4 (a,_,_,_) = a
          snd4 (_,a,_,_) = a
          sum' :: Num a => [(Int, Test, Int, (a,a))] -> (a,a)
          sum' []                 = (0,0)
          sum' ((_,_,_,(c,w)):ts) = case sum' ts of (c',w') -> (c' + c, w' + w)

      --group2 :: [(Int, Test, a, a)] -> [[(Int, Test, a, a)]]
      group2 = groupBy g' . sortBy f'
      f' (_,t1,_,_) (_,t2,_,_) = compare (testName t1, datatype t1, ghcFlags t1)
                                         (testName t2, datatype t2, ghcFlags t2)
      g' (_,t1,_,_) (_,t2,_,_) =    testName t1 == testName t2
                                 && datatype t1 == datatype t2
                                 && ghcFlags t1 == ghcFlags t2
      lst = map group2 . map (map (calcAvgStdDev . myFilter)) . map groupTest $ groupThread

  print $ map groupTest groupThread
  writeCSVFile "results.csv" lst
  handleGroups h lst

-- Show a frac with 4 decimal places, replace dot by comma
showF :: RealFrac a => a -> String
showF = map id . show . (/ 10000) . fromIntegral . round . (* 10000) where
  dot '.' = ','
  dot c   = c

-- Write out csv file used by pgfplot (quick and dirty)
writeCSVFile :: (Show a, Fractional a) => FilePath -> [[[(Int, Test, (a,a), (a,a))]]] -> IO ()
writeCSVFile fn l = do
    let lcsv = groupBy g' . sortBy f' . concat . concat $ l
        f' (_,t1,_,_) (_,t2,_,_) = (datatype t1, testName t1, lib t1) `compare` (datatype t2, testName t2, lib t2)
        g' (_,t1,_,_) (_,t2,_,_) = (datatype t1, testName t1) == (datatype t2, testName t2)
        csvline tsts = intercalate ", "
                     $ (show t_nm ++ show t_ty) : [ show (tm / h_tm) ++ ", " ++ show (std / h_tm)
-- rationale for std / h_tm ... std/tm is stddev as percentage of avg, tm/h_tm is avg as multiple of hand
-- so std/tm * tm/h_tm is percentage of multiple, which reduces to std/h_tm
                                                  | (_,_,(tm,_),(std,_)) <- tsts ]
            where (h_tm,h_std,t_nm,t_ty) = head [ (tm,std,testName t,datatype t) | (_,t,(tm,_),(std,_)) <- tsts, lib t == Hand ]
        csvfile = unlines $ (intercalate ", " $ "Benchmark" : [ nm ++ ", " ++ nm ++ "_stddev"
                                                              | tsts <- take 1 lcsv, (_,t,_,_) <- tsts
                                                              , let nm = case lib t of
                                                                            SYB -> if "HERMIT" `isInfixOf` ghcFlags t
                                                                                   then "SYBOPT"
                                                                                   else "SYB"
                                                                            _ -> show $ lib t ]
                            ) : sort (map csvline lcsv)

    writeFile fn csvfile

handleGroups :: (RealFrac a) => Handle -> [[[(Int, Test, (a,a), (a,a))]]] -> IO ()
handleGroups h l = do -- First show the "standard" output
                      mapM_ (mapM_ (handle1Group h)) l
                      -- Then show the output optimized for graphing
                      hPutStrLn h ("\n-------------------------------------")
                      hPutStrLn h ("Condensed output\n")

                      -- Group by num of threads, transpose
                      let lT = transpose . groupBy g . sortBy f . concat
                                 . map concat $ l
                          f (t1,_,_,_) (t2,_,_,_) = compare t1 t2
                          g (t1,_,_,_) (t2,_,_,_) = t1 == t2

                          getTest []            = error "getTest: impossible"
                          getTest ((_,a,_,_):_) = a

                          numTs = map (\(n,_,_,_) -> "N" ++ show n) (head lT)

                      hPutStrLn h (inTabs (["Test name", "LibName"] ++ numTs))
                      sequence_
                        [ hPutStrLn h (inTabs
                            (    [ name (getTest ll), show (lib (getTest ll))]
                              ++ [ showF wT | (_,_,(_,wT),_) <- ll ]))
                        | ll <- lT ]

handle1Group :: (RealFrac a) => Handle -> [(Int, Test, (a,a), (a,a))] -> IO ()
handle1Group _ [] = error "handleGroup []"
handle1Group h g  = do
                     mapM_ (hPutStrLn h)
                       [ inTabs [ show nrT, name t, show (lib t), showF a
                                , showF b, showF c, showF d]
                       | (nrT,t,(a,b),(c,d)) <- g ]


name :: Test -> String
name t = show (testName t) ++ "/" ++ show (datatype t) ++ " " ++ ghcFlags t

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------
main :: IO ()
main = do
        args <- parseArgsIO ArgsComplete myArgs

        -- Some variables
        let profiling = gotArg args P
            binsize   = gotArg args B
            help      = gotArg args H
            debug     = gotArg args D
            n, threads, threadsTo :: Int
            n         = if profiling then 1 else (getRequiredArg args N)
            threads   = getRequiredArg args T
            threadsTo = if threads >= 1 && getRequiredArg args TT >= threads
                          then getRequiredArg args TT else threads
            ghc       = getRequiredArg args C
            rts t =    (if t > 1
                       then (" -N" ++ show t)
                       else "")
                    ++ if profiling then " -p -K1g " else ""
                    ++ " " ++ getRequiredArg args R ++ " "
            flags t = " -fforce-recomp --make " ++ getRequiredArg args F ++ " "
                      ++ ghcFlags t ++ " "
                      ++ " -rtsopts "
                      ++ (if profiling then " -prof -auto-all " else "")
                      ++ (if threads > 1 || threadsTo > 1
                            then " -threaded -feager-blackholing " else "")
                      ++ " -outputdir out "
            hash :: Test -> String
            hash = show . hashString . show
            mainis t = "-main-is " ++ show (lib t) ++ "."
                         ++ show (testName t)
                         ++ ".Main.main" ++ show (datatype t)
                         ++ " -o " ++ newpath t ++ " "
            path t = show (lib t) </> show (testName t) </> "Main"
            newpath t = path t ++ show (lib t) ++ show (testName t) ++ show (datatype t) ++ hash t
            out t = "out" </> show (lib t) ++ "." ++ show (testName t) ++ "."
                      ++ show (datatype t) ++ "." ++ hash t ++ ".compileout"
            redirect t = " > " ++ out t ++ " 2>&1 "
            cmd t = ghc ++ flags t ++ mainis t ++ path t ++ redirect t

        -- Display usage information
        when help $ usageError args ""

        -- Sanity check
        when (profiling && binsize) $ do
          usageError args "Cannot profile and compute binary sizes."

        -- Compilation
        putStrLn "Compiling..." >> hFlush stdout
        sequence_ [ putStrLn $ show i ++ ": " ++ (cmd t) | (i,t) <- zip [1..] tests ]
        sequenceProgress_ [ system (cmd t) | t <- tests ]

        -- Remove old outputs
        putStrLn "Removing old outputs..." >> hFlush stdout
        files <- getDirectoryContents "out"
        let filesToDelete = filter ((==) ".out" . takeExtension) files
        mapM removeFile (map ("out" </>) filesToDelete)

        -- Running tests
        let newout t m nT = "out" </> "N" ++ show nT ++ "_"
                            ++ show (lib t) ++ "." ++ show (testName t) ++ "."
                            ++ show (datatype t) ++ "." ++ hash t ++ "." ++ show m ++ ".out"
            run t m nT =    newpath t
                         ++ " +RTS "
                         ++ (if debug
                             then (" -sout/" ++ show (lib t) ++ show (testName t)
                                   ++ show (datatype t) ++ hash t ++ show m ++ "_N"
                                   ++ show threads ++ ".txt ")
                             else "")
                         ++ rts nT ++ " -RTS"
                         ++ " > " ++ newout t m nT
        when (not binsize) $ do
          putStrLn "Running tests..." >> hFlush stdout
          sequence_ [ putStrLn $ show i ++ ": " ++ (run t m nrT) | nrT <- [threads..threadsTo], (i,t) <- zip [1..] tests, m <- [1..n]]
          sequenceProgress_ [ system (run t m nrT) | nrT <- [threads..threadsTo]
                                                   , t <- tests, m <- [1..n] ]

        -- Calculating binary size
        let filename t = newpath t ++ ".exe" -- TODO: this is not portable!
            size s = do
                       h' <- openFile s ReadMode
                       x <- hFileSize h'
                       hClose h'
                       return (fromInteger x)
            sizes = sequence [ size (filename t) | t <- tests ]

        -- Results output
        h <- getArgStdio args O WriteMode
        putStrLn ("-------------------------------------")
        hPutStrLn h "\nResults:"
        hPutStrLn h ("Number of repetitions: " ++ show n)
        hPutStrLn h ("Compiler flags: " ++ (getRequiredArg args F :: String))
        hPutStrLn h ("Environment: " ++ inCommas [os, arch, show compilerVersion])
        hPutStrLn h ("CPU time precision: " ++ show (fromInteger cpuTimePrecision / (1000000000 :: Double)) ++ " (ms)")
        hPutStrLn h ""
        -- Header
        hPutStrLn h (inTabs [ "N", "Test name", "LibName", "CPU time"
                            , "Wall time", "CPUt stddev", "Wallt stddev"])

        let parse :: Test -> Int -> Int -> IO (Double,Double)
            parse t m nrT = readFile' (newout t m nrT)
                            >>= return . pair . map (read :: String -> Double)
                                  . tail . words
            pair [x,y] = (x,y)
            pair s     = error (show s)
            liftIOList :: [(a, b, c, IO d)] -> IO [(a, b, c, d)]
            liftIOList [] = return []
            liftIOList ((a,b,c,d):t) = do  d' <- d
                                           t' <- liftIOList t
                                           return ((a,b,c,d'):t')
        case (profiling, binsize) of
          (True, False)  -> hPutStrLn h ("Profiling run, no benchmarking results.")
          (False, True)  -> sizes >>= \l -> printGroupStats h
                             (return [ (1,t,1,(s,s)) | (t,s) <- zip tests l ])
          (False, False) -> printGroupStats h (liftIOList
                              [ (nrT, t, m, parse t m nrT)
                              | nrT <- [threads..threadsTo]
                              , t <- tests, m <- [1..n]])
          (True, True)   -> error "Internal error #1 (can never happen)"
        hPutStrLn h ("-------------------------------------")
        hClose h


--------------------------------------------------------------------------------
-- Command-line arguments
--------------------------------------------------------------------------------
data MyArgs = N | O | F | P | B | C | H | T | TT | D | R
        deriving (Eq, Ord, Show)

myArgs :: [Arg MyArgs]
myArgs = [
          Arg { argIndex = N,
                argAbbr = Just 'n',
                argName = Just "number-times",
                argData = argDataDefaulted "int" ArgtypeInt 1,
                argDesc = "Number of times to run the input program"
              },
          Arg { argIndex = O,
                argAbbr = Just 'o',
                argName = Just "output",
                argData = argDataOptional "file" ArgtypeString,
                argDesc = "Output report file"
              },
          Arg { argIndex = F,
                argAbbr = Just 'f',
                argName = Just "ghc-flags",
                argData = argDataDefaulted "flags" ArgtypeString "",
                argDesc = "Flags to pass to the compiler"
              },
          Arg { argIndex = R,
                argAbbr = Just 'r',
                argName = Just "rts",
                argData = argDataDefaulted "rts" ArgtypeString "",
                argDesc = "RTS flags to pass to the program"
              },
          Arg { argIndex = P,
                argAbbr = Just 'p',
                argName = Just "profiling",
                argData = Nothing,
                argDesc = "Profile, do not benchmark"
              },
          Arg { argIndex = T,
                argAbbr = Just 't',
                argName = Just "threaded",
                argData = argDataDefaulted "num threads" ArgtypeInt 1,
                argDesc = "Use -threaded with given number of threads"
              },
          Arg { argIndex = TT,
                argAbbr = Just 's',
                argName = Just "threadMax",
                argData = argDataDefaulted "max num threads" ArgtypeInt 1,
                argDesc = "Runs tests from -tM to -sN threads, N >= M"
              },
          Arg { argIndex = B,
                argAbbr = Just 'b',
                argName = Just "binary-size",
                argData = Nothing,
                argDesc = "Compute binary sizes (Win only)"
              },
          Arg { argIndex = C,
                argAbbr = Just 'c',
                argName = Just "path-to-ghc",
                argData = argDataDefaulted "path" ArgtypeString "ghc",
                argDesc = "Path to GHC (defaults to \"ghc\")"
              },
          Arg { argIndex = H,
                argAbbr = Just 'h',
                argName = Just "help",
                argData = Nothing,
                argDesc = "Display usage instructions"
              },
          Arg { argIndex = D,
                argAbbr = Just 'd',
                argName = Just "debug",
                argData = Nothing,
                argDesc = "Print extra debug information"
              }
         ]


--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

sequenceProgress_ :: [IO ExitCode] -> IO ()
sequenceProgress_ [] = return ()
sequenceProgress_ l  = do
  let seq :: [IO ExitCode] -> Int -> IO ()
      seq []    _ = putStrLn "done."
      seq (h:t) n = do
                      putStr ((show n) ++ " ") >> hFlush stdout
                      sequenceError_ [h]
                      seq t (n + 1)
  putStr ("Total number of elements: " ++ show (length l) ++ ". ")
  seq l 1

-- sequence_ accounting for errors
sequenceError_ :: [IO ExitCode] -> IO ()
sequenceError_ []    = return ()
sequenceError_ (h:t) = do
                         e <- h
                         case e of
                           ExitSuccess   -> sequenceError_ t
                           ExitFailure n -> error ("Execution returned exit code "
                                                    ++ show n ++ ", aborted.")

-- Stricter readFile
hGetContents' hdl = do e <- hIsEOF hdl
                       if e then return []
                         else do c <- hGetChar hdl
                                 cs <- hGetContents' hdl
                                 return (c:cs)

readFile' fn = do hdl <- openFile fn ReadMode
                  xs <- hGetContents' hdl
                  hClose hdl
                  return xs

inCommas, inTabs :: [String] -> String
inCommas = concat . intersperse ","
inTabs = concat . intersperse "\t"
