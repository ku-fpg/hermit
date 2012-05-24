{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Command where

import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel

import Language.KURE
import Data.Dynamic


data ShellCommand :: * where
   Status        ::                             ShellCommand
   Message       :: String                   -> ShellCommand
   PushFocus     :: LensH Core Core          -> ShellCommand
   PopFocus      ::                             ShellCommand
   SuperPopFocus ::                             ShellCommand
   KernelCommand :: KernelCommand            -> ShellCommand

data ShellCommandBox = ShellCommandBox ShellCommand deriving Typeable

instance Extern ShellCommand where
    type Box ShellCommand = ShellCommandBox
    box i = ShellCommandBox i
    unbox (ShellCommandBox i) = i

interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
                [ Interp $ \ (ShellCommandBox cmd)       -> cmd
                , Interp $ \ (LensCoreCoreBox l)         -> PushFocus l
                , Interp $ \ (IntBox i)                  -> PushFocus $ childL i
                , Interp $ \ (StringBox str)             -> Message str
                ]

shell_externals :: [External]
shell_externals =
   [
--     external "exit"            Exit
--       [ "exits HERMIT" ]
     external "status"          Status
       [ "redisplays current state" ]
   , external "pop"             PopFocus
       [ "pops one lens" ]
   , external "."               PopFocus
       [ "pops one lens" ]
   , external "superpop"        SuperPopFocus
       [ "pops all lenses" ]
   ]
