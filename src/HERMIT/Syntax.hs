module HERMIT.Syntax
    ( -- * Utility Predicates for lexing Identifiers
      quoteShow,
      -- ** Lexing HERMIT Scripts
      isScriptIdFirstChar,
      isScriptIdChar,
      isScriptInfixIdChar,
      -- ** Lexing Core Fragments
      isCoreIdFirstChar,
      isCoreIdChar,
      isCoreInfixIdChar
    ) where

import Data.Char (isAlphaNum, isAlpha)

---------------------------------------------------------------------

-- | Characters that are valid as the leading character of an identifier in a HERMIT script.
isScriptIdFirstChar :: Char -> Bool
isScriptIdFirstChar c = isAlphaNum c || c `elem` "$_:."

-- | Characters that are valid identifier elements (a superset of 'isScriptIdFirstChar') in a HERMIT script.
isScriptIdChar :: Char -> Bool
isScriptIdChar c = isScriptIdFirstChar c || isScriptInfixIdChar c || c `elem` "'"
  -- infix identifiers can appear in dictionary names
  -- square brackets can appear in dictionary names (specifically, list instances).  However, we don't include them here because that would require us to always place spaces around [ ] when defining lists.  As a work-around, the user can place "" around any such names.

-- | Characters that are valid in infix operators in a HERMIT script.
isScriptInfixIdChar :: Char -> Bool
isScriptInfixIdChar c = c `elem` infixOperatorSymbols
                        -- old: "!£$%^&*-+=@#<>?/.:|"

---------------------------------------------------------------------

-- | Chars that are valid as the leading character of an identifier in a Core fragment.
isCoreIdFirstChar :: Char -> Bool
isCoreIdFirstChar c = c `elem` "_$[]:.=" || isAlpha c

-- | Characters that are valid identifier elements (a superset of 'isCoreIdFirstChar') in a Core fragment.
isCoreIdChar :: Char -> Bool
isCoreIdChar c = isAlphaNum c || isCoreIdFirstChar c || isCoreInfixIdChar c || c `elem` "'[]"
  -- infix identifiers can appear in dictionary names
  -- square brackets can appear in dictionary names (specifically, list instances)

-- | Characters that are valid in infix operators in a Core fragment.
isCoreInfixIdChar :: Char -> Bool
isCoreInfixIdChar c = c `elem` infixOperatorSymbols
                      -- old: "+*/._-:<>"

---------------------------------------------------------------------

-- TODO: Should the set of infix operator symobls be common to both HERMIT scripts and Core fragments?
--       I'm pretty sure the old definition of isCoreInfixIdChar was too limited at least.

infixOperatorSymbols :: [Char]
infixOperatorSymbols = "!£$%^&*-+=@#<>?/.:|"

---------------------------------------------------------------------

quoteShow :: Show a => a -> String
quoteShow x = if all isScriptIdChar s then s else show s
    where s = show x
