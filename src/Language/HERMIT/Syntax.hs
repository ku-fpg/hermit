module Language.HERMIT.Syntax
   (
      -- * Syntax Utilities
      isIdFirstChar,
      isIdChar,
      isInfixId
   )
where

import Data.Char (isAlphaNum)

---------------------------------------------------------------------

-- | Chars that are valid in identifiers anywhere.
isIdFirstChar :: Char -> Bool
isIdFirstChar c = isAlphaNum c || c `elem` "$_:."

-- | Chars that are valid in identifiers, but not as the first character.
isIdChar :: Char -> Bool
isIdChar c = isIdFirstChar c || c `elem` "-'"

-- | Chars that are valid in infix operators.
isInfixId :: Char -> Bool
isInfixId c = c `elem` "!£$%^&*-+=@#<>?/.:|" -- I removed _ ' \\ as I don't think they're valid infix-operator symbols.

---------------------------------------------------------------------
