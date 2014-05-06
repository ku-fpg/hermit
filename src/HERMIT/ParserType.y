{
{-# LANGUAGE CPP #-}
module HERMIT.ParserType
#if __GLASGOW_HASKELL__ <= 706
    () where
#else
    ( parseType
    , parseTypeT
    , parseTypeWithHoles
    , parseTypeWithHolesT
    ) where
#endif

import Control.Arrow
import Control.Monad.State
import Data.Char (isSpace, isDigit)

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
import HERMIT.ParserCore
import HERMIT.Syntax (isCoreInfixIdChar, isCoreIdFirstChar, isCoreIdChar)

import Language.KURE.MonadCatch (prefixFailMsg)
}

%name parser
%tokentype { Token }
%error { parseError }
%monad { TypeParseM } { >>= } { return }

%token
    '%forall'  { Tforall }
    '%rec'     { Trec }
    '%let'     { Tlet }
    '%in'      { Tin }
    '%case'    { Tcase }
    '%of'      { Tof }
    '%cast'    { Tcast }
    '%note'    { Tnote }
    '%external'    { Texternal }
    '%local'   { Tlocal }
    '%_'       { Twild }
    '('        { Toparen }
    ')'        { Tcparen }
    '{'        { Tobrace }
    '}'        { Tcbrace }
    '#'        { Thash}
    '='        { Teq }
    ':'        { Tcolon }
    '::'       { Tcoloncolon }
    ':=:'      { Tcoloneqcolon }
    '*'        { Tstar }
    '->'       { Tarrow }
    '\\'       { Tlambda}
    '@'        { Tat }
    '.'        { Tdot }
    '?'        { Tquestion}
    ';'            { Tsemicolon }
    NAME       { Tname $$ }
    CNAME      { Tcname $$ }
    INTEGER    { Tinteger $$ }
    RATIONAL   { Trational $$ }
    STRING     { Tstring $$ }
    CHAR       { Tchar $$ }

%%

-- | Top level type term.
expr : app             { $1 }

app : app arg          { mkAppTy $1 $2 }
    | arg              { $1 }

arg : '(' expr ')'     { $2 }
    | '(' ')'          {% lookupName "()" }
    | var              { $1 }

var : NAME             {% lookupName $1 }
{

#if __GLASGOW_HASKELL__ <= 706
findType = error "findType cannot be called in < GHC 7.8"
#endif

lookupName :: String -> TypeParseM Type
lookupName nm = do
    c <- getContext
    et <- lift $ attemptM $ findType nm c
    either (const (addTyVar nm)) return et

data TPState = TPState { tpContext :: HermitC
                       , tpUsed :: [TyVar]
                       }

type TypeParseM a = StateT TPState HermitM a

getContext :: TypeParseM HermitC
getContext = gets tpContext

addTyVar :: String -> TypeParseM Type
addTyVar tvStr = do
    used <- gets tpUsed
    case [ tv | tv <- used, getOccString tv == tvStr ] of
        [] -> do tv <- lift $ newTyVarH tvStr liftedTypeKind
                 modify $ \ st -> st { tpUsed = tv : tpUsed st }
                 return $ mkTyVarTy tv
        [tv] -> return $ mkTyVarTy tv
        other -> fail "addTyVar: impossible case"

---------------------------------------------

-- | Parse a CoreString into a Type, where all type variables must be bound.
parseType :: CoreString -> HermitC -> HermitM Type
parseType cs c = do
    (ty, holes) <- parseTypeWithHoles cs c
    guardMsg (null holes) "type contains unbound type variables."
    return ty

-- | Parse a CoreString into a Type, any unbound variables are returned.
parseTypeWithHoles :: CoreString -> HermitC -> HermitM (Type, [TyVar])
parseTypeWithHoles (CoreString s) c =
    case lexer s of
        Left msg -> fail msg
        Right tokens -> do
            (ty,st) <- runStateT (parser tokens) (TPState c [])
            return (ty,tpUsed st)

---------------------------------------------

-- | Parse a 'CoreString' to a 'Type', using the current context.
parseTypeT :: CoreString -> TransformH a Type
parseTypeT = contextonlyT . parseType

-- | Parse a 'CoreString' to a 'Type', using the current context, returning unbound type variables.
parseTypeWithHolesT :: CoreString -> TransformH a (Type, [TyVar])
parseTypeWithHolesT = contextonlyT . parseTypeWithHoles

---------------------------------------------

}
