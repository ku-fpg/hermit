{-# LANGUAGE CPP, LambdaCase, FlexibleContexts #-}

module HERMIT.Dictionary.Query
    ( -- * Queries and Predicates
      externals
    , infoT
    , compareCoreAtT
    , compareBoundIdsT
    ) where

import Control.Arrow

import Data.List (intercalate)
import qualified Data.Map as Map

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Dictionary.AlphaConversion hiding (externals)
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Inline hiding (externals)

--------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
    [ external "info" (infoT :: TransformH CoreTC String)
        [ "Display information about the current node." ] .+ Query
    , external "compare-bound-ids" (compareBoundIds :: String -> String -> TransformH CoreTC ())
        [ "Compare the definitions of two in-scope identifiers for alpha equality."] .+ Query .+ Predicate
    , external "compare-core-at" (compareCoreAtT ::  TransformH Core LocalPathH -> TransformH Core LocalPathH -> TransformH Core ())
        [ "Compare the core fragments at the end of the given paths for alpha-equality."] .+ Query .+ Predicate
    ]

--------------------------------------------------------

infoT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, BoundVars c, HasEmptyContext c, HasDynFlags m, MonadCatch m) => Transform c m CoreTC String
infoT =
  do crumbs <- childrenT
     fvs    <- arr freeVarsCoreTC
     transform $ \ c coreTC ->
       do dynFlags <- getDynFlags
          let node     =   "Node:        " ++ coreTCNode coreTC
              con      =   "Constructor: " ++ coreTCConstructor coreTC
              pa       =   "Path:     " ++ showCrumbs (snocPathToPath $ absPath c)
              children =   "Children: " ++ showCrumbs crumbs
              bds      =   "Local bindings in scope: " ++ concat
                                [ "\n  " ++ unqualifiedName k ++  " : " ++ hermitBindingSummary hbs
                                | (k,hbs) <- Map.toList (hermitBindings c)
                                ]
              freevars = [ "Free local identifiers:  " ++ showVarSet (filterVarSet isLocalId fvs)
                         , "Free global identifiers: " ++ showVarSet (filterVarSet isGlobalId fvs)
                         , "Free type variables:     " ++ showVarSet (filterVarSet isTyVar fvs)
                         , "Free coercion variables: " ++ showVarSet (filterVarSet isCoVar fvs)
                         ]

              typeId   = case coreTC of
                             Core (ExprCore e)      -> let tyK = exprKindOrType e
                                                           modName i = case nameModule_maybe (getName i) of
                                                                        Nothing -> "no module name."
                                                                        Just m -> moduleNameString (moduleName m)
                                                        in [(if isKind tyK then "Kind:        " else "Type:        ") ++ showPpr dynFlags tyK] ++
                                                           case e of
                                                             Var i -> [ ""
                                                                      , "OccName:                  " ++ getOccString i
                                                                      , if isLocalVar i then "Local" else "Global: " ++ modName i
                                                                      , "Unique:                   " ++ show (getUnique i)
                                                                      , "Identifier arity:         " ++ show (arityOf c i)
                                                                      , "Identifier binding depth: " ++ runKureM show id (lookupHermitBindingDepth i c)
                                                                      ] ++ if isId i then let inf = idInfo i
                                                                                          in [ "Unfolding:                " ++ showPpr dynFlags (unfoldingInfo inf)
                                                                                             , "Occurrence Info:          " ++ showPpr dynFlags (occInfo inf)
                                                                                             , "Inline Pragmas:           " ++ showPpr dynFlags (inlinePragInfo inf)
                                                                                             ]
                                                                                     else []
                                                             _     -> []
                             TyCo (TypeCore ty)     -> ["Kind: " ++ showPpr dynFlags (typeKind ty)]
                             TyCo (CoercionCore co) -> ["Kind: " ++ showPpr dynFlags (coercionKind co) ]
                             _                      -> []

          return $ intercalate "\n" ([node,con] ++ typeId ++ ["",pa,children,""] ++ freevars ++ [bds])

-- showIdInfo :: DynFlags -> Id -> String
-- showIdInfo dynFlags v = showSDoc dynFlags $ ppIdInfo v $ idInfo v

--------------------------------------------------------

coreTCNode :: CoreTC -> String
coreTCNode (Core core)           = coreNode core
coreTCNode (TyCo TypeCore{})     = "Type"
coreTCNode (TyCo CoercionCore{}) = "Coercion"

coreNode :: Core -> String
coreNode (GutsCore _)  = "Module"
coreNode (ProgCore _)  = "Program"
coreNode (BindCore _)  = "Binding Group"
coreNode (DefCore _)   = "Recursive Definition"
coreNode (ExprCore _)  = "Expression"
coreNode (AltCore _)   = "Case Alternative"

coreTCConstructor :: CoreTC -> String
coreTCConstructor = \case
                       Core core              -> coreConstructor core
                       TyCo (TypeCore ty)     -> typeConstructor ty
                       TyCo (CoercionCore co) -> coercionConstructor co

coreConstructor :: Core -> String
coreConstructor (GutsCore _)     = "ModGuts"
coreConstructor (ProgCore prog)  = case prog of
                                     ProgNil      -> "ProgNil"
                                     ProgCons _ _ -> "ProgCons"
coreConstructor (BindCore bnd)   = case bnd of
                                     Rec _      -> "Rec"
                                     NonRec _ _ -> "NonRec"
coreConstructor (DefCore _)      = "Def"
coreConstructor (AltCore _)      = "(,,)"
coreConstructor (ExprCore expr)  = case expr of
                                     Var _        -> "Var"
                                     Type _       -> "Type"
                                     Lit _        -> "Lit"
                                     App _ _      -> "App"
                                     Lam _ _      -> "Lam"
                                     Let _ _      -> "Let"
                                     Case _ _ _ _ -> "Case"
                                     Cast _ _     -> "Cast"
                                     Tick _ _     -> "Tick"
                                     Coercion _   -> "Coercion"

typeConstructor :: Type -> String
typeConstructor = \case
                     TyVarTy{}    -> "TyVarTy"
                     AppTy{}      -> "AppTy"
                     TyConApp{}   -> "TyConApp"
                     FunTy{}      -> "FunTy"
                     ForAllTy{}   -> "ForAllTy"
                     LitTy{}      -> "LitTy"

coercionConstructor :: Coercion -> String
coercionConstructor = \case
                         Refl{}        -> "Refl"
                         TyConAppCo{}  -> "TyConAppCo"
                         AppCo{}       -> "AppCo"
                         ForAllCo{}    -> "ForAllCo"
                         CoVarCo{}     -> "CoVarCo"
                         AxiomInstCo{} -> "AxiomInstCo"
                         SymCo{}       -> "SymCo"
                         TransCo{}     -> "TransCo"
                         NthCo{}       -> "NthCo"
                         InstCo{}      -> "InstCo"
#if __GLASGOW_HASKELL__ > 706
                         AxiomRuleCo{} -> "AxiomRuleCo"
                         LRCo{}        -> "LRCo"
                         SubCo{}       -> "SubCo"
                         UnivCo{}      -> "UnivCo"
#else
                         UnsafeCo{}    -> "UnsafeCo"
#endif

--------------------------------------------------------

-- | Compare the core fragments at the end of the specified 'LocalPathH's.
compareCoreAtT :: (ExtendPath c Crumb, AddBindings c, ReadBindings c, ReadPath c Crumb, HasEmptyContext c, MonadCatch m) => Transform c m Core LocalPathH -> Transform c m Core LocalPathH -> Transform c m Core ()
compareCoreAtT p1T p2T =
  do p1 <- p1T
     p2 <- p2T
     core1 <- localPathT p1 idR
     core2 <- localPathT p2 idR
     guardMsg (core1 `coreAlphaEq` core2) "core fragments are not alpha-equivalent."

-- | Compare the definitions of two identifiers for alpha-equality.
compareBoundIdsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Id -> Id -> Transform c HermitM x ()
compareBoundIdsT i1 i2 =
  do e1 <-                       fst ^<< getUnfoldingT AllBinders <<< return i1
     e2 <- replaceVarR i2 i1 <<< fst ^<< getUnfoldingT AllBinders <<< return i2
     -- recursive definitions wouldn't be alpha-equivalent without replacing the identifier
     guardMsg (e1 `exprAlphaEq` e2) "bindings are not alpha-equivalent."

-- | Compare the definitions of the two named identifiers for alpha-equality.
compareBoundIds :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => String -> String -> Transform c HermitM x ()
compareBoundIds nm1 nm2 = do i1 <- findIdT nm1
                             i2 <- findIdT nm2
                             compareBoundIdsT i1 i2

-- TODO: generalise compareBoundIds to comparBoundVars.
--       this will require generalising the underlying functions

--------------------------------------------------------
