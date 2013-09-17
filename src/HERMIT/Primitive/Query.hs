{-# LANGUAGE CPP, LambdaCase, FlexibleContexts #-}

module HERMIT.Primitive.Query
  ( -- * Queries and Predicates
    externals
  , infoT
  , compareValuesT
  )
where

import Control.Arrow

import Data.List (intercalate)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure

import HERMIT.Primitive.GHC hiding (externals)
import HERMIT.Primitive.Navigation hiding (externals)

import qualified Language.Haskell.TH as TH

--------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "info" (infoT :: TranslateH CoreTC String)
                [ "Display information about the current node." ]
         , external "compare-values" (compareValuesT ::  TH.Name -> TH.Name -> TranslateH Core ())
                [ "Compare the rhs of two values."] .+ Query .+ Predicate
         ]

--------------------------------------------------------

infoT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, BoundVars c, HasDynFlags m, MonadCatch m) => Translate c m CoreTC String
infoT =
  do crumbs <- childrenT
     fvs    <- arr freeVarsCoreTC
     translate $ \ c coreTC ->
       do dynFlags <- getDynFlags
          let node     =   "Node:        " ++ coreTCNode coreTC
              con      =   "Constructor: " ++ coreTCConstructor coreTC
              pa       =   "Path:     " ++ showCrumbs (snocPathToPath $ absPath c)
              children =   "Children: " ++ showCrumbs crumbs
              bds      =   "Local bindings in scope: " ++ showVarSet (boundVars c)
              freevars = [ "Free local identifiers:  " ++ showVarSet (filterVarSet isLocalId fvs)
                         , "Free global identifiers: " ++ showVarSet (filterVarSet isGlobalId fvs)
                         , "Free type variables:     " ++ showVarSet (filterVarSet isTyVar fvs)
                         , "Free coercion variables: " ++ showVarSet (filterVarSet isCoVar fvs)
                         ]
              typeId   = case coreTC of
                             Core (ExprCore e)      -> let tyK = exprKindOrType e
                                                        in [(if isKind tyK then "Kind:        " else "Type:        ") ++ showPpr dynFlags tyK] ++
                                                           case e of
                                                             Var i -> [ ""
                                                                      , "Identifier arity:         " ++ show (arityOf c i)
                                                                      , "Identifier binding depth: " ++ runKureM show id (lookupHermitBindingDepth i c) ]
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
                         LRCo{}        -> "LRCo"
                         SubCo{}       -> "SubCo"
                         UnivCo{}      -> "UnivCo"
#else
                         UnsafeCo{}    -> "UnsafeCo"
#endif

--------------------------------------------------------

compareValuesT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> TH.Name -> Translate c m Core ()
compareValuesT n1 n2 = do -- TODO: this can be made more efficient by performing a single traversal.  But I'm not sure of the intent.  What should happen if two things match a name?
        p1 <- onePathToT (arr $ namedBinding n1)
        p2 <- onePathToT (arr $ namedBinding n2)
        e1 <- localPathT p1 idR
        e2 <- localPathT p2 idR
        guardMsg (e1 `coreAlphaEq` e2) (show n1 ++ " and " ++ show n2 ++ " are not equal.")

--------------------------------------------------------
