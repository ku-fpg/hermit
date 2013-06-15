module Language.HERMIT.Primitive.Navigation.Crumbs
       ( -- * Navigating Using Crumbs
         crumbExternals
       )
where

import Language.HERMIT.Core
import Language.HERMIT.External

---------------------------------------------------------------------------------------

-- | 'External's for individual 'Crumb's.
crumbExternals :: [External]
crumbExternals = map (.+ Navigation)
            [
              external "prog" ModGuts_Prog
                [ "Descend into the program within a module." ]
            , external "prog-head" ProgCons_Head
                [ "Descend into the first binding group in a program." ]
            , external "prog-tail" ProgCons_Tail
                [ "Descend into the tail of the program." ]
            , external "nonrec-rhs" NonRec_RHS
                [ "Descend into the right-hand side of a non-recursive binding." ]
            , external "rec-def" Rec_Def
                [ "Descend into the (n-1)th definition in a recursive binding group." ]
            , external "def-rhs" Def_RHS
                [ "Descend into the right-hand side of a recursive definition." ]
            , external "app-fun" App_Fun
                [ "Descend into the function in an application." ]
            , external "app-arg" App_Arg
                [ "Descend into the argument in an application." ]
            , external "lam-body" Lam_Body
                [ "Descend into the body of a lambda." ]
            , external "let-bind" Let_Bind
                [ "Descend into the binding group of a let expression." ]
            , external "let-body" Let_Body
                [ "Descend into the body of a let expression." ]
            , external "case-expr" Case_Scrutinee
                [ "Descend into the scrutinised expression in a case expression." ]
            , external "case-type" Case_Type
                [ "Descend into the type of a case expression." ]
            , external "case-alt" Case_Alt
                [ "Descend into the (n-1)th alternative in a case expression." ]
            , external "cast-expr" Cast_Expr
                [ "Descend into the expression in a cast." ]
            , external "cast-co" Cast_Co
                [ "Descend into the coercion in a cast." ]
            , external "tick-expr" Tick_Expr
                [ "Descend into the expression in a tick." ]
            , external "alt-rhs" Alt_RHS
                [ "Descend into the right-hand side of a case alternative." ]
            , external "type" Type_Type
                [ "Descend into the type within a type expression." ]
            , external "coercion" Co_Co
                [ "Descend into the coercion within a coercion expression." ]
            , external "appTy-fun" AppTy_Fun
                [ "Descend into the type function in a type application." ]
            , external "appTy-arg" AppTy_Fun
                [ "Descend into the type argument in a type application." ]
            , external "tyCon-arg" TyConApp_Arg
                [ "Descend into the (n-1)th argument of a type constructor application." ]
            , external "fun-dom" FunTy_Dom
                [ "Descend into the domain of a function type." ]
            , external "fun-cod" FunTy_CoDom
                [ "Descend into the codomain of a function type." ]
            , external "forall-body" ForAllTy_Body
                [ "Descend into the body of a forall type." ]
            , external "refl-type" Refl_Type
                [ "Descend into the (n-1)th argument of a type constructor coercion." ]
            , external "coCon-arg" TyConAppCo_Arg
                [ "Descend into the function of a coercion application." ]
            , external "appCo-fun" AppCo_Fun
                [ "Descend into the coercion function in a coercion application." ]
            , external "appCo-arg" AppCo_Arg
                [ "Descend into the coercion argument in a coercion application." ]
            , external "coForall-body" ForAllCo_Body
                [ "Descend into the body of a forall coercion." ]
            , external "axiom-inst" AxiomInstCo_Arg
                [ "Descend into the (n-1)th argument of a coercion axiom instantiation." ]
            , external "unsafe-left" UnsafeCo_Left
                [ "Descend into the left-hand type of an unsafe coercion." ]
            , external "unsafe-right" UnsafeCo_Right
                [ "Descend into the right-hand type of an unsafe coercion." ]
            , external "sym-co" SymCo_Co
                [ "Descend into the coercion within a symmetric coercion." ]
            , external "trans-left" TransCo_Left
                [ "Descend into the left-hand type of a transitive coercion." ]
            , external "trans-right" TransCo_Right
                [ "Descend into the right-hand type of a transitive coercion." ]
            , external "nth-co" NthCo_Co
                [ "Descend into the coercion within an nth projection coercion." ]
            , external "inst-co" InstCo_Co
                [ "Descend into the coercion within a coercion instantiation." ]
            , external "inst-type" InstCo_Type
                [ "Descend into the type within a coercion instantiation." ]
            , external "lr-co" LRCo_Co
                [ "Descend into the coercion within a left/right projection coercion." ]
            ]

---------------------------------------------------------------------------------------
