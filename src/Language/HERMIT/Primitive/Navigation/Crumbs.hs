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
            , external "case-alt" Case_Alt
                [ "Descend into the (n-1)th alternative in a case expression." ]
            , external "cast-expr" Cast_Expr
                [ "Descend into the expression in a cast." ]
            , external "tick-expr" Tick_Expr
                [ "Descend into the expression in a tick." ]
            , external "alt-rhs" Alt_RHS
                [ "Descend into the right-hand side of a case alternative." ]
            ]

---------------------------------------------------------------------------------------
