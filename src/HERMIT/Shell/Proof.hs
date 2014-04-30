{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ScopedTypeVariables, TypeFamilies, TypeSynonymInstances #-}

module HERMIT.Shell.Proof
    ( externals
    , ProofCommand(..)
    , performProofCommand
    , UserProofTechnique
    , userProofTechnique
    ) where

import Control.Arrow hiding (loop)
import Control.Concurrent
import Control.Monad.Error
import Control.Monad.State

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (delete)

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>))
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Parser
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.Dictionary.Rules hiding (externals)

import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean

import HERMIT.Shell.Interpreter
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

import System.Console.Haskeline hiding (catch, display)

import System.IO

--------------------------------------------------------------------------------------------------------

-- | Externals that get us into the prover shell, or otherwise deal with lemmas.
externals :: [External]
externals = map (.+ Proof)
    [ external "rule-to-lemma" RuleToLemma
        [ "Create a lemma from a GHC RULE." ]
    , external "show-lemmas" ShowLemmas
        [ "List lemmas." ]
    , external "lemma" ((\s -> promoteExprBiR . lemma False s) :: CommandLineState -> LemmaName -> BiRewriteH Core)
        [ "Generate a bi-directional rewrite from a proven lemma." ]
    , external "lemma-unsafe" ((\s -> promoteExprBiR . lemma True s) :: CommandLineState -> LemmaName -> BiRewriteH Core)
        [ "Generate a bi-directional rewrite from a lemma, even if it is unproven." ]
    , external "lemma-lhs-intro" (lemmaLhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core)
        [ "Introduce the LHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
    , external "lemma-rhs-intro" (lemmaRhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core)
        [ "Introduce the RHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
    , external "prove-lemma" InteractiveProof
        [ "Proof a lemma interactively." ]
    , external "instantiate-lemma" (\ nm v cs -> ModifyLemma nm (++"-inst") (instantiateEqualityVarR (cmpString2Var v) cs >>> tryR instantiateDictsR) id)
        [ "Instantiate one of the universally quantified variables of the given lemma,"
        , "with the given Core expression, creating a new lemma. Instantiating an" 
        , "already proven lemma will result in the new lemma being considered proven." ]
    , external "instantiate-lemma-dictionaries" (\ nm -> ModifyLemma nm (++"-nodicts") instantiateDictsR id)
        [ "Instantiate all of the universally quantified dictionaries of the given lemma."
        , "Only works on dictionaries whose types are monomorphic (no free type variables)." ]
    , external "copy-lemma" (\ nm newName -> ModifyLemma nm (const newName) idR id)
        [ "Copy a given lemma, with a new name." ]
    , external "modify-lemma" (\ nm rr -> ModifyLemma nm id rr (const False))
        [ "Modify a given lemma. Resets the proven status to Not Proven." ]
    , external "extensionality" (extensionalityR . Just :: String -> RewriteH CoreExprEquality)
        [ "Given a name 'x, then"
        , "f == g  ==>  forall x.  f x == g x" ]
    , external "extensionality" (extensionalityR Nothing :: RewriteH CoreExprEquality)
        [ "f == g  ==>  forall x.  f x == g x" ]
    , external "lhs" (lhsR . extractR :: RewriteH Core -> RewriteH CoreExprEquality)
        [ "Apply a rewrite to the LHS of an equality." ]
    , external "lhs" (lhsT . extractT :: TransformH CoreTC String -> TransformH CoreExprEquality String)
        [ "Apply a transformation to the LHS of an equality." ]
    , external "rhs" (rhsR . extractR :: RewriteH Core -> RewriteH CoreExprEquality)
        [ "Apply a rewrite to the RHS of an equality." ]
    , external "rhs" (rhsT . extractT :: TransformH CoreTC String -> TransformH CoreExprEquality String)
        [ "Apply a transformation to the RHS of an equality." ]
    , external "both" (bothR . extractR :: RewriteH Core -> RewriteH CoreExprEquality)
        [ "Apply a rewrite to both sides of an equality, succeeding if either succeed." ]
    , external "both" ((\t -> liftM (\(r,s) -> unlines [r,s]) (bothT (extractT t))) :: TransformH CoreTC String -> TransformH CoreExprEquality String)
        [ "Apply a transformation to the RHS of an equality." ]
    ]

-- | Externals that are added to the dictionary only when in interactive proof mode.
proof_externals :: [External]
proof_externals = map (.+ Proof)
    [ external "induction" (PCInduction . cmpString2Var :: String -> ProofShellCommand)
        [ "Perform induction on given universally quantified variable."
        , "Each constructor case will generate a new CoreExprEquality to be proven."
        ]
    ]

--------------------------------------------------------------------------------------------------------

data ProofCommand
    = RuleToLemma RuleNameString
    | InteractiveProof LemmaName
    | ModifyLemma LemmaName (String -> String) (RewriteH CoreExprEquality) (Bool -> Bool)
    | ShowLemmas
    deriving (Typeable)

instance Extern ProofCommand where
    type Box ProofCommand = ProofCommand
    box i = i
    unbox i = i

--------------------------------------------------------------------------------------------------------

getLemmaByName :: Monad m => CommandLineState -> LemmaName -> m Lemma
getLemmaByName st nm =
    case [ lm | lm@(n,_,_) <- cl_lemmas st, n == nm ] of
        []    -> fail ("No lemma named: " ++ nm)
        (l:_) -> return l

deleteLemmaByName :: MonadState CommandLineState m => LemmaName -> m ()
deleteLemmaByName nm = modify $ \ st -> st { cl_lemmas = [ l | l@(n,_,_) <- cl_lemmas st, nm /= n ] }

lemma :: Bool -> CommandLineState -> LemmaName -> BiRewriteH CoreExpr
lemma ok st nm = beforeBiR
                   (do (_,equality,proven) <- getLemmaByName st nm
                       guardMsg (proven || ok) ("Lemma " ++ nm ++ " has not been proven.")
                       return equality
                   )
                   birewrite

--------------------------------------------------------------------------------------------------------

lemmaNameToEqualityT :: Monad m => CommandLineState -> LemmaName -> m CoreExprEquality
lemmaNameToEqualityT st nm =
  do (_,eq,_) <- getLemmaByName st nm
     return eq

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core
lemmaLhsIntroR st = lemmaNameToEqualityT st >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core
lemmaRhsIntroR st = lemmaNameToEqualityT st >=> eqRhsIntroR

--------------------------------------------------------------------------------------------------------

performProofCommand :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => ProofCommand -> m ()
performProofCommand (RuleToLemma nm) = do
    st <- gets cl_pstate
    equality <- queryS (ps_kernel st) (ruleNameToEqualityT nm :: TransformH Core CoreExprEquality) (mkKernelEnv st) (ps_cursor st)
    _ <- addLemmas [(nm,equality,False)]
    return ()

performProofCommand (InteractiveProof nm) = get >>= flip getLemmaByName nm >>= interactiveProof True

performProofCommand (ModifyLemma nm nFn rr pFn) = do
    st <- get
    (_,eq,p) <- getLemmaByName st nm
    
    -- query so lemma is transformed in current context
    eq' <- queryS (cl_kernel st) (return eq >>> rr :: TransformH Core CoreExprEquality) (cl_kernel_env st) (cl_cursor st)
    when (nFn nm == nm) $ deleteLemmaByName nm
    _ <- addLemmas [(nFn nm, eq', pFn p)]
    return ()

performProofCommand ShowLemmas = gets cl_lemmas >>= \ ls -> forM_ (reverse ls) printLemma

--------------------------------------------------------------------------------------------------------

printLemma :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Lemma -> m ()
printLemma (nm, CoreExprEquality bs lhs rhs, proven) = do
    st <- gets cl_pstate
    let k    = ps_kernel st
        env  = mkKernelEnv st
        sast = ps_cursor st
        pos  = ps_pretty_opts st
        pp   = ps_pretty st
        pr :: [Var] -> CoreExpr -> TransformH Core DocH
        pr vs e = return e >>> withVarsInScope vs (extractT $ liftPrettyH pos pp)
    cl_putStr nm
    cl_putStrLn $ if proven then " (Proven)" else " (Not Proven)"
    unless (null bs) $ do
        forallDoc <- queryS k (return bs >>> extractT (liftPrettyH pos Clean.ppForallQuantification) :: TransformH Core DocH) env sast -- TODO: rather than hardwiring the Clean PP here, we should store a pretty printer in the shell state, which should match the main PP, and be updated correspondingly.
        liftIO $ ps_render st stdout pos (Right forallDoc)
    lDoc <- queryS k (pr bs lhs) env sast
    rDoc <- queryS k (pr bs rhs) env sast
    liftIO $ ps_render st stdout pos (Right lDoc)
    cl_putStrLn "=="
    liftIO $ ps_render st stdout pos (Right rDoc)
    cl_putStrLn ""

--------------------------------------------------------------------------------------------------------

completeProof :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => LemmaName -> m ()
completeProof nm = do
    cl_putStrLn $ "Successfully proven: " ++ nm
    modify $ \ st -> st { cl_lemmas = [ (n,e, if n == nm then True else p) | (n,e,p) <- cl_lemmas st ] }
    get >>= continue

interactiveProof :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Bool -> Lemma -> m ()
interactiveProof topLevel lem = do
    origEs <- addProofExternals topLevel
    origSt <- get
    completionMVar <- liftIO $ newMVar origSt

    let ws_complete = " ()"

        -- If we are mid-script, then we just hit a call to interactive-proof,
        -- so treat the rest of the script as if it were a proof script.
        startup :: Lemma -> CLT (InputT IO) Lemma
        startup l = popScriptLine >>= maybe (return l) (runExprH l >=> startup)

        -- Main proof input loop
        loop :: Lemma -> CLT (InputT IO) ()
        loop l = do
            printLemma l
            st <- get
            liftIO $ modifyMVar_ completionMVar (const $ return st) -- so the completion can get the current state
            mLine <- lift $ getInputLine $ "proof> "

            case mLine of
                Nothing          -> fail "proof aborted (input: Nothing)"
                Just ('-':'-':_) -> loop l
                Just line        -> if all isSpace line
                                    then loop l
                                    else (evalProofScript l line `catchM` (\msg -> cl_putStrLn msg >> return l)) >>= loop

    -- Display a proof banner?

    -- Start the CLI
    let settings = setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings
        cleanup s = put (s { cl_externals = origEs }) 
    (r,_s) <- get >>= liftIO . runInputTBehavior defaultBehavior settings . flip runCLT (startup lem >>= loop)
    case r of
        Right _               -> return ()      -- this case isn't possible, loop never returns
        Left CLAbort          -> cleanup origSt >> unless topLevel abort -- abandon proof attempt, bubble out to regular shell
        Left (CLContinue st') -> cleanup st'    -- successfully proven
        Left _                -> fail "unsupported exception in interactive prover"

addProofExternals :: MonadState CommandLineState m => Bool -> m [External]
addProofExternals topLevel = do
    st <- get
    let es = cl_externals st
    when topLevel $ modify $ \ s -> s { cl_externals = proof_externals ++ es } 
    return es

evalProofScript :: MonadIO m => Lemma -> String -> CLT m Lemma
evalProofScript lem = parseScriptCLT >=> foldM runExprH lem

runExprH :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Lemma -> ExprH -> m Lemma
runExprH lem expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n")
                  $ interpExprH interpProof expr >>= performProofShellCommand lem

-- To decide whether to continue the proof or not.
checkProven :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Lemma -> m ()
checkProven (nm, eq, _) = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    b <- (queryS sk (return eq >>> testM verifyCoreExprEqualityT :: TransformH Core Bool) kEnv sast)
    when b $ completeProof nm

performProofShellCommand :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Lemma -> ProofShellCommand -> m Lemma
performProofShellCommand lem@(nm, eq, b) = go
    where go (PCRewrite rr)         = do
                st <- get
                let sk = cl_kernel st
                    kEnv = cl_kernel_env st
                    sast = cl_cursor st

                -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
                eq' <- queryS sk (return eq >>> rr :: TransformH Core CoreExprEquality) kEnv sast
                let lem' = (nm, eq', b)
                checkProven lem'
                return lem'
          go (PCTransform t)      = do
                st <- get
                let sk = cl_kernel st
                    kEnv = cl_kernel_env st
                    sast = cl_cursor st

                -- Why do a query? See above.
                res <- queryS sk (return eq >>> t :: TransformH Core String) kEnv sast
                cl_putStrLn res
                return lem
          go (PCInduction idPred) = performInduction lem idPred
          go (PCShell effect)     = performShellEffect effect >> return lem
          go (PCScript effect)    = do
                lemVar <- liftIO $ newMVar lem -- couldn't resist that name
                let lemHack e = liftIO (takeMVar lemVar) >>= flip runExprH e >>= \l -> liftIO (putMVar lemVar l) >> checkProven l
                performScriptEffect lemHack effect
                liftIO $ takeMVar lemVar
          go (PCQuery query)      = performQuery query (error "PCQuery ExprH") >> return lem
          go (PCProofCommand cmd) = performProofCommand cmd >> return lem
          go (PCUser prf)         = let UserProofTechnique t = prf in -- may add more constructors later
             do
                st <- get
                -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
                queryS (cl_kernel st) (return eq >>> t :: TransformH Core ()) (cl_kernel_env st) (cl_cursor st)
                completeProof nm -- note: we assume that if 't' completes without failing, the lemma is proved, we don't actually check
                return lem       -- never reached
          go (PCUnsupported s)    = cl_putStrLn s >> return lem

performInduction :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => Lemma -> (Id -> Bool) -> m Lemma
performInduction lem@(nm, eq@(CoreExprEquality bs lhs rhs), _) idPred = do
    st <- get
    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st

    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)
    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    cases <- queryS sk (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon,[Var],CoreExpr,CoreExpr)]) kEnv sast

    forM_ cases $ \ (mdc,vs,lhsE,rhsE) -> do

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            -- Generate list of specialized induction hypotheses for the recursive cases.
            eqs = [ discardUniVars $ instantiateEqualityVar (==i) (Var i') eq
                  | i' <- vs_matching_i_type ]
            nms = [ "ind-hyp-" ++ show n | n :: Int <- [0..] ]
            hypLemmas = zip3 nms eqs (repeat True)
            caseLemma = ( nm ++ "-induction-on-" ++ getOccString i ++ "-case-" ++ maybe "undefined" getOccString mdc
                        , CoreExprEquality (delete i bs ++ vs) lhsE rhsE
                        , False )

        origLemmas <- addLemmas hypLemmas
        interactiveProof False caseLemma -- recursion!
        modify $ \ s -> s { cl_lemmas = origLemmas } -- put original lemmas back

    completeProof nm
    return lem -- this is never reached, but the type says we need it.

addLemmas :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => [Lemma] -> m [Lemma]
addLemmas lems = do
    forM_ lems printLemma
    st <- get
    put $ st { cl_lemmas = cl_lemmas st ++ lems }
    return $ cl_lemmas st

data ProofShellCommand
    = PCRewrite (RewriteH CoreExprEquality)
    | PCTransform (TransformH CoreExprEquality String)
    | PCInduction (Id -> Bool)
    | PCShell ShellEffect
    | PCScript ScriptEffect
    | PCQuery QueryFun
    | PCProofCommand ProofCommand
    | PCUser UserProofTechnique
    | PCUnsupported String
    deriving Typeable

-- keep abstract to avoid breaking things if we modify this later
newtype UserProofTechnique = UserProofTechnique (TransformH CoreExprEquality ())

userProofTechnique :: TransformH CoreExprEquality () -> UserProofTechnique
userProofTechnique = UserProofTechnique

instance Extern ProofShellCommand where
    type Box ProofShellCommand = ProofShellCommand
    box i = i
    unbox i = i

data RewriteCoreExprEqualityBox = 
        RewriteCoreExprEqualityBox (RewriteH CoreExprEquality) deriving Typeable

instance Extern (RewriteH CoreExprEquality) where
    type Box (RewriteH CoreExprEquality) = RewriteCoreExprEqualityBox
    box = RewriteCoreExprEqualityBox
    unbox (RewriteCoreExprEqualityBox r) = r

data TransformCoreExprEqualityStringBox = 
        TransformCoreExprEqualityStringBox (TransformH CoreExprEquality String) deriving Typeable

instance Extern (TransformH CoreExprEquality String) where
    type Box (TransformH CoreExprEquality String) = TransformCoreExprEqualityStringBox 
    box = TransformCoreExprEqualityStringBox 
    unbox (TransformCoreExprEqualityStringBox t) = t

data UserProofTechniqueBox = UserProofTechniqueBox UserProofTechnique deriving Typeable

instance Extern UserProofTechnique where
    type Box UserProofTechnique = UserProofTechniqueBox
    box = UserProofTechniqueBox
    unbox (UserProofTechniqueBox t) = t

interpProof :: [Interp ProofShellCommand]
interpProof =
  [ interp $ \ (RewriteCoreBox rr)                    -> PCRewrite $ bothR $ extractR rr
  , interp $ \ (RewriteCoreTCBox rr)                  -> PCRewrite $ bothR $ extractR rr
  , interp $ \ (BiRewriteCoreBox br)                  -> PCRewrite $ bothR $ (extractR (forwardT br) <+ extractR (backwardT br))
  , interp $ \ (effect :: ShellEffect)                -> PCShell effect
  , interp $ \ (effect :: ScriptEffect)               -> PCScript effect
  , interp $ \ (StringBox str)                        -> PCQuery (message str)
  , interp $ \ (query :: QueryFun)                    -> PCQuery query
  , interp $ \ (cmd :: ProofCommand)                  -> PCProofCommand cmd
  , interp $ \ (RewriteCoreExprEqualityBox r)         -> PCRewrite r
  , interp $ \ (TransformCoreExprEqualityStringBox t) -> PCTransform t
  , interp $ \ (UserProofTechniqueBox t)              -> PCUser t
  , interp $ \ (cmd :: ProofShellCommand)             -> cmd
  , interp $ \ (CrumbBox _cr)                         -> PCUnsupported "CrumbBox"
  , interp $ \ (PathBox _p)                           -> PCUnsupported "PathBox"
  , interp $ \ (TransformCorePathBox _tt)             -> PCUnsupported "TransformCorePathBox"
  , interp $ \ (TransformCoreTCPathBox _tt)           -> PCUnsupported "TransformCoreTCPathBox"
  , interp $ \ (TransformCoreStringBox _tt)           -> PCUnsupported "TransformCoreStringBox"
  , interp $ \ (TransformCoreTCStringBox _tt)         -> PCUnsupported "TransformCoreTCStringBox"
  , interp $ \ (TransformCoreTCDocHBox _tt)           -> PCUnsupported "TransformCoreTCDocHBox"
  , interp $ \ (TransformCoreCheckBox _tt)            -> PCUnsupported "TransformCoreCheckBox"
  , interp $ \ (TransformCoreTCCheckBox _tt)          -> PCUnsupported "TransformCoreTCCheckBox"
  , interp $ \ (_effect :: KernelEffect)              -> PCUnsupported "KernelEffect"
  ]

