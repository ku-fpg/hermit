{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HERMIT.Shell.Proof
    ( externals
    , UserProofTechnique
    , userProofTechnique
    , withProofExternals
    , performProofShellCommand
    , forceProofs
    , ProofShellCommand(PCEnd)
    , ProofReason(UserProof)
    ) where

import Control.Arrow hiding (loop, (<+>))
import Control.Monad (forM, forM_, liftM)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.State (MonadState, modify, gets)

import Data.Dynamic
import Data.List (delete, zipWith4)
import qualified Data.Map as M
import Data.Monoid
import Data.String (fromString)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>), text, sep, (<+>), ($+$), nest)
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name
import HERMIT.Parser
import HERMIT.Syntax
import HERMIT.Utilities

import HERMIT.Dictionary.Induction hiding (externals)
import HERMIT.Dictionary.Local.Case hiding (externals)
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.Dictionary.Undefined hiding (externals)

import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

--------------------------------------------------------------------------------------------------------

-- | Externals that get us into the prover shell.
externals :: [External]
externals = map (.+ Proof)
    [ external "prove-lemma" (CLSModifyAndShow . interactiveProofIO)
        [ "Proof a lemma interactively." ]
    ]

-- | Externals that are added to the dictionary only when in interactive proof mode.
proof_externals :: [External]
proof_externals = map (.+ Proof)
    [ external "lemma" (PCEnd . LemmaProof Obligation)
        [ "Prove lemma by asserting it is alpha-equivalent to an already proven lemma." ]
    , external "lemma-unsafe" (PCEnd . LemmaProof UnsafeUsed)
        [ "Prove lemma by asserting it is alpha-equivalent to an already proven lemma." ] .+ Unsafe
    , external "induction" (PCInduction . cmpString2Var :: String -> ProofShellCommand)
        [ "Perform induction on given universally quantified variable."
        , "Each constructor case will generate a new lemma to be proven."
        ]
    , external "prove-by-cases" (PCByCases . cmpString2Var :: String -> ProofShellCommand)
        [ "Case split on given universally quantified variable."
        , "Each constructor case will generate a new lemma to be proven."
        ]
    , external "prove-consequent" PCConsequent
        [ "Prove the consequent of an implication by assuming the antecedent." ]
    , external "prove-conjunction" PCConjunction
        [ "Prove a conjunction by proving both sides of it." ]
    , external "inst-assumed" (\ i nm cs -> PCInstAssumed i (cmpHN2Var nm) cs)
        [ "Split an assumed lemma which is a conjunction/disjunction." ]
    , external "split-assumed" PCSplitAssumed
        [ "Split an assumed lemma which is a conjunction/disjunction." ]
    , external "end-proof" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the lemma as proven" ]
    , external "end-case" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the proof case as proven" ]
    , external "assume" (PCEnd UserAssume)
        [ "mark lemma as assumed" ]
    ]

--------------------------------------------------------------------------------------------------------

-- | Top level entry point!
interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    (r,st) <- runCLT s $ do
                ps <- getProofStackEmpty
                let t :: TransformH x (HermitC,Lemma)
                    t = contextT &&& getLemmaByNameT nm
                (c,l) <- case ps of
                            [] -> queryInFocus (t :: TransformH Core (HermitC,Lemma))
                                               (Always $ "prove-lemma " ++ quoteShow nm)
                            todo : _ -> queryInFocus (inProofFocusT todo t) Never
                pushProofStack $ Unproven nm l c [] mempty
    return $ fmap (const st) r

withProofExternals :: (MonadError CLException m, MonadState CommandLineState m) => m a -> m a
withProofExternals comp = do
    (es,sf) <- gets (cl_externals &&& cl_safety)
    let pes = filterSafety sf proof_externals
        -- commands with same same in proof_externals will override those in normal externals
        newEs = pes ++ filter ((`notElem` (map externName pes)) . externName) es
        reset s = s { cl_externals = es }
    modify $ \ s -> s { cl_externals = newEs }
    r <- comp `catchError` (\case CLContinue s -> continue (reset s)
                                  other        -> modify reset >> throwError other)
    modify reset
    return r

forceProofs :: (MonadCatch m, CLMonad m) => m ()
forceProofs = do
    (c,nls) <- queryInFocus (contextT &&& getObligationNotProvenT :: TransformH Core (HermitC, [NamedLemma])) Never
    todos <- getProofStackEmpty
    let already = map ptName todos
        nls' = [ nl | nl@(nm,_) <- nls, not (nm `elem` already) ]
    if null nls'
    then return ()
    else do
        c' <- case todos of
                todo : _ -> queryInFocus (inProofFocusT todo contextT) Never
                _        -> return c
        forM_ nls' $ \ (nm,l) -> pushProofStack (Unproven nm l c' [] mempty)

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, CLMonad m) => ProofReason -> ExprH -> m ()
endProof reason expr = do
    Unproven nm (Lemma q _ _ temp) c ls _ : _ <- getProofStack
    let msg = "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."
        deleteOr tr = if temp then constT (deleteLemma nm) else tr
        t = case reason of
                UserAssume -> deleteOr (markLemmaProvenT nm Assumed)
                Reflexivity -> setFailMsg msg (do tryR (extractR reflexivityR) >>> verifyQuantifiedT
                                                  deleteOr (markLemmaProvenT nm Proven))
                LemmaProof u nm' -> verifyEquivalentT u nm' >> deleteOr (markLemmaProvenT nm Proven)
                UserProof up -> let UserProofTechnique tr = up
                                in extractT tr >> deleteOr (markLemmaProvenT nm Proven)
    queryInFocus (constT (withLemmas (M.fromList ls) $ applyT t c q) :: TransformH Core ())
                 (Always $ unparseExprH expr ++ " -- proven " ++ quoteShow nm)
    _ <- popProofStack
    cl_putStrLn $ "Successfully proven: " ++ show nm

-- Note [Query]
-- We want to do our proof in the current context of the shell, whatever that is,
-- so we run them using queryInFocus below. This has the benefit that proof commands
-- can generate additional lemmas, and add to the version history.
performProofShellCommand :: (MonadCatch m, CLMonad m)
                         => ProofShellCommand -> ExprH -> m ()
performProofShellCommand cmd expr = go cmd >> ifM isRunningScript (return ()) (showWindow Nothing)
    where str = unparseExprH expr
          go (PCInduction idPred) = performInduction (Always str) idPred
          go (PCByCases idPred)   = proveByCases (Always str) idPred
          go PCConsequent         = proveConsequent str
          go PCConjunction        = proveConjunction str
          go (PCInstAssumed i v cs) = instAssumed i v cs str
          go (PCSplitAssumed i)   = splitAssumed i str
          go (PCEnd why)          = endProof why expr

proveConsequent :: (MonadCatch m, CLMonad m) => String -> m ()
proveConsequent expr = do
    todo : _ <- getProofStack
    (c, Impl ante con) <- setFailMsg "not an implication" $
                          queryInFocus (inProofFocusT todo (contextT &&& projectT)) Never
    let nm = ptName todo
        ls = (nm <> "-antecedent", Lemma ante BuiltIn NotUsed True) : ptAssumed todo
    (k,ast) <- gets (cl_kernel &&& cl_cursor)
    addAST =<< tellK k expr ast
    _ <- popProofStack
    pushProofStack $ MarkProven nm (lemmaT (ptLemma todo)) -- proving the consequent proves the lemma
    pushProofStack $ Unproven (nm <> "-consequent") (Lemma con NotProven Obligation True) c ls mempty

proveConjunction :: (MonadCatch m, CLMonad m) => String -> m ()
proveConjunction expr = do
    Unproven nm (Lemma (Quantified bs cl) p u t) c ls _ : _ <- getProofStack
    case cl of
        Conj (Quantified lbs lcl) (Quantified rbs rcl) -> do
            (k,ast) <- gets (cl_kernel &&& cl_cursor)
            addAST =<< tellK k expr ast
            _ <- popProofStack
            pushProofStack $ MarkProven nm t
            pushProofStack $ Unproven (nm <> "-r") (Lemma (Quantified (bs++rbs) rcl) p u True) c ls mempty
            pushProofStack $ Unproven (nm <> "-l") (Lemma (Quantified (bs++lbs) lcl) p u True) c ls mempty
        _ -> fail "not a conjunction."

splitAssumed :: (MonadCatch m, CLMonad m) => Int -> String -> m ()
splitAssumed i expr = do
    Unproven nm lem c ls ps : _ <- getProofStack
    (b, (n, Lemma q p u t):a) <- getIth i ls
    qs <- splitQuantified q
    let nls = [ (n <> fromString (show j), Lemma q' p u t) | (j::Int,q') <- zip [0..] qs ]
    (k,ast) <- gets (cl_kernel &&& cl_cursor)
    addAST =<< tellK k expr ast
    _ <- popProofStack
    pushProofStack $ Unproven nm lem c (b ++ nls ++ a) ps

instAssumed :: (MonadCatch m, CLMonad m) => Int -> (Var -> Bool) -> CoreString -> String -> m ()
instAssumed i pr cs expr = do
    todo : _ <- getProofStack
    (b, orig@(n, Lemma q p u t):a) <- getIth i $ ptAssumed todo
    q' <- queryInFocus (inProofFocusT todo $ return q >>> instantiateQuantifiedVarR pr cs) Never
    (k,ast) <- gets (cl_kernel &&& cl_cursor)
    addAST =<< tellK k expr ast
    _ <- popProofStack
    pushProofStack $ todo { ptAssumed = b ++ orig:(n <> "'", Lemma q' p u t):a }

getIth :: MonadCatch m => Int -> [a] -> m ([a],[a])
getIth _ [] = fail "getIth: out of range"
getIth n (x:xs) = go n x xs []
    where go 0 y ys zs = return (reverse zs, y:ys)
          go _ _ [] _  = fail "getIth: out of range"
          go i z (y:ys) zs = go (i-1) y ys (z:zs)

-- | Always returns non-empty list, or fails.
splitQuantified :: MonadCatch m => Quantified -> m [Quantified]
splitQuantified (Quantified bs cl) = do
    case cl of
        Conj (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        Disj (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        Impl (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        _ -> fail "equalities cannot be split!"

performInduction :: (MonadCatch m, CLMonad m)
                 => CommitMsg -> (Id -> Bool) -> m ()
performInduction cm idPred = do
    (nm, Lemma q@(Quantified bs (Equiv lhs rhs)) _ _ temp, ctxt, ls, _) <- currentLemma
    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $
         soleElement (filter idPred bs)

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    cases <- queryInContext
                (inductionCaseSplit bs i lhs rhs :: TransformH LCoreTC [(Maybe DataCon, [Var], CoreExpr, CoreExpr)])
                cm

    -- replace the current lemma with the three subcases
    -- proving them will prove this case automatically
    _ <- popProofStack
    pushProofStack $ MarkProven nm temp
    forM_ (reverse cases) $ \ (mdc,vs,lhsE,rhsE) -> do

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            caseName = maybe "undefined" unqualifiedName mdc

        -- Generate list of specialized induction hypotheses for the recursive cases.
        qs <- forM vs_matching_i_type $ \ i' -> do
                liftM discardUniVars $ instQuantified (boundVars ctxt) (==i) (Var i') q
                -- TODO rethink the discardUniVars

        let nms = [ fromString ("ind-hyp-" ++ show n) | n :: Int <- [0..] ]
            hypLemmas = zip nms $ zipWith4 Lemma qs (repeat BuiltIn) (repeat NotUsed) (repeat True)
            lemmaName = fromString $ show nm ++ "-induction-case-" ++ caseName
            caseLemma = Lemma (mkQuantified (delete i bs ++ vs) lhsE rhsE) NotProven Obligation True

        pushProofStack $ Unproven lemmaName caseLemma ctxt (hypLemmas ++ ls) mempty

proveByCases :: (MonadCatch m, CLMonad m)
             => CommitMsg -> (Id -> Bool) -> m ()
proveByCases cm idPred = do
    (nm, Lemma (Quantified bs cl) _ _ temp, ctxt, ls, _) <- currentLemma
    guardMsg (any idPred bs) "specified identifier is not universally quantified in this lemma."
    let (as,b:bs') = break idPred bs -- safe because above guard
    guardMsg (not (any idPred bs')) "multiple matching quantifiers."

    cases <- queryInContext (do ue <- mkUndefinedValT (varType b)
                                liftM (ue:) (constT (caseExprsForM (varToCoreExpr b)))) cm

    -- replace the current lemma with the three subcases
    -- proving them will prove the overall lemma automatically
    _ <- popProofStack
    pushProofStack $ MarkProven nm temp
    forM_ (zip [(0::Int)..] $ reverse cases) $ \ (i,e) -> do

        let lemmaName = fromString $ show nm ++ "-case-" ++ show i
            Quantified bs'' cl' = substQuantified b e $ Quantified bs' cl
            fvs = varSetElems $ localFreeVarsExpr e
            caseLemma = Lemma (Quantified (as++fvs++bs'') cl') NotProven Obligation True

        pushProofStack $ Unproven lemmaName caseLemma ctxt ls mempty

data ProofShellCommand
    = PCInduction (Id -> Bool)
    | PCByCases (Id -> Bool)
    | PCConsequent
    | PCConjunction
    | PCSplitAssumed Int
    | PCInstAssumed Int (Var -> Bool) CoreString
    | PCEnd ProofReason
    deriving Typeable

data ProofReason = UserProof UserProofTechnique -- ^ Run the technique, mark Proven if succeeds
                 | UserAssume                   -- ^ Assume
                 | Reflexivity                  -- ^ Check for alpha-equivalence first
                 | LemmaProof Used LemmaName    -- ^ Used should be 'UnsafeUsed' or 'Obligation'

-- keep abstract to avoid breaking things if we modify this later
newtype UserProofTechnique = UserProofTechnique (TransformH LCoreTC ())
    deriving Typeable

userProofTechnique :: TransformH LCoreTC () -> UserProofTechnique
userProofTechnique = UserProofTechnique

instance Extern ProofShellCommand where
    type Box ProofShellCommand = ProofShellCommand
    box i = i
    unbox i = i

instance Extern UserProofTechnique where
    type Box UserProofTechnique = UserProofTechnique
    box i = i
    unbox i = i
