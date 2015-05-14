{-# LANGUAGE GADTs, KindSignatures, FlexibleInstances, 
             StandaloneDeriving, ConstraintKinds, FlexibleContexts
  #-}
module HERMIT.Shell.Effector where
        
import HERMIT.Kure
import HERMIT.Shell.Types

class Effector e where
   toEffectH :: (MonadCatch m, CLMonad m) => e -> m ()
