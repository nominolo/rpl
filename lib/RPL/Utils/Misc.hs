module RPL.Utils.Misc where

-- | Monadic variant of 'if' where the condition may have side effects.
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c t e = do b <- c; if b then t else e

-- | Monadic variant of 'Control.Monad.unless' where the condition may have
-- side effects.
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM c act = ifM c (return ()) act

-- | Monadic variant of 'Control.Monad.when' where the condition may have
-- side effects.
whenM :: Monad m => m Bool -> m () -> m ()
whenM c act = ifM c act (return ())
