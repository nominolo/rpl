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

-- Monadic fold over two lists at once.  Input lists must be of same
-- length.
foldM2 :: Monad m => (a -> b -> c -> m a) -> a -> [b] -> [c] -> m a
foldM2 f a0 bs0 cs0 = worker a0 bs0 cs0
  where worker a [] [] = return a
        worker a (b:bs) (c:cs) = do a' <- f a b c
                                    worker a' bs cs
        worker _ _ _ = error "foldM2: arguments are not of same length"

