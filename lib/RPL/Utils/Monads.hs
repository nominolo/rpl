{-# LANGUAGE Rank2Types, BangPatterns, FlexibleInstances, MultiParamTypeClasses #-}
module RPL.Utils.Monads 
  ( StrictStateErrorM, runStrictStateErrorM,
    MonadState(..), gets, modify,
    MonadError(..), MonadIO(..),
    StrictStateErrorT, runStrictStateErrorT
  )
where

import Control.Monad.Trans
import Control.Applicative
import Control.Monad.State.Class
import Control.Monad.Error.Class

-- * 'StrictStateErrorM' Monad

newtype StrictStateErrorM s e a
  = SSEM { unSSEM :: forall r.
                     (s -> a -> r)
                  -> (e -> r)
                  -> s
                  -> r 
         }

instance Functor (StrictStateErrorM s e) where
  fmap f m = SSEM $ \k e s -> unSSEM m (\s' a -> k s' (f a)) e s

instance Monad (StrictStateErrorM s e) where
  return a = SSEM $ \k _ s -> k s a
  (SSEM f) >>= g  = SSEM $ \k e s -> f (\s' a -> unSSEM (g a) k e s') e s

instance Applicative (StrictStateErrorM s e) where
  pure a = SSEM $ \k _ s -> k s a
  mf <*> mx = SSEM $ \k e s -> 
                unSSEM mf (\s' f -> unSSEM mx (\s'' x -> k s'' (f x)) e s') e s

runStrictStateErrorM :: StrictStateErrorM s e a -> s -> Either e a
runStrictStateErrorM m s0 =
  unSSEM m (\_s a -> Right a) Left s0

instance MonadState s (StrictStateErrorM s e) where
  get = SSEM $ \k _ s -> k s s
  put s' = SSEM $ \k _ _ -> k s' ()

instance MonadError e (StrictStateErrorM s e) where
  throwError err = SSEM $ \_ e _ -> e err
  catchError m h =
    SSEM $ \k e s -> unSSEM m k (\err -> unSSEM (h err) k e s) s

------------------------------------------------------------------------
-- * 'StrictStateErrorM' Monad Transformer

newtype StrictStateErrorT s e m a
  = SSET { unSSET :: forall r.
                     (s -> a -> m r)
                  -> (e -> m r)
                  -> s
                  -> m r 
         }

runStrictStateErrorT :: Monad m => StrictStateErrorT s e m a -> s -> m (Either e (a, s))
runStrictStateErrorT m s0 =
  unSSET m (\s a -> return $ Right (a, s)) (return . Left) s0

instance Functor m => Functor (StrictStateErrorT s e m) where
  fmap f m = SSET $ \k e s -> unSSET m (\s' a -> k s' (f a)) e s

instance Monad m => Monad (StrictStateErrorT s e m) where
  return a = SSET $ \k _ s -> k s a
  (SSET f) >>= g = SSET $ \k e s -> f (\s' a -> unSSET (g a) k e s') e s

instance Applicative m => Applicative (StrictStateErrorT s e m) where
  pure a = SSET $ \k _ s -> k s a
  mf <*> mx = SSET $ \k e s -> 
                unSSET mf (\s' f -> unSSET mx (\s'' x -> k s'' (f x)) e s') e s

instance MonadTrans (StrictStateErrorT s e) where
  lift m = SSET $ \k _ s -> m >>= k s

instance MonadIO m => MonadIO (StrictStateErrorT s e m) where
  liftIO io = SSET $ \k _ s -> liftIO io >>= k s

instance Monad m => MonadState s (StrictStateErrorT s e m) where
  get = SSET $ \k _ s -> k s s
  put s' = SSET $ \k _ _ -> k s' ()

instance Monad m => MonadError e (StrictStateErrorT s e m) where
  throwError err = SSET $ \_ e _ -> e err
  catchError m h =
    SSET $ \k e s -> unSSET m k (\err -> unSSET (h err) k e s) s
