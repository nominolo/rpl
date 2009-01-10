{-# LANGUAGE Rank2Types, BangPatterns #-}
module RPL.Utils.Monads where

import Control.Applicative

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

runStrictStateErrorM :: StrictStateErrorM s e a -> s -> Either e (s,a)
runStrictStateErrorM m s0 =
  unSSEM m (\s a -> Right (s, a)) Left s0

getState :: StrictStateErrorM s e s
getState = SSEM $ \k _ s -> k s s

setState :: s -> StrictStateErrorM s e ()
setState s' = SSEM $ \k _ _ -> k s' ()

gets :: (s -> a) -> StrictStateErrorM s e a
gets f = f <$> getState

modifyState :: (s -> s) -> StrictStateErrorM s e ()
modifyState f = SSEM $ \k _ s -> let !s' = f s in k s' ()

throwError :: e -> StrictStateErrorM s e a
throwError err = SSEM $ \_ e _ -> e err

catchError :: StrictStateErrorM s e a
           -> (e -> StrictStateErrorM s e a)
           -> StrictStateErrorM s e a
catchError m h =
    SSEM $ \k e s -> unSSEM m k (\err -> unSSEM (h err) k e s) s
