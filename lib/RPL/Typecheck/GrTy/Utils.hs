{-# LANGUAGE FlexibleContexts #-}
module RPL.Typecheck.GrTy.Utils where

import RPL.Typecheck.GrTy.Types
import qualified RPL.Type as Typ
import qualified RPL.BuiltIn as Typ
import RPL.Typecheck.GrTy.TestUtils
import RPL.Utils.Monads
import Control.Applicative
import Control.Monad ( foldM )

import qualified Data.IntSet as IS

infixr 6 -->

tu1 = do 
  n <- runM $ (nInt --> nInt) --> nInt --> nInt
--        (forAll $ \a ->
--         (forAll $ \b -> a --> b) --> (forAll $ \b -> a --> b))
--        --> nInt
--        (forAll $ \a -> (forAll $ \b -> b --> b) --> a)
  dottyNode n

-- tu2 = (forAll $ \a ->
--         --(letN (forAll $ \b -> a --> b) $ \n -> n --> n))
--       --> nInt


forAll :: (MonadGen NodeId m, MonadIO m, Applicative m) => (m Node -> m Node) -> m Node
forAll f = do v <- newNode Bot []
              n <- f (pure v)
              bindTo v (Just n) Flex
              return n

(-->) :: (MonadGen NodeId m, MonadIO m, Applicative m) =>
         m Node -> m Node -> m Node
x --> y = do n1 <- x
             n2 <- y
             arr <- newNode (TyConNode Typ.funTyCon) [n1,n2]
             bindTo n1 (Just arr) Rigid
             bindTo n2 (Just arr) Rigid
             return arr

nInt :: (MonadGen NodeId m, MonadIO m) => m Node             
nInt = do newNode (TyConNode Typ.typeInt) []
          
tu2 = runM $ do
  n1 <- newNode Bot []
  n2 <- newNode Bot []
  n3 <- newNode Bot []
  n4 <- newNode Bot []
  n5 <- newNode (TyConNode Typ.funTyCon) [n1,n2]
  n6 <- newNode (TyConNode Typ.funTyCon) [n3,n4]
  n7 <- newNode (TyConNode Typ.funTyCon) [n5,n6]
  bindTo n6 (Just n7) Flex
  bindTo n3 (Just n6) Flex
  bindTo n4 (Just n6) Flex
  bindTo n5 (Just n7) Flex
  bindTo n1 (Just n5) Flex
  bindTo n2 (Just n5) Flex
  liftIO $ do
    --dottyNode n7
    print =<< locallyCongruent n1 n2
    print =<< locallyCongruent n1 n3
    print =<< locallyCongruent n3 n4
    print =<< locallyCongruent n5 n6
