{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ListMonad where

import Control.Monad.Reader
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Fail as Fail
import Control.Monad.State
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity

newtype ListT m a = ListT { runListT :: m [a] }
                  deriving Functor

instance Monad m => Applicative (ListT m) where
  pure  x = ListT $ return [x]
  ListT f <*> ListT x = ListT $ do
    x' <- x
    f' <- f
    return $ foldl (\ bs g -> map g x' ++ bs) [] f'
      
instance Monad m => Monad (ListT m) where
  ListT a >>= k = ListT $ do
    a' <- a
    foldl (\ mbs b -> let ListT x = k b in do
              mbs' <- mbs
              x'   <- x
              return (x' ++ mbs')) (return []) a'

instance MonadTrans ListT where
  lift = \ ma -> ListT $ do
    a' <- ma
    return [a']

instance MonadReader r m => MonadReader r (ListT m) where
  ask = lift ask
  local f (ListT m) = ListT $ local f m
  reader = lift . reader

instance Monad m => MonadFail (ListT m) where
  fail _ = ListT $ return []

instance MonadState s m => MonadState s (ListT m) where
  state = lift . state
  get   = lift get
  put   = lift . put

instance (Applicative m, Monad m) => Alternative (ListT m) where
  empty = ListT $ return []
  (ListT m1) <|> (ListT m2) = ListT $ do
    vs1 <- m1
    vs2 <- m2
    return $ vs1 ++ vs2

instance MonadError a m => MonadError a (ListT m) where
  throwError s = lift (throwError s)
  catchError (ListT m) k = ListT $
    catchError m (runListT . k)
    

instance Monad m => MonadPlus (ListT m) where

