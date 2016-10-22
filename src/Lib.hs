{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Lib where

import           Control.Lens
import           Control.Monad.Free
import           Data.Proxy

-- Coproducts, and prism/typeclass-based injection
--
-- adapted from a combination of:
-- - http://mpickering.github.io/posts/2014-12-20-closed-type-family-data-types.html
-- - http://degoes.net/articles/modern-fp
-- - http://degoes.net/articles/modern-fp-part-2

data (f :+: g) e
  = InL (f e)
  | InR (g e)
  deriving (Functor)

makePrisms ''(:+:)

data Crumbs = Here | L Crumbs | R Crumbs

data Resolution = Found Crumbs | NotFound | Ambiguous

type family Elem e f :: Resolution where
  Elem e e         = 'Found 'Here
  Elem e (l :+: r) = Choose (Elem e l) (Elem e r)
  Elem e f         = 'NotFound

type family Choose e f :: Resolution where
    Choose ('Found x) ('Found y) = 'Ambiguous
    Choose 'Ambiguous x = 'Ambiguous
    Choose x 'Ambiguous = 'Ambiguous
    Choose ('Found a) b = 'Found ('L a)
    Choose a ('Found b) = 'Found ('R b)
    Choose a b = 'NotFound

type Injection f g = forall a. Prism' (g a) (f a)

class Inject (res :: Resolution) f g where
  inj :: Proxy res -> Injection f g

instance Inject ('Found 'Here) f f where
  inj _ = id

instance Inject ('Found p) f l => Inject ('Found ('L p)) f (l :+: r) where
  inj _ = _InL . inj (Proxy :: Proxy ('Found p))

instance Inject ('Found p) f r => Inject ('Found ('R p)) f (l :+: r) where
  inj _ = _InR . inj (Proxy :: Proxy ('Found p))

type f :<: g = (Inject (Elem f g) f g, Functor g)

-- TODO: possibly use some standard natural transformation definition?
type f ~> g = forall a. f a -> g a
infixr 4 ~> -- TODO: not sure if this precedence level is correct for Haskell

inject :: forall f g. (f :<: g) => f ~> g
inject = review (inj resolution)
  where
    resolution :: Proxy (Elem f g)
    resolution = Proxy


--
-- Example usage
--


data MessageId
data Message

-- CPS transformation of Store, to get a base functor:
data StoreF a
  = GetMessage MessageId (Message -> a)
  | PutMessage Message (Message -> a)
  deriving (Functor)



-- Example 1: (less generic) typeclass targeting Free

class Functor f => Store f where
  getMessage :: MessageId -> Free f Message
  putMessage :: Message -> Free f Message

instance (StoreF :<: f) => Store f where
  getMessage mId = liftF $ inject $ GetMessage mId id
  putMessage m = liftF $ inject $ PutMessage m id

example2 :: (StoreF :<: f)
         => MessageId
         -> Free f Message
example2 messageId = do
  msg <- getMessage messageId
  -- ... modify msg ...
  putMessage msg



-- -- Example 2: more generic typeclass targeting any functor
--
-- class Functor f => Store f where
--   getMessage :: MessageId -> f Message
--   putMessage :: Message -> f Message
--
-- instance Store StoreF where
--   getMessage mId = GetMessage mId id
--   putMessage m = PutMessage m id
--
-- instance (StoreF :<: g) => Store (Free g) where
--   getMessage mId = liftF $ inject (getMessage mId :: StoreF Message)
--   putMessage m = liftF $ inject (putMessage m :: StoreF Message)
--
-- example2 :: (StoreF :<: f)
--          => MessageId
--          -> Free f Message
-- example2 messageId = do
--   msg <- getMessage messageId
--   -- ... modify msg ...
--   putMessage msg



