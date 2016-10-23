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

import           Prelude hiding (log)
import           Control.Lens
import           Control.Monad.Free
import           Control.Monad (void)
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

type family Choose a b :: Resolution where
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

newtype Halt f a = Halt (f ()) deriving (Functor)



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





-- Adding another algebra

data LogF a
  = Log String a
  deriving (Functor)

class Functor f => Logging f where
  log :: String -> Free f ()

instance (LogF :<: f) => Logging f where
  log msg = liftF $ inject $ Log msg ()

-- A program which both gets a message and does some logging side-by-side. This
-- is not as modular as we could be, by adding a Store-to-Logging interpreter,
-- composing that with a Store-to-lower-level interpreter, and using this
-- composite interpreter.
storeAndLog :: (StoreF :<: f, LogF :<: f)
            => MessageId
            -> Free f Message
storeAndLog mId = do
  log "getting a message"
  getMessage mId



-- A database algebra

data Row
type Sql = String

data DatabaseF a
  = Query Sql (Row -> a)
  | Execute Sql a
  deriving (Functor)

class Functor f => Database f where
  query :: Sql -> Free f Row
  execute :: Sql -> Free f ()

instance (DatabaseF :<: f) => Database f where
  query sql = liftF $ inject $ Query sql id
  execute sql = liftF $ inject $ Execute sql ()




-- Interpretation

type Interpreter f g = f ~> Free g
type f ~< g = Interpreter f g
infixr 4 ~< -- TODO: not sure if this precedence level is correct for Haskell


storeDatabase :: StoreF ~< DatabaseF
storeDatabase (GetMessage mId next) = next . mkMessage <$> query (sql mId)
  where
    sql :: MessageId -> Sql
    sql = undefined
    mkMessage :: Row -> Message
    mkMessage = undefined
storeDatabase (PutMessage m next) = next . const m <$> execute (sql m)
  where
    sql :: Message -> Sql
    sql = undefined



-- TODO: not sure if this is correct...
halt :: Functor f => Free f () -> Free (Halt f) a
-- halt (Pure ()) = Free $ Halt $ pure () -- TODO: or maybe take a default value
halt (Pure ()) = error "expected a program of length 1?"
halt (Free as) = Free $ Halt $ void as

storeLogging :: StoreF ~< Halt LogF
storeLogging (GetMessage _mId _next) = halt $ log "getting message"
storeLogging (PutMessage _m _next) = halt $ log "putting message"

-- TODO: how to best handle if we didn't want to log for every action in an
-- algebra? Add a Noop LogF constructor? or use Coproduct with Const or
-- something?

-- TODO: what if we wanted to log more than once in response to an operation?


-- Interpreter composition
--
--   Cases:
--     1. a ~< b -> a ~< c -> a ~< (b :+: c)
--          e.g. composing storeDatabase and storeLogging
--     2. a ~< c -> b ~< c -> (a :+: b) ~< c
--     3. b ~< d -> c ~< d -> a ~< (b :+: c) -> a ~< d
--
--   To get these operators in terms of algebraic abstractions, it seems we
--   probably need second-order Arrow/ArrowChoice for &&&, |||, +++, and
--   possibly *** (or maybe we only need Profunctor?).
--




-- TODO: Experiment with Inject for interpreter composition




-- Execution

-- TODO: DatabaseF ~> IO
-- TODO: LogF ~> IO
