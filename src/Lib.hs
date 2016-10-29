{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- "Free transformers" aka the onion architecture
--
-- adapted from a combination of:
-- - http://degoes.net/articles/modern-fp
-- - http://degoes.net/articles/modern-fp-part-2
-- - http://mpickering.github.io/posts/2014-12-20-closed-type-family-data-types.html
-- - https://gist.github.com/jdegoes/97459c0045f373f4eaf126998d8f65dc
--
-- In this example, we don't yet generalize over "computational context" (i.e.
-- sequential/Free or parallel/FreeAp) -- everything is sequential/Free.
--
module Lib where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Free
import           Data.Proxy
import           Prelude            hiding (log)




-- Coproducts, and prism/typeclass-based injection

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

type f ~> g = forall a. f a -> g a
infixr 4 ~>

inject :: forall f g. (f :<: g) => f ~> g
inject = review (inj resolution)
  where
    resolution :: Proxy (Elem f g)
    resolution = Proxy

-- TODO: probably add a function for `liftF . inject`




-- A simple algebra with a typeclass targeting Free

newtype MessageId = MessageId Int deriving (Show)
newtype Message = Message String deriving (Show)

class Functor f => Store f where
  getMessage :: MessageId -> Free f Message
  putMessage :: Message -> Free f Message

-- CPS transform of Store (if it targeted `f Message`), to get a base functor:
data StoreF a
  = GetMessage MessageId (Message -> a)
  | PutMessage Message (Message -> a)
  deriving (Functor)

instance (StoreF :<: f) => Store f where
  getMessage mId = liftF $ inject $ GetMessage mId id
  putMessage m = liftF $ inject $ PutMessage m id

getThenPut :: (StoreF :<: f)
           => MessageId
           -> Free f Message
getThenPut messageId = do
  msg <- getMessage messageId
  -- ... modify msg ...
  putMessage msg




-- -- Alternative algebra: a more generic typeclass targeting any functor
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
-- composite interpreter. See below for an example of this.
storeAndLog :: (StoreF :<: f, LogF :<: f)
            => MessageId
            -> Free f Message
storeAndLog mId = do
  log "getting a message"
  getMessage mId




-- A database algebra

type Row = (Int, String)
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

type f ~< g = f ~> Free g
infixr 4 ~<

storeDatabase :: StoreF ~< DatabaseF
storeDatabase (GetMessage mId next) = next . mkMessage <$> query (sql mId)
  where
    sql :: MessageId -> Sql
    sql (MessageId mid) = "select * from messages where id = " ++ show mid

    mkMessage :: Row -> Message
    mkMessage (_id, body) = Message body

storeDatabase (PutMessage m next) = next m <$ execute (sql m)
  where
    sql :: Message -> Sql -- insecure demo code:
    sql (Message body) = "insert into messages values (" ++ show body ++ ")"




-- Interpretation solely for effects

data Halt f a
  = Effect (f ())
  | Noop
  deriving (Functor)

eff :: Functor f => Free f () -> Free (Halt f) a
eff (Pure ()) = Free Noop
eff (Free as) = Free $ Effect $ void as

storeLogging :: StoreF ~< Halt LogF
storeLogging (GetMessage _mId _next) = eff $ log "getting message"
storeLogging (PutMessage _m _next)   = eff $ return ()

databaseLogging :: DatabaseF ~< Halt LogF
databaseLogging (Query _ _)   = eff $ log "querying"
databaseLogging (Execute _ _) = eff $ log "issuing execute"




-- Translation to IO

execDatabase :: DatabaseF ~> IO
execDatabase (Query sql next) = next <$> queryDb sql
  where
    queryDb :: Sql -> IO Row
    queryDb _ = return (1, "data")
execDatabase (Execute sql next) = next <$ execDb sql
  where
    execDb :: Sql -> IO ()
    execDb _ = return ()

execLogging :: LogF ~> IO
execLogging (Log str next) = next <$ putStrLn str




-- Interpreter composition

unhalt :: Functor f => Free (Halt f) a -> Free f ()
unhalt (Pure _)               = return ()
unhalt (Free Noop)            = return ()
unhalt (Free (Effect action)) = liftF action

beforeEffect :: (Functor g, Functor e)
             => f ~< g
             -> f ~< Halt e
             -> f ~< (g :+: e)
(elaborate `beforeEffect` toEff) fa = do
  a <- hoistFree InL $ elaborate fa
  hoistFree InR $ unhalt $ toEff fa
  return a

afterEffect :: (Functor g, Functor e)
            => f ~< g
            -> f ~< Halt e
            -> f ~< (e :+: g)
(elaborate `afterEffect` toEff) fx = do
  hoistFree InL $ unhalt $ toEff fx
  hoistFree InR $ elaborate fx

-- TODO: add betweenEffects? e.g. for logging before and after an instruction

weave :: (Functor g, Functor h)
      => f ~< g
      -> f ~< h
      -> f ~< (g :+: h)
weave int1 int2 fx = do
  _ <- hoistFree InL $ int1 fx
  hoistFree InR $ int2 fx

(~<+) :: (Functor g, Functor h)
      => f ~< g
      -> f ~< h
      -> f ~< (g :+: h)
int1 ~<+ int2 = weave int1 int2

infixl 3 ~<+

-- Converts an interpreter to accept a program instead of an instruction.
acceptProgram :: Monad g
              => f ~> g
              -> Free f ~> g
acceptProgram = foldFree

-- "Horizontal" interpreter composition
hCompose :: (Monad h)
         => g ~> h
         -> f ~< g
         -> f ~> h
int2 `hCompose` int1 = acceptProgram int2 . int1

(~<>) :: (Monad h)
      => f ~< g
      -> g ~> h
      -> f ~> h
int1 ~<> int2 = int2 `hCompose` int1

infixl 2 ~<>

hComposeEffect :: (Functor g, Monad h)
      => g ~> h
      -> f ~< Halt g
      -> f a
      -> h ()
int2 `hComposeEffect` int1 = acceptProgram int2 . unhalt . int1

(~<!>) :: (Functor g, Monad h)
       => f ~< Halt g
       -> g ~> h
       -> f a
       -> h ()
int1 ~<!> int2 = int2 `hComposeEffect` int1

infixl 2 ~<!>

mergeInterpreters :: a ~> c
                  -> b ~> c
                  -> (a :+: b) ~> c
mergeInterpreters int1 int2 = \case
  InL ax -> int1 ax
  InR bx -> int2 bx

(+~<) :: a ~> c
      -> b ~> c
      -> (a :+: b) ~> c
(+~<) = mergeInterpreters

infixl 3 +~<

-- possibly: b ~> d -> c ~> d -> a ~< (b :+: c) -> a ~> d

-- TODO: "Vertical" interpreter composition
-- vCompose :: a ~< b -> a ~< c -> a ~< Product b c
-- vCompose = _todoVert

-- TODO: Monoidal composition
--   "Interpreters compose monoidally as per the operations supported by
-- T[_[_], _]. For example, if T supports a notion of failure, then two T[F, A]
-- operations can be appended together, such that the first computation is used
-- if it succeeds, otherwise the second. Racing is another example of monoidal
-- composition possible with parallel computations."

execOnlyLogging :: StoreF a -> IO ()
execOnlyLogging = storeDatabase ~<> databaseLogging ~<!> execLogging

execStore :: StoreF ~> IO
execStore = (storeDatabase `afterEffect` storeLogging)
        ~<> ((+~<) execLogging execDatabase)

main :: IO ()
main = void . acceptProgram execStore $ program
  where
    program = getThenPut $ MessageId 1




-- Representing interpreter composition in terms of higher algebraic abstractions

class Category1 (cat1 :: (* -> *) -> (* -> *) -> *) where
  id1 :: forall f. (Functor f) => cat1 f f

  compose1 :: forall f g h. (Functor f, Functor g, Functor h)
           => cat1 g h -> cat1 f g -> cat1 f h

newtype Interpreter f g = Interpreter { unInterpreter :: f ~< g }

instance Category1 Interpreter where
  id1 = Interpreter liftF

  (Interpreter cgh) `compose1` (Interpreter cfg) =
    Interpreter $ cfg ~<> cgh

-- TODO: Arrow1/ArrowChoice1 for operators like &&&, |||, +++, ***
--       Also, how does Profunctor fit in, if at all?




-- TODO: Using Codensity/CPS to increase efficiency
