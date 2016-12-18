{-# LANGUAGE FunctionalDependencies #-}
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
-- {-# LANGUAGE TypeFamilyDependencies #-}

module FreeTransformers where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.Free.Church
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

-- type f ~< g = f ~> Free g
-- infixr 4 ~<

-- Creates a Free program from the provided injectable instruction
-- instruction :: (f :<: g) => f ~< g
-- instruction = liftF . inject

instruction :: (f :<: g, MonadFree g m) => f ~> m
instruction = liftF . inject



-- A simple algebra with a typeclass targeting Free

newtype MessageId = MessageId Int deriving (Show)
newtype Message = Message String deriving (Show)

-- class Functor f => Store f where
--   getMessage :: MessageId -> Free f Message
--   putMessage :: Message -> Free f Message

class MonadFree f m => Store f m | m -> f where
  getMessage :: MessageId -> m Message
  putMessage :: Message -> m Message

-- CPS transform of Store (if it targeted `f Message`), to get a base functor:
data StoreF a
  = GetMessage MessageId (Message -> a)
  | PutMessage Message (Message -> a)
  deriving (Functor)

-- instance (StoreF :<: f) => Store f where
--   getMessage mId = instruction $ GetMessage mId id
--   putMessage msg = instruction $ PutMessage msg id

instance (StoreF :<: f, MonadFree f m) => Store f m where
  getMessage mId = instruction $ GetMessage mId id
  putMessage msg = instruction $ PutMessage msg id

-- getThenPut :: (Store f)
--            => MessageId
--            -> Free f Message
-- getThenPut messageId = do
--   msg <- getMessage messageId
--   -- ... modify msg ...
--   putMessage msg

getThenPut :: (Store f m)
           => MessageId
           -> m Message
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
--   getMessage mId = instruction (getMessage mId :: StoreF Message)
--   putMessage m = instruction (putMessage m :: StoreF Message)
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

-- class Functor f => Logging f where
--   log :: String -> Free f ()

class MonadFree f m => Logging f m where
  log :: String -> m ()

-- instance (LogF :<: f) => Logging f where
--   log msg = instruction $ Log msg ()

instance (LogF :<: f, MonadFree f m) => Logging f m where
  log msg = instruction $ Log msg ()

-- A program which both gets a message and does some logging side-by-side. This
-- is not as modular as we could be, by adding a Store-to-Logging interpreter,
-- composing that with a Store-to-lower-level interpreter, and using this
-- composite interpreter. See below for an example of this.
-- storeAndLog :: (Store f, Logging f)
--             => MessageId
--             -> Free f Message
-- storeAndLog mId = do
--   log "getting a message"
--   getMessage mId

storeAndLog :: (Store f m, Logging f m)
            => MessageId
            -> m Message
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

class MonadFree f m => Database f m where
  query :: Sql -> m Row
  execute :: Sql -> m ()

instance (DatabaseF :<: f, MonadFree f m) => Database f m where
  query sql = instruction $ Query sql id
  execute sql = instruction $ Execute sql ()




-- Interpretation

storeDatabase :: MonadFree DatabaseF m => StoreF ~> m
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

-- eff :: Functor f => Free f () -> Free (Halt f) a
-- eff (Pure ()) = Free Noop
-- eff (Free as) = Free $ Effect $ void as
-- 
-- storeLogging :: StoreF ~> Free (Halt LogF)
-- storeLogging (GetMessage _mId _next) = eff $ log "getting message"
-- storeLogging (PutMessage _m _next)   = eff $ return ()

-- -- TODO: move this and effF into sep modules
-- effFree :: Functor f => Free f () -> Free (Halt f) a
-- effFree (Pure ()) = wrap Noop
-- effFree (Free as) = wrap $ Effect $ void as
-- 
-- -- TODO: move this and effFree into sep modules
-- effF :: Functor f => F f () -> F (Halt f) a
-- effF = toF . effFree . fromF -- TODO: make this more efficient!

-- -- Approach A (joel: this might require yoneda here?)
--
-- class Programmable (free :: (* -> *) -> * -> *) where
--   eff :: Functor f => free f () -> free (Halt f) a

-- instance Programmable Free where
--   eff (Pure ()) = wrap Noop
--   eff (Free as) = wrap $ Effect $ void as

-- instance Programmable F where
--   eff = toF . effFree . fromF -- TODO: make this more efficient!

-- -- Approach B (This is going to require an injective type family?)
-- class MonadFree f m => Program f m | m -> f where
--   type Substrate m :: (* -> *) -> * -> *
--   eff :: (Substrate m) f () -> (Substrate m) (Halt f) a
-- 
-- instance Functor f => Program f (Free f) where
--   type Substrate (Free f) = Free
-- 
--   eff (Pure ()) = wrap Noop
--   eff (Free as) = wrap $ Effect $ void as
-- 
-- instance Functor f => Program f (F f) where
--   type Substrate (F f) = F
-- 
--   eff = toF . effFree . fromF -- TODO: make this more efficient!

foo :: (LogF :<: f, MonadFree f m, Functor f) => m ()
foo = log "getting message"

-- Approach C
--
-- TODO: we might be able to take `m` out of the parameters by using an equality constraint?
-- class MonadFree f m => Program free f m | m -> f, m -> free, free f -> m where
--   eff :: free f () -> free (Halt f) a
--
-- instance Functor f => Program Free f (Free f) where
--   eff (Pure ()) = wrap Noop
--   eff (Free as) = wrap $ Effect $ void as
--
-- instance Functor f => Program F f (F f) where
--   eff = toF . effFree . fromF -- TODO: make this more efficient!
--
-- storeLoggingC :: Program free LogF (free LogF) => StoreF ~> free (Halt LogF)
-- storeLoggingC (GetMessage _mId _next) = eff $ foo
-- storeLoggingC (PutMessage _m _next)   = eff $ return ()


--
-- TODO try adding (Functor f, Monad (free f)) to get rid of Monad constraint on beforeEffect.
--

class (Functor f, MonadFree f (free f)) => Program free f where
  -- Halt
  eff    :: free f () -> free (Halt f) a
  unhalt :: free (Halt f) a -> free f ()
  -- Generalized free operations
  hoist  :: Functor g => (f ~> g) -> (free f ~> free g)
  foldProgram :: Monad m => (f ~> m) -> (free f ~> m)

instance Functor f => Program Free f where
  eff (Pure ()) = wrap Noop
  eff (Free as) = wrap $ Effect $ void as

  unhalt (Pure _)               = return ()
  unhalt (Free Noop)            = return ()
  unhalt (Free (Effect action)) = liftF action

  hoist = hoistFree
  foldProgram = foldFree

instance Functor f => Program F f where
  eff = toF . eff . fromF -- TODO: make this more efficient!

  unhalt = toF . unhalt . fromF -- TODO: make this more efficient!

  hoist = hoistF
  foldProgram = foldF

storeLogging :: Program free LogF => StoreF ~> free (Halt LogF)
storeLogging (GetMessage _mId _next) = eff $ log "getting message"
storeLogging (PutMessage _m _next)   = eff $ return ()

databaseLogging :: Program free LogF => DatabaseF ~> free (Halt LogF)
databaseLogging (Query _ _)   = eff $ log "querying"
databaseLogging (Execute _ _) = eff $ log "issuing execute"

-- storeLogging :: StoreF ~> F (Halt LogF)
-- storeLogging (GetMessage _mId _next) = effF $ log "getting message"
-- storeLogging (PutMessage _m _next)   = effF $ return ()
--
-- databaseLogging :: DatabaseF ~> F (Halt LogF)
-- databaseLogging (Query _ _)   = effF $ log "querying"
-- databaseLogging (Execute _ _) = effF $ log "issuing execute"





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

-- -- TODO: move this into sep module
-- unhaltFree :: Functor f => Free (Halt f) a -> Free f ()
-- unhaltFree (Pure _)               = return ()
-- unhaltFree (Free Noop)            = return ()
-- unhaltFree (Free (Effect action)) = liftF action
-- 
-- -- TODO: move this into sep module
-- unhaltF :: Functor f => F (Halt f) a -> F f ()
-- unhaltF = toF . unhaltFree . fromF -- TODO: make this more efficient!

-- TODO: move this into sep module
beforeEffect :: ( Program free g, Program free e, Monad (free (g :+: e)))
             => f ~> free g
             -> f ~> free (Halt e)
             -> f ~> free (g :+: e)
(elaborate `beforeEffect` toEff) fa = do
  a <- hoist InL $ elaborate fa
  hoist InR $ unhalt $ toEff fa
  return a

-- -- TODO: move this into sep module
-- beforeEffectF :: Functor e
--               => f ~> F g
--               -> f ~> F (Halt e)
--               -> f ~> F (g :+: e)
-- (elaborate `beforeEffectF` toEff) fa = do
--   a <- hoistF InL $ elaborate fa
--   hoistF InR $ unhalt $ toEff fa
--   return a

afterEffect :: (Program free g, Program free e, Monad (free (e :+: g)))
            => f ~> free g
            -> f ~> free (Halt e)
            -> f ~> free (e :+: g)
(elaborate `afterEffect` toEff) fx = do
  hoist InL $ unhalt $ toEff fx
  hoist InR $ elaborate fx

-- afterEffect monomorphized to Free:
afterEffectFree :: (Functor g, Functor e)
                => f ~> Free g
                -> f ~> Free (Halt e)
                -> f ~> Free (e :+: g)
afterEffectFree = afterEffect

-- TODO: add betweenEffects? e.g. for logging before and after an instruction

weave :: (Program free g, Program free h, Monad (free (g :+: h)))
      => f ~> free g
      -> f ~> free h
      -> f ~> free (g :+: h)
weave int1 int2 fx = do
  _ <- hoist InL $ int1 fx
  hoist InR $ int2 fx


(~<+) :: (Program free g, Program free h, Monad (free (g :+: h)))
      => f ~> free g
      -> f ~> free h
      -> f ~> free (g :+: h)
int1 ~<+ int2 = weave int1 int2

infixl 3 ~<+


-- Converts an interpreter to accept a program instead of an instruction.
acceptProgram :: (Monad g, Program free f)
              => f ~> g
              -> free f ~> g
acceptProgram = foldProgram

-- "Horizontal" interpreter composition
hCompose :: (Monad h, Program free g)
         => g ~> h
         -> f ~> free g
         -> f ~> h
int2 `hCompose` int1 = acceptProgram int2 . int1

(~<>) :: (Monad h, Program free g)
      => f ~> free g
      -> g ~> h
      -> f ~> h
int1 ~<> int2 = int2 `hCompose` int1

infixl 2 ~<>

-- hCompose monomorphized to Free:
hComposeFree :: (Functor g, Monad h)
             => g ~> h
             -> f ~> Free g
             -> f ~> h
hComposeFree = hCompose

hComposeEffect :: (Program free g, Monad h)
      => g ~> h
      -> f ~> free (Halt g)
      -> f a
      -> h ()
int2 `hComposeEffect` int1 = acceptProgram int2 . unhalt . int1

(~<!>) :: (Program free g, Monad h)
       => f ~> free (Halt g)
       -> g ~> h
       -> f a
       -> h ()
int1 ~<!> int2 = int2 `hComposeEffect` int1

infixl 2 ~<!>

-- hComposeEffect monomorphized to Free:
hComposeEffectFree :: (Functor g, Monad h)
      => g ~> h
      -> f ~> Free (Halt g)
      -> f a
      -> h ()
hComposeEffectFree = hComposeEffect

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
execOnlyLogging = storeDatabase' ~<> databaseLogging' ~<!> execLogging
  --
  -- TODO: we can do better than this. need concretized versions of combinators
  --       for Free vs F, and change import to swap impl.
  --
  where
    storeDatabase' :: StoreF ~> Free DatabaseF
    storeDatabase' = storeDatabase

    databaseLogging' :: DatabaseF ~> Free (Halt LogF)
    databaseLogging' = databaseLogging

execStore :: StoreF ~> IO
execStore = (storeDatabase' `afterEffect` storeLogging)
        ~<> ((+~<) execLogging execDatabase)
  where
    storeDatabase' :: StoreF ~> Free DatabaseF
    storeDatabase' = storeDatabase

main :: IO ()
main = void . acceptProgram execStore $ program
  where
    acceptProgram = foldFree
    program = getThenPut $ MessageId 1



{-
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
-}
