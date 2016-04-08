{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, Trustworthy,
             TypeFamilies, UndecidableInstances #-}

module Control.Monad.Safe
    ( -- * SafeT
      SafeT
    , runSafeT

     -- * MonadSafe
    , ReleaseKey
    , MonadSafe(..)

      -- * Utilities
      -- $utilities
    , onException
    , finally
    , bracket
    , bracket_
    , bracketOnError

    -- * Re-exports
    -- $reexports
    , module Control.Monad.Catch
    , module Control.Exception
    ) where

import           Control.Applicative               (Alternative)
import           Control.Exception                 (Exception (..),
                                                    SomeException (..))
import           Control.Monad                     (MonadPlus)
import qualified Control.Monad.Base                as B
import           Control.Monad.Catch               (Exception (..),
                                                    Handler (..),
                                                    MonadCatch (..),
                                                    MonadMask (..),
                                                    MonadThrow (..),
                                                    SomeException, catchAll,
                                                    catchIOError, catchIf,
                                                    catchJust, catches, handle,
                                                    handleAll, handleIOError,
                                                    handleIf, handleJust, mask_,
                                                    try, tryJust,
                                                    uninterruptibleMask_)
import qualified Control.Monad.Catch               as C
import qualified Control.Monad.Catch.Pure          as E
import qualified Control.Monad.Cont.Class          as CC
import qualified Control.Monad.Error.Class         as EC
import           Control.Monad.IO.Class            (MonadIO (liftIO))
import qualified Control.Monad.State.Class         as SC
import           Control.Monad.Trans.Class         (MonadTrans (lift))
import           Control.Monad.Trans.Control       (MonadBaseControl (..))
import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.RWS.Lazy      as RWS
import qualified Control.Monad.Trans.RWS.Strict    as RWS'
import qualified Control.Monad.Trans.State.Lazy    as S
import qualified Control.Monad.Trans.State.Strict  as S'
import qualified Control.Monad.Trans.Writer.Lazy   as W
import qualified Control.Monad.Trans.Writer.Strict as W'
import qualified Control.Monad.Writer.Class        as WC
import           Data.IORef                        (IORef, atomicModifyIORef',
                                                    newIORef)
import qualified Data.Map                          as M

data Finalizers m = Finalizers
    { _nextKey    :: !Integer
    , _finalizers :: !(M.Map Integer (m ()))
    }

{-| 'SafeT' is a monad transformer that extends the base monad with the ability
    to 'register' and 'release' finalizers.

    All unreleased finalizers are called at the end of the 'SafeT' block, even
    in the event of exceptions.
-}
newtype SafeT m r = SafeT { unSafeT :: R.ReaderT (IORef (Maybe (Finalizers m))) m r }
    deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
              EC.MonadError e, SC.MonadState s, WC.MonadWriter w, CC.MonadCont,
              MonadThrow, MonadCatch, MonadMask, MonadIO, B.MonadBase b)

instance MonadTrans SafeT where
    lift m = SafeT (lift m)

instance MonadBaseControl b m => MonadBaseControl b (SafeT m) where
#if MIN_VERSION_monad_control(1,0,0)
     type StM (SafeT m) a = StM m a
     liftBaseWith f = SafeT $ R.ReaderT $ \reader' ->
         liftBaseWith $ \runInBase ->
             f $ runInBase . (\(SafeT r) -> R.runReaderT r reader'  )
     restoreM = SafeT . R.ReaderT . const . restoreM
#else
     newtype StM (SafeT m) a = StMT (StM m a)
     liftBaseWith f = SafeT $ R.ReaderT $ \reader' ->
         liftBaseWith $ \runInBase ->
             f $ liftM StMT . runInBase . \(SafeT r) -> R.runReaderT r reader'
     restoreM (StMT base) = SafeT $ R.ReaderT $ const $ restoreM base
#endif

{-| Run the 'SafeT' monad transformer, executing all unreleased finalizers at
    the end of the computation
-}
runSafeT :: (MonadMask m, MonadIO m) => SafeT m r -> m r
runSafeT m = C.bracket
    (liftIO $ newIORef $! Just $! Finalizers 0 M.empty)
    (\ioref -> do
        mres <- liftIO $ atomicModifyIORef' ioref $ \val ->
            (Nothing, val)
        case mres of
            Nothing -> error "runSafeT's resources were freed by another"
            Just (Finalizers _ fs) -> mapM snd (M.toDescList fs) )
    (R.runReaderT (unSafeT m))
{-# INLINABLE runSafeT #-}

-- | Token used to 'release' a previously 'register'ed finalizer
newtype ReleaseKey = ReleaseKey { unlock :: Integer }

{-| 'MonadSafe' lets you 'register' and 'release' finalizers that execute in a
    'Base' monad
-}
class (MonadCatch m, MonadMask m, MonadIO m, MonadIO (Base m)) => MonadSafe m where
    {-| The monad used to run resource management actions, corresponding to the
        monad directly beneath 'SafeT'
    -}
    type Base (m :: * -> *) :: * -> *

    -- | Lift an action from the 'Base' monad
    liftBase :: Base m r -> m r

    {-| 'register' a finalizer, ensuring that the finalizer gets called if the
        finalizer is not 'release'd before the end of the surrounding 'SafeT'
        block.
    -}
    register :: Base m () -> m ReleaseKey

    {-| 'release' a registered finalizer

        You can safely call 'release' more than once on the same 'ReleaseKey'.
        Every 'release' after the first one does nothing.
    -}
    release  :: ReleaseKey -> m ()

instance (MonadIO m, MonadCatch m, MonadMask m) => MonadSafe (SafeT m) where
    type Base (SafeT m) = m

    liftBase = lift

    register io = do
        ioref <- SafeT R.ask
        liftIO $ do
            n <- atomicModifyIORef' ioref $ \val ->
                case val of
                    Nothing -> error "register: SafeT block is closed"
                    Just (Finalizers n fs) ->
                        (Just $! Finalizers (n + 1) (M.insert n io fs), n)
            return (ReleaseKey n)

    release key = do
        ioref <- SafeT R.ask
        liftIO $ atomicModifyIORef' ioref $ \val ->
            case val of
                Nothing -> error "release: SafeT block is closed"
                Just (Finalizers n fs) ->
                    (Just $! Finalizers n (M.delete (unlock key) fs), ())

instance (MonadSafe m) => MonadSafe (I.IdentityT m) where
    type Base (I.IdentityT m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m) => MonadSafe (E.CatchT m) where
    type Base (E.CatchT m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m) => MonadSafe (R.ReaderT i m) where
    type Base (R.ReaderT i m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m) => MonadSafe (S.StateT s m) where
    type Base (S.StateT s m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m) => MonadSafe (S'.StateT s m) where
    type Base (S'.StateT s m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m, Monoid w) => MonadSafe (W.WriterT w m) where
    type Base (W.WriterT w m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m, Monoid w) => MonadSafe (W'.WriterT w m) where
    type Base (W'.WriterT w m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m, Monoid w) => MonadSafe (RWS.RWST i w s m) where
    type Base (RWS.RWST i w s m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

instance (MonadSafe m, Monoid w) => MonadSafe (RWS'.RWST i w s m) where
    type Base (RWS'.RWST i w s m) = Base m
    liftBase = lift . liftBase
    register = lift . register
    release  = lift . release

{-| Analogous to 'C.onException' from @Control.Monad.Catch@, except this also
    protects against premature termination

    @(\`onException\` io)@ is a monad morphism.
-}
onException :: (MonadSafe m) => m a -> Base m b -> m a
m1 `onException` io = do
    key <- register (io >> return ())
    r   <- m1
    release key
    return r
{-# INLINABLE onException #-}

{- $utilities
    These utilities let you supply a finalizer that runs in the 'Base' monad
    (i.e. the monad directly beneath 'SafeT').  If you don't need to use the
    full power of the 'Base' monad and you only need to use to use 'IO', then
    just wrap the finalizer in 'liftIO', like this:

> myAction `finally` (liftIO myFinalizer)

    This will lead to a simple inferred type with a single 'MonadSafe'
    constraint:

> (MonadSafe m) => ...

    For examples of this, see the utilities in "Pipes.Safe.Prelude".

    If you omit the 'liftIO', the compiler will infer the following constraint
    instead:

> (MonadSafe m, Base m ~ IO) => ...

    This means that this function would require 'IO' directly beneath the
    'SafeT' monad transformer, which might not be what you want.
-}

{-| Analogous to 'C.finally' from @Control.Monad.Catch@, except this also
    protects against premature termination
-}
finally :: (MonadSafe m) => m a -> Base m b -> m a
m1 `finally` after = bracket_ (return ()) after m1
{-# INLINABLE finally #-}

{-| Analogous to 'C.bracket' from @Control.Monad.Catch@, except this also
    protects against premature termination
-}
bracket :: (MonadSafe m) => Base m a -> (a -> Base m b) -> (a -> m c) -> m c
bracket before after action = mask $ \restore -> do
    h <- liftBase before
    r <- restore (action h) `onException` after h
    _ <- liftBase (after h)
    return r
{-# INLINABLE bracket #-}

{-| Analogous to 'C.bracket_' from @Control.Monad.Catch@, except this also
    protects against premature termination
-}
bracket_ :: (MonadSafe m) => Base m a -> Base m b -> m c -> m c
bracket_ before after action = bracket before (\_ -> after) (\_ -> action)
{-# INLINABLE bracket_ #-}

{-| Analogous to 'C.bracketOnError' from @Control.Monad.Catch@, except this also
    protects against premature termination
-}
bracketOnError
    :: (MonadSafe m) => Base m a -> (a -> Base m b) -> (a -> m c) -> m c
bracketOnError before after action = mask $ \restore -> do
    h <- liftBase before
    restore (action h) `onException` after h
{-# INLINABLE bracketOnError #-}

{- $reexports
    @Control.Monad.Catch@ re-exports all functions except for the ones that
    conflict with the generalized versions provided here (i.e. 'bracket',
    'finally', etc.).

    @Control.Exception@ re-exports 'Exception' and 'SomeException'.
-}
