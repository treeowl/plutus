{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term names.
module UntypedPlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , runDeBruijnT
    ,namedTermDeBruijnM,unNamedTermDeBruijnM,indexTermDeBruijnM,unIndexTermDeBruijnM) where

import           PlutusCore.DeBruijn.Internal

import           PlutusCore.Name
import           PlutusCore.Quote
import           UntypedPlutusCore.Core

import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Lens                 hiding (Index, index)

{- Note [Comparison with typed deBruijn conversion]
This module is just a boring port of the typed version.
-}

-- | Convert a 'Term' with 'Name's into a 'Term' with 'NamedDeBruijn's.
namedTermDeBruijnM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term Name uni fun ann
    -> m (Term NamedDeBruijn uni fun ann)
namedTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    LamAbs ann n t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> namedTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> namedTermDeBruijnM t1 <*> namedTermDeBruijnM t2
    Delay ann t -> Delay ann <$> namedTermDeBruijnM t
    Force ann t -> Force ann <$> namedTermDeBruijnM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann

unNamedTermDeBruijnM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedDeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unNamedTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName n
    -- binder cases
    LamAbs ann n t -> declareIndex n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs ann n' <$> unNamedTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unNamedTermDeBruijnM t1 <*> unNamedTermDeBruijnM t2
    Delay ann t -> Delay ann <$> unNamedTermDeBruijnM t
    Force ann t -> Force ann <$> unNamedTermDeBruijnM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann

-- | Convert a 'Term' with 'Name's into a 'Term' with just-index 'DeBruijn's.
indexTermDeBruijnM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term Name uni fun ann
    -> m (Term DeBruijn uni fun ann)
indexTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann . DeBruijn . view index <$> nameToDeBruijn n
    -- binder cases
    LamAbs ann n t -> declareUnique n $ do
        n' <- DeBruijn . view index <$> nameToDeBruijn n
        withScope $ LamAbs ann n' <$> indexTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> indexTermDeBruijnM t1 <*> indexTermDeBruijnM t2
    Delay ann t -> Delay ann <$> indexTermDeBruijnM t
    Force ann t -> Force ann <$> indexTermDeBruijnM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann

-- TODO: use fresh names instead of repeating fake names?
-- | Convert a 'Term' with just-index 'DeBruijn's into a 'Term' with 'Name's.
unIndexTermDeBruijnM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term DeBruijn uni fun ann
    -> m (Term Name uni fun ann)
unIndexTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName (fakeNameDeBruijn n)
    -- binder cases
    LamAbs ann n t -> declareIndex n $ do
        n' <- deBruijnToName $ fakeNameDeBruijn n
        withScope $ LamAbs ann n' <$> unIndexTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unIndexTermDeBruijnM t1 <*> unIndexTermDeBruijnM t2
    Delay ann t -> Delay ann <$> unIndexTermDeBruijnM t
    Force ann t -> Force ann <$> unIndexTermDeBruijnM t
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
    Error ann -> pure $ Error ann
