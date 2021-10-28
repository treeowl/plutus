{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module PlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , TyDeBruijn (..)
    , NamedTyDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , runDeBruijnT
    ,namedTyDeBruijnM,namedTermDeBruijnM,unNamedTyDeBruijnM,unNamedTermDeBruijnM) where

import           PlutusCore.DeBruijn.Internal

import           PlutusCore.Core
import           PlutusCore.Name
import           PlutusCore.Quote

import           Control.Monad.Except
import           Control.Monad.Reader

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}
-- | Convert a 'Type' with 'TyName's into a 'Type' with 'NamedTyDeBruijn's.
namedTyDeBruijnM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Type TyName uni ann
    -> m (Type NamedTyDeBruijn uni ann)
namedTyDeBruijnM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> tyNameToDeBruijn n
    -- binder cases
    TyForall ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyForall ann tn' k <$> namedTyDeBruijnM ty
    TyLam ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyLam ann tn' k <$> namedTyDeBruijnM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> namedTyDeBruijnM i <*> namedTyDeBruijnM o
    TyApp ann fun arg -> TyApp ann <$> namedTyDeBruijnM fun <*> namedTyDeBruijnM arg
    TyIFix ann pat arg -> TyIFix ann <$> namedTyDeBruijnM pat <*> namedTyDeBruijnM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's.
namedTermDeBruijnM
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Term TyName Name uni fun ann
    -> m (Term NamedTyDeBruijn NamedDeBruijn uni fun ann)
namedTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    TyAbs ann tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyAbs ann tn' k <$> namedTermDeBruijnM t
    LamAbs ann n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> namedTyDeBruijnM ty <*> namedTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> namedTermDeBruijnM t1 <*> namedTermDeBruijnM t2
    TyInst ann t ty -> TyInst ann <$> namedTermDeBruijnM t <*> namedTyDeBruijnM ty
    Unwrap ann t -> Unwrap ann <$> namedTermDeBruijnM t
    IWrap ann pat arg t -> IWrap ann <$> namedTyDeBruijnM pat <*> namedTyDeBruijnM arg <*> namedTermDeBruijnM t
    Error ann ty -> Error ann <$> namedTyDeBruijnM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn

-- | Convert a 'Type' with 'NamedTyDeBruijn's into a 'Type' with 'TyName's.
unNamedTyDeBruijnM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Type NamedTyDeBruijn uni ann
    -> m (Type TyName uni ann)
unNamedTyDeBruijnM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> deBruijnToTyName n
    -- binder cases
    TyForall ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyForall ann tn' k <$> unNamedTyDeBruijnM ty
    TyLam ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyLam ann tn' k <$> unNamedTyDeBruijnM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> unNamedTyDeBruijnM i <*> unNamedTyDeBruijnM o
    TyApp ann fun arg -> TyApp ann <$> unNamedTyDeBruijnM fun <*> unNamedTyDeBruijnM arg
    TyIFix ann pat arg -> TyIFix ann <$> unNamedTyDeBruijnM pat <*> unNamedTyDeBruijnM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

-- | Convert a 'Term' with 'NamedTyDeBruijn's and 'NamedDeBruijn's into a 'Term' with 'TyName's and 'Name's.
unNamedTermDeBruijnM
    :: (MonadReader Levels m, MonadQuote m, AsFreeVariableError e, MonadError e m)
    => Term NamedTyDeBruijn NamedDeBruijn uni fun ann
    -> m (Term TyName Name uni fun ann)
unNamedTermDeBruijnM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName n
    -- binder cases
    TyAbs ann tn k t -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyAbs ann tn' k <$> unNamedTermDeBruijnM t
    LamAbs ann n ty t -> declareIndex n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs ann n' <$> unNamedTyDeBruijnM ty <*> unNamedTermDeBruijnM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unNamedTermDeBruijnM t1 <*> unNamedTermDeBruijnM t2
    TyInst ann t ty -> TyInst ann <$> unNamedTermDeBruijnM t <*> unNamedTyDeBruijnM ty
    Unwrap ann t -> Unwrap ann <$> unNamedTermDeBruijnM t
    IWrap ann pat arg t -> IWrap ann <$> unNamedTyDeBruijnM pat <*> unNamedTyDeBruijnM arg <*> unNamedTermDeBruijnM t
    Error ann ty -> Error ann <$> unNamedTyDeBruijnM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
