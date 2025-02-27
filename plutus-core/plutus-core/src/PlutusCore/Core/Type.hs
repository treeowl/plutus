{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE DerivingVia              #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE UndecidableInstances     #-}

module PlutusCore.Core.Type
    ( Kind (..)
    , Type (..)
    , Term (..)
    , Version (..)
    , Program (..)
    , UniOf
    , Normalized (..)
    , TyVarDecl (..)
    , VarDecl (..)
    , TyDecl (..)
    , tyDeclVar
    , HasUniques
    , Binder (..)
    , defaultVersion
    -- * Helper functions
    , toTerm
    , termAnn
    , typeAnn
    , mapFun
    , tyVarDeclAnn
    , tyVarDeclName
    , tyVarDeclKind
    , varDeclAnn
    , varDeclName
    , varDeclType
    , tyDeclAnn
    , tyDeclType
    , tyDeclKind
    )
where

import           PlutusPrelude

import           PlutusCore.Name

import           Control.Lens
import           Data.Hashable
import qualified Data.Kind                as GHC
import           Instances.TH.Lift        ()
import           Language.Haskell.TH.Lift
import           Universe

{- Note [Annotations and equality]
Equality of two things does not depend on their annotations.
So don't use @deriving Eq@ for things with annotations.
-}

data Kind ann
    = Type ann
    | KindArrow ann (Kind ann) (Kind ann)
    deriving (Show, Functor, Generic, NFData, Lift, Hashable)

-- | A 'Type' assigned to expressions.
type Type :: GHC.Type -> (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type
data Type tyname uni ann
    = TyVar ann tyname
    | TyFun ann (Type tyname uni ann) (Type tyname uni ann)
    | TyIFix ann (Type tyname uni ann) (Type tyname uni ann)
      -- ^ Fix-point type, for constructing self-recursive types
    | TyForall ann tyname (Kind ann) (Type tyname uni ann)
    | TyBuiltin ann (SomeTypeIn uni) -- ^ Builtin type
    | TyLam ann tyname (Kind ann) (Type tyname uni ann)
    | TyApp ann (Type tyname uni ann) (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

data Term tyname name uni fun ann
    = Var ann name -- ^ a named variable
    | TyAbs ann tyname (Kind ann) (Term tyname name uni fun ann)
    | LamAbs ann name (Type tyname uni ann) (Term tyname name uni fun ann)
    | Apply ann (Term tyname name uni fun ann) (Term tyname name uni fun ann)
    | Constant ann (Some (ValueOf uni)) -- ^ a constant term
    | Builtin ann fun
    | TyInst ann (Term tyname name uni fun ann) (Type tyname uni ann)
    | Unwrap ann (Term tyname name uni fun ann)
    | IWrap ann (Type tyname uni ann) (Type tyname uni ann) (Term tyname name uni fun ann)
    | Error ann (Type tyname uni ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Version of Plutus Core to be used for the program.
data Version ann
    = Version ann Natural Natural Natural
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program tyname name uni fun ann = Program ann (Version ann) (Term tyname name uni fun ann)
    deriving (Show, Functor, Generic, NFData, Hashable)

-- | Extract the universe from a type.
type family UniOf a :: GHC.Type -> GHC.Type

type instance UniOf (Term tyname name uni fun ann) = uni

-- | A "type variable declaration", i.e. a name and a kind for a type variable.
data TyVarDecl tyname ann = TyVarDecl
    { _tyVarDeclAnn  :: ann
    , _tyVarDeclName :: tyname
    , _tyVarDeclKind :: Kind ann
    } deriving (Functor, Show, Generic)
makeLenses ''TyVarDecl

-- | A "variable declaration", i.e. a name and a type for a variable.
data VarDecl tyname name uni fun ann = VarDecl
    { _varDeclAnn  :: ann
    , _varDeclName :: name
    , _varDeclType :: Type tyname uni ann
    } deriving (Functor, Show, Generic)
makeLenses ''VarDecl

-- | A "type declaration", i.e. a kind for a type.
data TyDecl tyname uni ann = TyDecl
    { _tyDeclAnn  :: ann
    , _tyDeclType :: Type tyname uni ann
    , _tyDeclKind :: Kind ann
    } deriving (Functor, Show, Generic)
makeLenses ''TyDecl

tyDeclVar :: TyVarDecl tyname ann -> TyDecl tyname uni ann
tyDeclVar (TyVarDecl ann name kind) = TyDecl ann (TyVar ann name) kind

instance HasUnique tyname TypeUnique => HasUnique (TyVarDecl tyname ann) TypeUnique where
    unique f (TyVarDecl ann tyname kind) =
        unique f tyname <&> \tyname' -> TyVarDecl ann tyname' kind

instance HasUnique name TermUnique => HasUnique (VarDecl tyname name uni fun ann) TermUnique where
    unique f (VarDecl ann name ty) =
        unique f name <&> \name' -> VarDecl ann name' ty

newtype Normalized a = Normalized
    { unNormalized :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
      deriving newtype (NFData, Pretty, PrettyBy config)
      deriving Applicative via Identity

-- | All kinds of uniques an entity contains.
type family HasUniques a :: GHC.Constraint
type instance HasUniques (Kind ann) = ()
type instance HasUniques (Type tyname uni ann) = HasUnique tyname TypeUnique
type instance HasUniques (Term tyname name uni fun ann) =
    (HasUnique tyname TypeUnique, HasUnique name TermUnique)
type instance HasUniques (Program tyname name uni fun ann) =
    HasUniques (Term tyname name uni fun ann)

-- | The default version of Plutus Core supported by this library.
defaultVersion :: ann -> Version ann
defaultVersion ann = Version ann 1 0 0

toTerm :: Program tyname name uni fun ann -> Term tyname name uni fun ann
toTerm (Program _ _ term) = term

typeAnn :: Type tyname uni ann -> ann
typeAnn (TyVar ann _       ) = ann
typeAnn (TyFun ann _ _     ) = ann
typeAnn (TyIFix ann _ _    ) = ann
typeAnn (TyForall ann _ _ _) = ann
typeAnn (TyBuiltin ann _   ) = ann
typeAnn (TyLam ann _ _ _   ) = ann
typeAnn (TyApp ann _ _     ) = ann

termAnn :: Term tyname name uni fun ann -> ann
termAnn (Var ann _       ) = ann
termAnn (TyAbs ann _ _ _ ) = ann
termAnn (Apply ann _ _   ) = ann
termAnn (Constant ann _  ) = ann
termAnn (Builtin  ann _  ) = ann
termAnn (TyInst ann _ _  ) = ann
termAnn (Unwrap ann _    ) = ann
termAnn (IWrap ann _ _ _ ) = ann
termAnn (Error ann _     ) = ann
termAnn (LamAbs ann _ _ _) = ann

-- | Map a function over the set of built-in functions.
mapFun :: (fun -> fun') -> Term tyname name uni fun ann -> Term tyname name uni fun' ann
mapFun f = go where
    go (LamAbs ann name ty body)  = LamAbs ann name ty (go body)
    go (TyAbs ann name kind body) = TyAbs ann name kind (go body)
    go (IWrap ann pat arg term)   = IWrap ann pat arg (go term)
    go (Apply ann fun arg)        = Apply ann (go fun) (go arg)
    go (Unwrap ann term)          = Unwrap ann (go term)
    go (Error ann ty)             = Error ann ty
    go (TyInst ann term ty)       = TyInst ann (go term) ty
    go (Var ann name)             = Var ann name
    go (Constant ann con)         = Constant ann con
    go (Builtin ann fun)          = Builtin ann (f fun)

-- | This is a wrapper to mark the place where the binder is introduced (i.e. LamAbs/TyAbs)
-- and not where it is actually used (TyVar/Var..).
-- This marking allows us to skip the (de)serialization of binders at LamAbs/TyAbs positions
-- iff 'name' is DeBruijn-encoded (level or index). See for example the instance of  'UntypedPlutusCore.Core.Instance.Flat'
newtype Binder name = Binder { unBinder :: name }
