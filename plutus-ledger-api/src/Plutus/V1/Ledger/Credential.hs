{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

{-

Address and staking address credentials for outputs.

-}
module Plutus.V1.Ledger.Credential(
    StakingCredential(..)
    , Credential(..)
    ) where

import           Codec.Serialise.Class    (Serialise)
import           Control.DeepSeq          (NFData)
import           Data.Aeson               (FromJSON, ToJSON)
import           Data.Hashable            (Hashable)
import           GHC.Generics             (Generic)
import           Plutus.V1.Ledger.Crypto  (PubKeyHash)
import           Plutus.V1.Ledger.Scripts (ValidatorHash)
import qualified PlutusTx                 as PlutusTx
import qualified PlutusTx.Bool            as PlutusTx
import qualified PlutusTx.Eq              as PlutusTx
import           Prettyprinter            (Pretty (..), (<+>))

-- | Staking credential used to assign rewards
data StakingCredential
    = StakingHash Credential
    | StakingPtr Integer Integer Integer -- NB: The fields should really be Word64 / Natural / Natural, but 'Integer' is our only integral type so we need to use it instead.
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, Serialise, Hashable, NFData)

instance Pretty StakingCredential where
    pretty (StakingHash h)    = "StakingHash" <+> pretty h
    pretty (StakingPtr a b c) = "StakingPtr:" <+> pretty a <+> pretty b <+> pretty c

instance PlutusTx.Eq StakingCredential where
    {-# INLINABLE (==) #-}
    StakingHash l == StakingHash r = l PlutusTx.== r
    StakingPtr a b c == StakingPtr a' b' c' =
        a PlutusTx.== a'
        PlutusTx.&& b PlutusTx.== b'
        PlutusTx.&& c PlutusTx.== c'
    _ == _ = False

-- | Credential required to unlock a transaction output
data Credential
  = PubKeyCredential PubKeyHash -- ^ The transaction that spends this output must be signed by the private key
  | ScriptCredential ValidatorHash -- ^ The transaction that spends this output must include the validator script and be accepted by the validator.
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, Serialise, Hashable, NFData)

instance Pretty Credential where
    pretty (PubKeyCredential pkh) = "PubKeyCredential:" <+> pretty pkh
    pretty (ScriptCredential val) = "ScriptCredential:" <+> pretty val

instance PlutusTx.Eq Credential where
    {-# INLINABLE (==) #-}
    PubKeyCredential l == PubKeyCredential r  = l PlutusTx.== r
    ScriptCredential a == ScriptCredential a' = a PlutusTx.== a'
    _ == _                                    = False

PlutusTx.makeIsDataIndexed ''StakingCredential [('StakingHash,0), ('StakingPtr,1)]
PlutusTx.makeIsDataIndexed ''Credential [('PubKeyCredential,0), ('ScriptCredential,1)]
PlutusTx.makeLift ''StakingCredential
PlutusTx.makeLift ''Credential
