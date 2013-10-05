module TypeInfo where

open import Level using (suc)
open import Function using (id)
open import Reflection using (Name)

open import Data.List using (List)
open import Data.Product using (∃)

open import Utils

record TypeInfo {ℓ} (t : Set ℓ) : Set (suc (suc ℓ)) where
  constructor typeinfo
  field
    name : Name
    args : List (Heterogeneous (suc ℓ))
