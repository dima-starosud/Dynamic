module TypeInfo where

open import Level using (suc)
open import Function using (id)
open import Reflection using (Name)

open import Data.List using (List)
open import Data.Product using (∃)

Heterogeneous : ∀ {ℓ} → Set (suc ℓ)
Heterogeneous = ∃ id

record TypeInfo {ℓ} (t : Set ℓ) : Set (suc (suc ℓ)) where
  constructor typeinfo
  field
    name : Name
    args : List (Heterogeneous {suc ℓ})
