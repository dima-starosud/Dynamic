module Utils where

open import Level using (suc)
open import Function using (id)
open import Data.Product using (Σ)
open import Category.Monad.Indexed

open RawIMonadPlus {{...}} public

Heterogeneous : ∀ ℓ → Set (suc ℓ)
Heterogeneous ℓ = Σ (Set ℓ) id
