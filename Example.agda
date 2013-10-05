
module Example where

open import Data.Nat
open import Data.Maybe
open import Data.List

open import Dynamic

record ListT (m : Set → Set) (a : Set) : Set where
  constructor listT

TYPES = ℕ ::: Maybe ::: ListT ::: []

