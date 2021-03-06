
module Example where

open import Function using (id; _$_; _∘_; _∋_)

open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String)
open import Data.Maybe using (maybe′)
open import Data.List using (sum; downFrom; [_])
open import Data.Product using (_,_; ,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Dynamic

CTX = String ::: List ::: List ℕ ::: []

ti-nat : Instance (TypeInfo ℕ)
ti-nat = value (typeinfo (quote ℕ) [])

ti-string : Instance (TypeInfo String)
ti-string = value (typeinfo (quote String) [])

ti-list : {a : Set} → Instance (TypeInfo (List a))
ti-list {a} = value (typeinfo (quote List) [ _ , a ])

go : Dynamic CTX → String
go dyn = maybe′ id fallback
         (showℕ ∘ sum <$> cast< List ℕ > dyn ∣
          cast< String > dyn)
  where
    fallback = "Value is neither String nor List ℕ"

test-string : go (toDyn CTX "I'm String") ≡ "I'm String"
test-string = refl

test-list : go (toDyn CTX (downFrom 10)) ≡ "45"
test-list = refl
