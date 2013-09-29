
module Dynamic where

import Level as L

open import Function using (id)

import Data.Nat using ()
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Data.Maybe

open import Relation.Binary.Core hiding (_⇒_)
open import Relation.Binary.HeterogeneousEquality
open import Relation.Binary.PropositionalEquality.TrustMe

Heterogeneous : ∀ {ℓ} → Set (L.suc ℓ)
Heterogeneous = ∃ id

infixl 9 _$$_
data TypeRep {ℓ} {n} (vec : Vec Heterogeneous n) : {t : Set ℓ} → t → Set (L.suc ℓ) where
  stop : (i : Fin n) → TypeRep vec (proj₂ (lookup i vec))
  _$$_ : {A : Set _} {B : Set _} {f : A → B} {a : A} →
         TypeRep vec f → TypeRep vec a → TypeRep vec (f a)

private
  ⇒-args : ∀ {a b} {A1 A2 : Set a} {B1 : Set b} {B2 : Set b}
           {f : A1 → B1} {g : A2 → B2} →
           f ≅ g → A1 ≡ A2 × B1 ≡ B2
  ⇒-args _ = trustMe , trustMe

typeRepEq : ∀ {ℓ n T1 t1 T2 t2 vec} → TypeRep {ℓ} {n} vec {T1} t1 → TypeRep {ℓ} {n} vec {T2} t2 → Maybe (t1 ≅ t2)
typeRepEq (stop i)  (stop j) with compare i j
typeRepEq (stop ._) (stop ._) | equal _ = just refl
typeRepEq (stop _)  (stop _)  | _ = nothing

typeRepEq (f $$ x) (g $$ y) with typeRepEq f g | typeRepEq x y
typeRepEq (_ $$ _) (_ $$ _) | just p    | just refl with ⇒-args p
typeRepEq (_ $$ _) (_ $$ _) | just refl | just refl | refl , refl = just refl

typeRepEq (_ $$ _) (_ $$ _) | _ | _ = nothing
typeRepEq _ _ = nothing

{-------------------------- DYNAMIC --------------------------}

Dynamic : ∀ {ℓ} (rep : {t : Set (L.suc ℓ)} → t → Set (L.suc (L.suc ℓ))) → Set (L.suc (L.suc ℓ))
Dynamic rep = ∃ λ t → rep t × t

{-
record DecidableRep {ℓ} (rep : {t : Set (L.suc ℓ)} → t → Set (L.suc (L.suc ℓ))) : Set (L.suc (L.suc ℓ)) where
  constructor decidable
  field get : ∀ {t₁ t₂ : Set _} → rep t₁ → rep t₂ → Maybe (t₁ ≅ t₂)

cast : ∀ {ℓ} {rep : {t : Set _} → t → Set _}
       {{dec : DecidableRep rep}} {t : Set _} {new : rep t}
       → Dynamic {ℓ} rep → Maybe t
cast {{dec = dec}} {new = new} (_ , old , val) = _ (DecidableRep.get dec old new)
-- -}

{-------------------------- TESTING --------------------------}

private
  postulate
    StateT : Set → (Set → Set) → Set → Set
    Int    : Set
    String : Set

  vec : Vec Heterogeneous _
  vec = (_ , StateT) ∷ (_ , Maybe) ∷ (_ , Int) ∷ (_ , String) ∷ []

  one : Fin 4
  one = suc zero

  two : Fin 4
  two = suc (suc zero)

  three : Fin 4
  three = suc (suc (suc zero))

  test1 : TypeRep vec (StateT Int Maybe String)
  test1 = stop zero $$ stop two $$ stop one $$ stop three

  test2 : TypeRep vec (Maybe Int)
  test2 = stop one $$ stop two

