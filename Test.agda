module Test where

open import Level using (suc)

open import Data.List using (List; _∷_; []; [_])
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Instance
open import SetFuncRep
open import TypeInfo
open import TypeRepMono

sfDec : ∀ {ℓ} (t₁ t₂ : Set (suc ℓ)) {{s : _}} →
        BuildSetFunc {ℓ} t₁ [ s ]=>
        BuildSetFunc {ℓ} t₂ [ s ]=> Maybe (t₁ ≡ t₂)
sfDec {ℓ} t₁ t₂ {{s}} =
  withI {{s}} λ sf₁ → withI {{s}} λ sf₂ → helper (BuildSetFunc.get sf₁) (BuildSetFunc.get sf₂)
  where
    helper : {t₁ t₂ : Set (suc ℓ)} → SetFunc ℓ t₁ → SetFunc ℓ t₂ → Maybe (t₁ ≡ t₂)
    helper set set = just refl
    helper (a₁ ⇒ b₁) (a₂ ⇒ b₂) with helper a₁ a₂ | helper b₁ b₂
    ... | just refl | just refl = just refl
    ... | _         | _         = nothing
    helper _ _ = nothing

postulate
  Int : Set
  Map : Set → Set
  Trans : (Set → Set) → Set → Set

ti-int : Instance (TypeInfo Int)
ti-int = value (typeinfo (quote Int) [])

ti-map : ∀ {t} → Instance (TypeInfo (Map t))
ti-map {t} = value (typeinfo (quote Map) [ _ , t ])

ti-trs : ∀ {t a} → Instance (TypeInfo (Trans t a))
ti-trs {t} {a} = value (typeinfo (quote Trans) ((_ , t) ∷ [ _ , a ]))

qint = stop (quote Int)
qmap = stop (quote Map)
qtrans = stop (quote Trans)

trTest : TypeRep
trTest = getTypeRep (Trans (Trans (Trans Map)) (Map Int))

trProff : trTest ≡ qtrans $$ (qtrans $$ (qtrans $$ qmap)) $$ (qmap $$ qint)
trProff = refl

sfTest : Maybe _
sfTest = sfDec (Set → Set → Set) (Set → Set → Set)

sfProof : sfTest ≡ just refl
sfProof = refl

