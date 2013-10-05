module SetFuncRep where

open import Level using () renaming (suc to sucL)

open import Data.Maybe using (Maybe; just; nothing; monadPlus)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)

open import Utils
open import Instance

infixr 9 _⇒_
data SetFunc ℓ : Set (sucL ℓ)  → Set (sucL (sucL ℓ)) where
  set : SetFunc ℓ (Set ℓ)
  _⇒_ : ∀ {a b} → SetFunc ℓ a → SetFunc ℓ b → SetFunc ℓ (a → b)

record BuildSetFunc {ℓ} (a : Set (sucL ℓ)) : Set (sucL (sucL ℓ)) where
  constructor buildSetFunc
  field get : SetFunc ℓ a

BuildSetFunc-set : ∀ {ℓ} → Instance (BuildSetFunc (Set ℓ))
BuildSetFunc-set = value (buildSetFunc set)

BuildSetFunc-⇒ : ∀ {ℓ} {a b : Set (sucL ℓ)} → Instance (BuildSetFunc (a → b))
BuildSetFunc-⇒ {a = a} {b = b} =
  instance (BuildSetFunc a ∷ BuildSetFunc b ∷ [])
  λ {(buildSetFunc sfa) (buildSetFunc sfb) → buildSetFunc (sfa ⇒ sfb)}

getSetFunc : ∀ {ℓ} (t : Set (sucL ℓ)) → BuildSetFunc t => SetFunc ℓ t
getSetFunc _ = withI BuildSetFunc.get

constructType : ∀ {ℓ} {t : Set (sucL ℓ)} → SetFunc ℓ t → t
constructType set = Dummy
  where record Dummy {ℓ} : Set ℓ where
constructType (a ⇒ b) = λ _ → constructType b

completeCtor : ∀ {ℓ} {t : Set (sucL ℓ)} → t → SetFunc ℓ t → Set ℓ × ℕ
completeCtor {ℓ} ctor = helper (ctor , 0)
  where
    helper : {t : Set (sucL ℓ)} → t × ℕ → SetFunc ℓ t → Set ℓ × ℕ
    helper result set = result
    helper (ctor , n) (a ⇒ b) = helper (ctor (constructType a) , suc n) b

setFuncEq : ∀ {ℓ} {t₁ t₂ : Set (sucL ℓ)} → SetFunc ℓ t₁ → SetFunc ℓ t₂ → Maybe (t₁ ≡ t₂)
setFuncEq set set = just refl
setFuncEq (a₁ ⇒ b₁) (a₂ ⇒ b₂) = cong₂ (λ a b → a → b) <$> setFuncEq a₁ a₂ ⊛ setFuncEq b₁ b₂
setFuncEq _ _ = nothing
