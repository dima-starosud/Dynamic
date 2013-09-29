module Instance where

open import Level using (Lift; _⊔_; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; [])

data Instance {ℓ} (i : Set ℓ) : Set (suc ℓ) where
  value : i → Instance i
  requires : (t : Set ℓ) (f : t → Instance i) → Instance i

Func : ∀ {ℓ} (ts : List (Set ℓ)) (R : Set ℓ) → Set ℓ
Func [] R = R
Func (t ∷ ts) R = t → Func ts R

instance : ∀ {ℓ} (ts : List (Set ℓ)) {i : Set ℓ} (f : Func ts i) → Instance i
instance [] f = value f
instance (t ∷ ts) f = requires _ λ v → instance ts (f v)

expandRequirement : ∀ {ℓ} {i t : Set ℓ} → Instance t → (t → Instance i) → Instance i
expandRequirement (value t) f = f t
expandRequirement (requires _ f') f = requires _ λ v' → expandRequirement (f' v') f

{-# NO_TERMINATION_CHECK #-}
ResInstanceType : ∀ {a b} {i : Set a} (I : Instance i) (R : i → Set b) → Set (suc a ⊔ b)
ResInstanceType {a} {b} (value i) R = {dirty-hack : Lift {_} {suc a ⊔ b} ⊤} → R i
ResInstanceType (requires t f) R = {{v : Instance t}} → ResInstanceType (expandRequirement v f) R

{-# NO_TERMINATION_CHECK #-}
resolveInstance : ∀ {a b} {i : Set a} (I : Instance i) {R : i → Set b} (r : (x : i) → R x) → ResInstanceType I R
resolveInstance (value i) r = λ {_} → r i
resolveInstance (requires _ f) r = λ {{v}} → resolveInstance (expandRequirement v f) r

data Stop : Set where
  resume : Stop

private
  WithIType : {{s : Stop}} → ∀ {a b} (i : Set a) (R : i → Set b) → Set (suc a ⊔ b)
  WithIType {{resume}} i R = {{I : Instance i}} → ResInstanceType I R

infixr 0 _=>_
_=>_ : ∀ {a b} (i : Set a) (R : Set b) → Set (suc a ⊔ b)
i => R = WithIType i λ _ → R

infixr 0 _=\>_
_=\>_ : ∀ {a b} (i : Set a) (R : i → Set b) → Set (suc a ⊔ b)
_=\>_ = WithIType

infixr 0 _[_]=>_
_[_]=>_ : ∀ {a b} (i : Set a) (s : Stop) (R : Set b) → Set (suc a ⊔ b)
i [ s ]=> R = WithIType {{s}} i λ _ → R

infixr 0 _[_]=\>_
_[_]=\>_ : ∀ {a b} (i : Set a) (s : Stop) (R : i → Set b) → Set (suc a ⊔ b)
i [ s ]=\> R = WithIType {{s}} i R

withI : {{s : Stop}} → ∀ {a b} {i : Set a} {R : i → Set b} (r : ∀ i → R i) → i [ s ]=\> R
withI {{resume}} r = λ {{I}} → resolveInstance I r
