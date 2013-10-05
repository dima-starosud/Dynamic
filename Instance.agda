module Instance where

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to sucL)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; [])

data Instance {ℓ} (i : Set ℓ) : Set (sucL ℓ) where
  value : i → Instance i
  requires : (t : Set ℓ) (f : t → Instance i) → Instance i

Func : ∀ {a} (ts : List (Set a)) (b : Level) (R : Set (a ⊔ b)) → Set (a ⊔ b)
Func [] _ R = R
Func (t ∷ ts) b R = t → Func ts b R

instance : ∀ {ℓ} (ts : List (Set ℓ)) {i : Set ℓ} (f : Func ts ℓ i) → Instance i
instance [] f = value f
instance (t ∷ ts) f = requires _ λ v → instance ts (f v)

instanceI : ∀ {ℓ} (ts : List (Set ℓ)) {i : Set ℓ} (f : Func ts (sucL ℓ) (Instance i)) → Instance i
instanceI [] f = f
instanceI (t ∷ ts) f = requires _ λ v → instanceI ts (f v)

expandRequirement : ∀ {ℓ} {i t : Set ℓ} → Instance t → (t → Instance i) → Instance i
expandRequirement (value t) f = f t
expandRequirement (requires _ f') f = requires _ λ v' → expandRequirement (f' v') f

ResInstanceType : ∀ {a b} (n : ℕ) {i : Set a}
                  (I : Instance i) (R : i → Set b) → Set (sucL a ⊔ b)
ResInstanceType {a} {b} _ (value i) R = {dirty-hack : Lift {_} {sucL a ⊔ b} ⊤} → R i
ResInstanceType {a} {b} zero (requires _ _) _ = Lift {_} {sucL a ⊔ b} ⊤
ResInstanceType (suc n) (requires t f) R = {{v : Instance t}} → ResInstanceType n (expandRequirement v f) R

resolveInstance : ∀ {a b} (depth : ℕ) {i : Set a}
                  (I : Instance i) {R : i → Set b} (r : (x : i) → R x) → ResInstanceType depth I R
resolveInstance _ (value i) r = λ {_} → r i
resolveInstance zero (requires _ _) _ = lift _
resolveInstance (suc n) (requires _ f) r = λ {{v}} → resolveInstance n (expandRequirement v f) r

data Stop : Set where
  resume : Stop

record SearchDepth : Set where
  constructor searchdepth
  field
    get : ℕ

private
  WithIType : {{s : Stop}} → ∀ {a b} (depth : ℕ) (i : Set a) (R : i → Set b) → Set (sucL a ⊔ b)
  WithIType {{resume}} depth i R = {{I : Instance i}} → ResInstanceType depth I R

infixr 0 _=>_
_=>_ : ∀ {a b} {{depth : SearchDepth}} (i : Set a) (R : Set b) → Set (sucL a ⊔ b)
_=>_ {{searchdepth n}} i R = WithIType n i λ _ → R

infixr 0 _=\>_
_=\>_ : ∀ {a b} {{depth : SearchDepth}} (i : Set a) (R : i → Set b) → Set (sucL a ⊔ b)
_=\>_ {{searchdepth n}} = WithIType n

infixr 0 _[_]=>_
_[_]=>_ : ∀ {a b} {{depth : SearchDepth}} (i : Set a) (s : Stop) (R : Set b) → Set (sucL a ⊔ b)
_[_]=>_ {{searchdepth n}} i s R = WithIType {{s}} n i λ _ → R

infixr 0 _[_]=\>_
_[_]=\>_ : ∀ {a b} {{depth : SearchDepth}} (i : Set a) (s : Stop) (R : i → Set b) → Set (sucL a ⊔ b)
_[_]=\>_ {{searchdepth n}} i s R = WithIType {{s}} n i R

withI : {{s : Stop}} → ∀ {a b} {{depth : SearchDepth}} {i : Set a} {R : i → Set b} (r : ∀ i → R i) → i [ s ]=\> R
withI {{resume}} {{searchdepth n}} r = λ {{I}} → resolveInstance n I r

DefaultSearchDepth : SearchDepth
DefaultSearchDepth = searchdepth 25
