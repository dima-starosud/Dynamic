module TypeRepMono where

open import Level using () renaming (suc to sucL)
open import Function using (id)
open import Reflection using (Name)

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; []; [_]; drop)
open import Data.Product using (∃; _×_; _,_)

open import Instance

Heterogeneous : ∀ {ℓ} → Set (sucL ℓ)
Heterogeneous = ∃ id

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

dropTail : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → List a
dropTail {a = a} n xs = helper (drop n xs) xs
  where
    helper : List a → List a → List a
    helper [] _ = []
    helper _ [] = []
    helper (y ∷ ys) (x ∷ xs) = x ∷ helper ys xs

infixl 9 _$$_
data TypeRep : Set where
  stop : Name → TypeRep
  _$$_ : TypeRep → TypeRep → TypeRep

record BuildTypeRep {ℓ} {t : Set (sucL ℓ)} (c : t) : Set (sucL (sucL ℓ)) where
  constructor buildTypeRep
  field get : TypeRep

record TypeInfo {ℓ} (t : Set ℓ) : Set (sucL (sucL ℓ)) where
  constructor typeinfo
  field
    name : Name
    args : List (Heterogeneous {sucL ℓ})

typeinfo⇒instance : ∀ {ℓ} {t : Set ℓ} {t' : Set (sucL ℓ)} {c : t'} → ℕ → TypeInfo t → Instance (BuildTypeRep {ℓ} c)
typeinfo⇒instance {ℓ = ℓ} {c = c} n (typeinfo name args) = helper (stop name) (dropTail n args)
  where
    helper : TypeRep → List (Heterogeneous {sucL ℓ}) → Instance (BuildTypeRep {ℓ} c)
    helper tr [] = value (buildTypeRep tr)
    helper tr ((_ , t) ∷ ts) =
      requires (BuildTypeRep t)
      λ {(buildTypeRep arg) -> helper (tr $$ arg) ts}

BuildTypeRep-instance : ∀ {ℓ} {t : Set (sucL ℓ)} {c : t} → Instance (BuildTypeRep c)
BuildTypeRep-instance {t = t} {c = c} =
  requires (BuildSetFunc t)
  λ {(buildSetFunc sf) → 
     let typ , n = completeCtor c sf
     in requires (TypeInfo typ) (typeinfo⇒instance n)
    }

getTypeRep : ∀ {ℓ} {t : Set (sucL ℓ)} (c : t) → BuildTypeRep c => TypeRep
getTypeRep _ = withI BuildTypeRep.get
