module TypeRepMono where

open import Level using () renaming (suc to sucL)
open import Function using (id)
open import Reflection using (Name)

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; []; drop)
open import Data.Product using (_×_; _,_)

open import Utils
open import Instance
open import TypeInfo
open import SetFuncRep

infixl 9 _$$_
data TypeRep : Set where
  stop : Name → TypeRep
  _$$_ : TypeRep → TypeRep → TypeRep

record BuildTypeRep {ℓ} {t : Set (sucL ℓ)} (c : t) : Set (sucL (sucL ℓ)) where
  constructor buildTypeRep
  field get : TypeRep

dropTail : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → List a
dropTail {a = a} n xs = helper (drop n xs) xs
  where
    helper : List a → List a → List a
    helper [] _ = []
    helper _ [] = []
    helper (y ∷ ys) (x ∷ xs) = x ∷ helper ys xs

typeinfo⇒instance : ∀ {ℓ} {t : Set ℓ} {t' : Set (sucL ℓ)} {c : t'} → ℕ → TypeInfo t → Instance (BuildTypeRep {ℓ} c)
typeinfo⇒instance {ℓ = ℓ} {c = c} n (typeinfo name args) = helper (stop name) (dropTail n args)
  where
    helper : TypeRep → List (Heterogeneous (sucL ℓ)) → Instance (BuildTypeRep {ℓ} c)
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
