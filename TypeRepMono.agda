module TypeRepMono where

open import Level using (Lift; _⊔_) renaming (suc to sucL; zero to zeroL)
open import Function
open import Reflection using (Name)

open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; []; [_]; drop) renaming (map to mapL)
open import Data.Product using (∃; _×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Data.Maybe using (Maybe; just; nothing)

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

dropTail : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → List a
dropTail {a = a} n xs = helper (drop n xs) xs
  where
    helper : List a → List a → List a
    helper [] _ = []
    helper _ [] = []
    helper (y ∷ ys) (x ∷ xs) = x ∷ helper ys xs

Heterogeneous : ∀ {ℓ} → Set (sucL ℓ)
Heterogeneous = ∃ id

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

{-----------------------------------------------------------}

postulate
  Int : Set
  Map : Set → Set
  Trans : (Set → Set) → Set → Set

ti-int : Instance (TypeInfo Int)
ti-int = value (typeinfo (quote Int) [])

ti-myb : ∀ {t} → Instance (TypeInfo (Map t))
ti-myb {t} = value (typeinfo (quote Map) [ _ , t ])

ti-trs : ∀ {t a} → Instance (TypeInfo (Trans t a))
ti-trs {t} {a} = value (typeinfo (quote Trans) ((_ , t) ∷ [ _ , a ]))

qint = stop (quote Int)
qmap = stop (quote Map)
qtrans = stop (quote Trans)

trTest : TypeRep
trTest = getTypeRep (Trans (Trans (Trans Map)) (Map Int))

trProff : trTest ≡ qtrans $$ (qtrans $$ (qtrans $$ qmap)) $$ (qmap $$ qint)
trProff = refl

{-----------------------------------------------------------}

sfDec : ∀ {ℓ} (t₁ t₂ : Set (sucL ℓ))
        {{s : _}} →
        BuildSetFunc {ℓ} t₁ [ s ]=>
        BuildSetFunc {ℓ} t₂ [ s ]=> Maybe (t₁ ≡ t₂)
sfDec {ℓ} t₁ t₂ {{s}} =
  withI {{s}} λ sf₁ → withI {{s}} λ sf₂ → helper (BuildSetFunc.get sf₁) (BuildSetFunc.get sf₂)
  where
    helper : {t₁ t₂ : Set (sucL ℓ)} → SetFunc ℓ t₁ → SetFunc ℓ t₂ → Maybe (t₁ ≡ t₂)
    helper set set = just refl
    helper (a₁ ⇒ b₁) (a₂ ⇒ b₂) with helper a₁ a₂ | helper b₁ b₂
    ... | just refl | just refl = just refl
    ... | _         | _         = nothing
    helper _ _ = nothing

xcxcxc : Maybe _
xcxcxc = sfDec (Set → Set → Set) (Set → Set → Set)

sdfv : xcxcxc ≡ just refl
sdfv = refl

