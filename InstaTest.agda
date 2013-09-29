module InstaTest where

open import Level using (Lift; _⊔_) renaming (suc to sucL; zero to zeroL)
open import Function
open import Reflection using (Name)

open import Data.Nat using (ℕ) renaming (suc to sucN)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; []; [_]; drop) renaming (map to mapL)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Data.Maybe using (Maybe; just; nothing)

import Dynamic
open Dynamic using (Heterogeneous)

data Instance {ℓ} (i : Set ℓ) : Set (sucL ℓ) where
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
ResInstanceType : ∀ {a b} {i : Set a} (I : Instance i) (R : i → Set b) → Set (sucL a ⊔ b)
ResInstanceType {a} {b} (value i) R = {dirty-hack : Lift {_} {sucL a ⊔ b} ⊤} → R i
ResInstanceType (requires t f) R = {{v : Instance t}} → ResInstanceType (expandRequirement v f) R

{-# NO_TERMINATION_CHECK #-}
resolveInstance : ∀ {a b} {i : Set a} (I : Instance i) {R : i → Set b} (r : (x : i) → R x) → ResInstanceType I R
resolveInstance (value i) r = λ {_} → r i
resolveInstance (requires _ f) r = λ {{v}} → resolveInstance (expandRequirement v f) r

data Stop : Set where
  resume : Stop

WithIType : {{s : Stop}} → ∀ {a b} (i : Set a) (R : i → Set b) → Set (sucL a ⊔ b)
WithIType {{resume}} i R = {{I : Instance i}} → ResInstanceType I R

infixr 0 _=>_
_=>_ : ∀ {a b} (i : Set a) (R : Set b) → Set (sucL a ⊔ b)
i => R = WithIType i λ _ → R

infixr 0 _=\>_
_=\>_ : ∀ {a b} (i : Set a) (R : i → Set b) → Set (sucL a ⊔ b)
_=\>_ = WithIType

infixr 0 _[_]=>_
_[_]=>_ : ∀ {a b} (i : Set a) (s : Stop) (R : Set b) → Set (sucL a ⊔ b)
i [ s ]=> R = WithIType {{s}} i λ _ → R

infixr 0 _[_]=\>_
_[_]=\>_ : ∀ {a b} (i : Set a) (s : Stop) (R : i → Set b) → Set (sucL a ⊔ b)
i [ s ]=\> R = WithIType {{s}} i R

withI : {{s : Stop}} → ∀ {a b} {i : Set a} {R : i → Set b} (r : ∀ i → R i) → i [ s ]=\> R
withI {{resume}} r = λ {{I}} → resolveInstance I r

{-----------------------------------------------------------}

infixr 9 _⇒_
data SF ℓ : Set (sucL ℓ)  → Set (sucL (sucL ℓ)) where
  set : SF ℓ (Set ℓ)
  _⇒_ : ∀ {a b} → SF ℓ a → SF ℓ b → SF ℓ (a → b)

record BuildSF {ℓ} (a : Set (sucL ℓ)) : Set (sucL (sucL ℓ)) where
  constructor buildSF
  field get : SF ℓ a

bsf-set : ∀ {ℓ} → Instance (BuildSF (Set ℓ))
bsf-set = value (buildSF set)

bsf-imp : ∀ {ℓ} {a b : Set (sucL ℓ)} → Instance (BuildSF (a → b))
bsf-imp {a = a} {b = b} =
  instance (BuildSF a ∷ BuildSF b ∷ [])
  λ {(buildSF sfa) (buildSF sfb) → buildSF (sfa ⇒ sfb)}

getSF : ∀ {ℓ} (t : Set (sucL ℓ)) →
        BuildSF t => SF ℓ t
getSF _ = withI BuildSF.get

buildSfType : ∀ {ℓ} {t : Set (sucL ℓ)} → SF ℓ t → t
buildSfType set = Dummy
  where record Dummy {ℓ} : Set ℓ where
buildSfType (a ⇒ b) = λ _ → buildSfType b

completeCtor : ∀ {ℓ} {t : Set (sucL ℓ)} → t → SF ℓ t → Set ℓ × ℕ
completeCtor {ℓ} ctor = helper (ctor , 0)
  where
    helper : {t : Set (sucL ℓ)} → t × ℕ → SF ℓ t → Set ℓ × ℕ
    helper result set = result
    helper (ctor , n) (a ⇒ b) = helper (ctor (buildSfType a) , sucN n) b

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

btr : ∀ {ℓ} {t : Set (sucL ℓ)} {c : t} → Instance (BuildTypeRep c)
btr {t = t} {c = c} =
  requires (BuildSF t)
  λ {(buildSF sf) → 
     let typ , n = completeCtor c sf
     in requires (TypeInfo typ) (typeinfo⇒instance n)
    }

getTR : ∀ {ℓ} {t : Set (sucL ℓ)} (c : t) →
        BuildTypeRep c => TypeRep
getTR _ = withI BuildTypeRep.get

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
trTest = getTR (Trans (Trans (Trans Map)) (Map Int))

trProff : trTest ≡ qtrans $$ (qtrans $$ (qtrans $$ qmap)) $$ (qmap $$ qint)
trProff = refl

{-----------------------------------------------------------}

sfDec : ∀ {ℓ} (t₁ t₂ : Set (sucL ℓ))
        {{s : Stop}} →
        BuildSF {ℓ} t₁ [ s ]=>
        BuildSF {ℓ} t₂ [ s ]=> Maybe (t₁ ≡ t₂)
sfDec {ℓ} t₁ t₂ {{s}} =
  withI {{s}} λ sf₁ → withI {{s}} λ sf₂ → helper (BuildSF.get sf₁) (BuildSF.get sf₂)
  where
    helper : {t₁ t₂ : Set (sucL ℓ)} → SF ℓ t₁ → SF ℓ t₂ → Maybe (t₁ ≡ t₂)
    helper set set = just refl
    helper (a₁ ⇒ b₁) (a₂ ⇒ b₂) with helper a₁ a₂ | helper b₁ b₂
    ... | just refl | just refl = just refl
    ... | _         | _         = nothing
    helper _ _ = nothing

xcxcxc : Maybe _
xcxcxc = sfDec (Set → Set → Set) (Set → Set → Set)

sdfv : xcxcxc ≡ just refl
sdfv = refl

