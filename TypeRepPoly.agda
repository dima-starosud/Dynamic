
module TypeRepPoly where

open import Level using (Lift; lower; lift; suc; _⊔_)
open import Reflection using (Name; _≟-Name_)
open import Function using (id; const; _∋_; flip; _∘_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using () renaming (suc to sucN; zero to zeroN)
open import Data.Fin using (Fin; compare; equal) renaming (suc to sucF; zero to zeroF)
open import Data.Vec using (Vec; []; _∷_; lookup; foldl; zip; allFin; map)
open import Data.List using (List; []; _∷_; [_])
open import Data.Product using (Σ; ∃; _×_; _,_; ,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing; monadPlus; maybe)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

open import Utils
open import Instance
open import TypeInfo
open import SetFuncRep
import TypeRepMono as M

infixl 9 _$$_
data TypeRep {ℓ} {n} (vec : Vec (Heterogeneous ℓ) n) : {t : Set ℓ} → t → Set (suc ℓ) where
  stop : (i : Fin n) → TypeRep vec (proj₂ (lookup i vec))
  _$$_ : {A : Set _} {B : Set _} {f : A → B} {a : A} →
         TypeRep vec f → TypeRep vec a → TypeRep vec (f a)

private
  ⇒-args : ∀ {a b} {A₁ A₂ : Set a} {B₁ : Set b} {B₂ : Set b}
           {f : A₁ → B₁} {g : A₂ → B₂} →
           f ≅ g → A₁ ≡ A₂ × B₁ ≡ B₂
  ⇒-args _ = trustMe , trustMe

typeRepEq : ∀ {ℓ n T₁ t₁ T₂ t₂ vec} → TypeRep {ℓ} {n} vec {T₁} t₁ → TypeRep {ℓ} {n} vec {T₂} t₂ → Maybe (t₁ ≅ t₂)
typeRepEq (stop i)  (stop j) with compare i j
typeRepEq (stop ._) (stop ._) | equal _ = just refl
typeRepEq (stop _)  (stop _)  | _ = nothing
typeRepEq (f $$ x) (g $$ y) with typeRepEq f g | typeRepEq x y
typeRepEq (_ $$ _) (_ $$ _) | just p    | just refl with ⇒-args p
typeRepEq (_ $$ _) (_ $$ _) | just refl | just refl | refl , refl = just refl
typeRepEq (_ $$ _) (_ $$ _) | _ | _ = nothing
typeRepEq _ _ = nothing

private
  findIndex : ∀ {ℓ β n} {t : Set ℓ} → (t → Bool) → Vec t n → Maybe (Lift {_} {β} (Fin n))
  findIndex {ℓ} {β} {n = n} {t = t} f = foldl _ folder nothing ∘ zip (allFin n)
    where
      folder : Maybe (Lift (Fin n)) → Fin n × t → _
      folder acc (fin , t) = acc ∣ (if f t then just (lift fin) else nothing)

  name-eq : Name → Name → Bool
  name-eq n m with n ≟-Name m
  ... | yes _ = true
  ... | no _ = false

  CtorSf : ∀ ℓ → Set (suc (suc ℓ))
  CtorSf ℓ = Name × Σ (Set (suc ℓ)) λ sf → SetFunc ℓ sf × sf

  CtorSfTr : ∀ {ℓ n} → Vec (Heterogeneous (suc ℓ)) n → Set (suc (suc ℓ))
  CtorSfTr {ℓ} vec = Σ (Set (suc ℓ)) λ t → SetFunc ℓ t × Σ t λ ctor → TypeRep {suc ℓ} vec {t} ctor

  TryApplySfTr : ∀ {ℓ n} {vec : Vec (Heterogeneous (suc ℓ)) n} → CtorSfTr vec → CtorSfTr vec → Maybe (CtorSfTr vec)
  TryApplySfTr {vec = vec} (._ , sfA ⇒ sfB , A⇒B , trA⇒B) (_ , sfA' , A' , trA') = helper A⇒B A' sfB trA⇒B trA' <$> setFuncEq sfA sfA'
    where
      helper : ∀ {A B A'} (f : A → B) (a' : A') → SetFunc _ B → TypeRep vec f → TypeRep vec a' → A ≡ A' → CtorSfTr vec
      helper f a' sfB trF trA' refl = _ , sfB , f a' , trF $$ trA'
  TryApplySfTr (._ , set , _ , _) _ = nothing

  toH : ∀ {ℓ} → CtorSf ℓ → Heterogeneous (suc ℓ)
  toH (_ , t , _ , sf) = t , sf

  toHVec : ∀ {ℓ n} → Vec (CtorSf ℓ) n → Vec (Heterogeneous (suc ℓ)) n
  toHVec = map toH

  stop-TypeRep : ∀ {ℓ n} (i : Fin n) (vec : Vec (CtorSf ℓ) n) →
                 TypeRep (toHVec vec) (proj₂ (toH (lookup i vec)))
  stop-TypeRep {ℓ} {n} i vec = subst id (≡-proof n i vec) (stop i)
    where
      ≡-proof : ∀ {m} n i {base : Vec _ m} (vec : Vec (CtorSf ℓ) n) →
                TypeRep base (proj₂ (lookup i (toHVec vec))) ≡
                TypeRep base (proj₂ (toH (lookup i vec)))
      ≡-proof zeroN () []
      ≡-proof (sucN n) zeroF (x ∷ xs) = refl
      ≡-proof (sucN n) (sucF i) (x ∷ xs) = ≡-proof n i xs

  TypeRepDataHelper : ∀ {ℓ n} (vec : Vec (CtorSf ℓ) n) → M.TypeRep → Maybe (CtorSfTr (toHVec vec))
  TypeRepDataHelper {ℓ} {n} vec (M.stop name) = helper <$> findIndex (name-eq name) (map proj₁ vec)
    where
      helper : Lift {_} {suc (suc ℓ)} (Fin n) → CtorSfTr (toHVec vec)
      helper (lift i) = _ , sf , ctor , stop-TypeRep i vec
        where
          ctorsf = lookup i vec
          sf = proj₁ (proj₂ (proj₂ ctorsf))
          ctor = proj₂ (proj₂ (proj₂ ctorsf))
  TypeRepDataHelper vec (f M.$$ a) =
    TypeRepDataHelper vec f >>= λ f →
    TypeRepDataHelper vec a >>= λ a →
    TryApplySfTr f a

  HeteroTypeRep : ∀ ℓ → Set (suc (suc ℓ))
  HeteroTypeRep ℓ = ∃ λ n → Σ (Vec _ n) λ vec → Σ (Set (suc ℓ)) λ t → Σ t λ ctor → TypeRep {suc ℓ} vec {t} ctor

  TypeRepData : ∀ {ℓ n} (vec : Vec (CtorSf ℓ) n) → M.TypeRep → HeteroTypeRep ℓ
  TypeRepData vec mtr with TypeRepDataHelper vec mtr
  ... | nothing = 1 , (_ , Lift ⊤) ∷ [] , _ , Lift ⊤ , stop zeroF
  ... | just (t , _ , ctor , tr) = _ , _ , t , ctor , tr

record BuildCtorSf {ℓ n} (vec : Vec (Heterogeneous (suc ℓ)) n) : Set (suc (suc ℓ)) where
  constructor buildCtorSf
  field
    get : Vec (CtorSf ℓ) n

BuildCtorSf-nil : ∀ {ℓ} → Instance (BuildCtorSf {ℓ} [])
BuildCtorSf-nil {ℓ} = value (buildCtorSf [])

BuildCtorSf-cons : ∀ {ℓ n} {x : Heterogeneous (suc ℓ)} {xs : Vec (Heterogeneous (suc ℓ)) n} →
                   Instance (BuildCtorSf (x ∷ xs))
BuildCtorSf-cons {x = (t , x)} {xs = xs} =
  instanceI (BuildSetFunc t ∷ [ BuildCtorSf xs ])
  λ {(buildSetFunc sf) (buildCtorSf xs) →
     let ctor , _ = completeCtor x sf
     in instance [ TypeInfo ctor ]
        λ {(typeinfo name _) → buildCtorSf ((name , t , sf , x) ∷ xs)}
    }

record BuildTypeRep {ℓ n} (vec : Vec (Heterogeneous (suc ℓ)) n) {t : Set (suc ℓ)} (ctor : t) : Set (suc (suc ℓ)) where
  constructor buildTypeRep
  field
    get : TypeRep vec ctor

record BuildRefl {ℓ} {t : Set ℓ} (x y : t) : Set ℓ where
  constructor buildRefl
  field
    get : x ≡ y

record BuildHetRefl {ℓ} {t₁ t₂ : Set ℓ} (x : t₁) (y : t₂) : Set ℓ where
  constructor buildRefl
  field
    get : x ≅ y

BuildRefl-instance : ∀ {ℓ} {t : Set ℓ} {x : t} → Instance (BuildRefl x x)
BuildRefl-instance = value (buildRefl refl)

BuildHetRefl-instance : ∀ {ℓ} {t : Set ℓ} {x : t} → Instance (BuildHetRefl x x)
BuildHetRefl-instance = value (buildRefl refl)

private
  typeRepFromRefls :
    ∀ {ℓ n₁ n₂}
    {vec₁ : Vec (Heterogeneous (suc ℓ)) n₁} {vec₂ : Vec (Heterogeneous (suc ℓ)) n₂}
    {t₁ t₂ : Set (suc ℓ)} {ctor₁ : t₁} {ctor₂ : t₂} →
    lift {_} {suc (suc ℓ)} n₁ ≡ lift {_} {suc (suc ℓ)} n₂ →
    vec₁ ≅ vec₂ →
    t₁ ≡ t₂ →
    lift {_} {suc (suc ℓ)} ctor₁ ≅ lift {_} {suc (suc ℓ)} ctor₂ →
    TypeRep vec₁ {t₁} ctor₁ → TypeRep vec₂ {t₂} ctor₂
  typeRepFromRefls refl refl refl refl = id

  instanceHelper :
    ∀ {ℓ} n₁ n₂
    (vec₁ : Vec (Heterogeneous (suc ℓ)) n₁) (vec₂ : Vec (Heterogeneous (suc ℓ)) n₂)
    (t₁ t₂ : Set (suc ℓ)) (ctor₁ : t₁) (ctor₂ : t₂) →
    TypeRep vec₁ {t₁} ctor₁ → Instance (BuildTypeRep vec₂ ctor₂)
  instanceHelper {ℓ} n₁ n₂ vec₁ vec₂ t₁ t₂ ctor₁ ctor₂ tr₁ =
    instance (
      BuildRefl (lift {_} {suc (suc ℓ)} n₁) (lift {_} {suc (suc ℓ)} n₂) ∷
      BuildHetRefl vec₁ vec₂ ∷
      BuildRefl t₁ t₂ ∷
      BuildHetRefl (lift {_} {suc (suc ℓ)} ctor₁) (lift {_} {suc (suc ℓ)} ctor₂) ∷
      [])
    λ {(buildRefl n-eq) (buildRefl vec-eq) (buildRefl t-eq) (buildRefl ctor-eq) →
       buildTypeRep (typeRepFromRefls n-eq vec-eq t-eq ctor-eq tr₁)
      }

BuildTypeRep-instance : ∀ {ℓ n} {vec : Vec (Heterogeneous (suc ℓ)) n} {t : Set (suc ℓ)} {ctor : t} → Instance (BuildTypeRep vec ctor)
BuildTypeRep-instance {ℓ} {n} {vec} {t} {ctor} =
  instanceI (BuildCtorSf vec ∷ [ M.BuildTypeRep ctor ])
  λ {(buildCtorSf vecSf) (M.buildTypeRep ctorTr) →
     let n₁ , vec₁ , t₁ , ctor₁ , tr₁ = TypeRepData vecSf ctorTr
     in instanceHelper n₁ n vec₁ vec t₁ t ctor₁ ctor tr₁
    }

getTypeRep : ∀ {n} (vec : Vec _ n) (t : Set) → BuildTypeRep vec t => TypeRep vec t
getTypeRep _ _ = withI BuildTypeRep.get
