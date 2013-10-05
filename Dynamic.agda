
module Dynamic where

open import Level using (suc)

open import Data.Nat using () renaming (suc to sucN)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Product using (_,_; ,_)
open import Relation.Binary.HeterogeneousEquality using (refl)

open        Data.Vec public using ([])
open import Data.Maybe public using (Maybe; just; nothing; monadPlus)

open import Utils public
open import Instance public
open import SetFuncRep public
open import TypeInfo public
open import TypeRepPoly public
open import TypeRepMono public using () renaming (BuildTypeRep-instance to Mono-BuildTypeRep-instance)

record Dynamic {ℓ} {n} (vec : Vec (Heterogeneous (suc ℓ)) n) : Set (suc (suc ℓ)) where
  constructor dynamic
  field
    typ : Set ℓ
    val : typ
    rep : TypeRep vec {Set ℓ} typ

toDyn : ∀ {ℓ} {n} (vec : Vec (Heterogeneous (suc ℓ)) n)
        {typ : Set ℓ} (val : typ) →
        BuildTypeRep vec typ => Dynamic vec
toDyn _ val = withI λ i → dynamic _ val (BuildTypeRep.get i)

castTr<_> : ∀ {ℓ} {n} {vec : Vec (Heterogeneous (suc ℓ)) n}
                 {typ : Set ℓ} (rep' : TypeRep vec typ) (dyn : Dynamic vec) →
                 Maybe typ
castTr< rep' > (dynamic _ val rep) with typeRepEq rep rep'
... | nothing = nothing
... | just refl = just val

cast<_> : ∀ {ℓ} {n} {vec : Vec (Heterogeneous (suc ℓ)) n}
          (typ : Set ℓ) (dyn : Dynamic vec) →
          BuildTypeRep vec typ => Maybe typ
cast< typ > dyn = withI λ i → castTr< BuildTypeRep.get i > dyn

infixr 5 _:::_
_:::_ : ∀ {ℓ} {n} {typ : Set ℓ} (ctor : typ) (vec : Vec (Heterogeneous ℓ) n) →
        Vec (Heterogeneous ℓ) (sucN n)
ctor ::: vec = (_ , ctor) ∷ vec
