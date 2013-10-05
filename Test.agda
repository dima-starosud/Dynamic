module Test where

open import Level using (suc)
open import Function using (id; _$_; _∘_; _∋_)

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; _∷_; []; toList)
open import Data.List using (List; _∷_; []; [_])
open import Data.Product using (_,_; ,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

open import Utils
open import Instance
open import SetFuncRep
open import TypeInfo
open import TypeRepMono as M
open import TypeRepPoly as P

postulate
  Int : Set
  Map : Set → Set
  Trans : (Set → Set) → Set → Set

ti-int : Instance (TypeInfo Int)
ti-int = value (typeinfo (quote Int) [])

ti-map : ∀ {t} → Instance (TypeInfo (Map t))
ti-map {t} = value (typeinfo (quote Map) [ , t ])

ti-trs : ∀ {t a} → Instance (TypeInfo (Trans t a))
ti-trs {t} {a} = value (typeinfo (quote Trans) ((, t) ∷ [ , a ]))

ti-top : Instance (TypeInfo ⊤)
ti-top = value (typeinfo (quote ⊤) [])

qint = M.stop (quote Int)
qmap = M.stop (quote Map)
qtrans = M.stop (quote Trans)

monoTrTest : M.TypeRep
monoTrTest = M.getTypeRep (Trans (Trans (Trans Map)) (Map Int))

monoTrTestProff : monoTrTest ≡ qtrans $$ (qtrans $$ (qtrans $$ qmap)) $$ (qmap $$ qint)
monoTrTestProff = refl

setFuncEq2 : ∀ {ℓ} (t₁ t₂ : Set (suc ℓ)) {{s : _}} →
             BuildSetFunc {ℓ} t₁ [ s ]=>
             BuildSetFunc {ℓ} t₂ [ s ]=> Maybe (t₁ ≡ t₂)
setFuncEq2 {ℓ} t₁ t₂ {{s}} =
  withI {{s}} λ sf₁ → withI {{s}} λ sf₂ → setFuncEq (BuildSetFunc.get sf₁) (BuildSetFunc.get sf₂)

sfe2Test : Maybe _
sfe2Test = setFuncEq2 (Set → Set → Set) (Set → Set → Set)

sfe2Proof : sfe2Test ≡ just refl
sfe2Proof = refl

record Show (t : Set) : Set where
  constructor mkShow
  field get : t → String

ShowList : ∀ {a} → Instance (Show (List a))
ShowList {a} = instance [ Show a ] (mkShow ∘ helper ∘ Show.get)
  where
    helper : (a → String) → List a → String
    helper show xs = "[" ++ shows xs ++ "]"
      where
        shows : List a → String
        shows [] = ""
        shows (x ∷ []) = show x
        shows (x ∷ xs) = show x ++ ", " ++ shows xs

ShowVec : ∀ {a n} → Instance (Show (Vec a n))
ShowVec {a} = instance [ Show (List a) ] λ i → mkShow (Show.get i ∘ toList)

ShowNat : Instance (Show ℕ)
ShowNat = value (mkShow showℕ)

show : {t : Set} → t → Show t => String
show t = withI λ s → Show.get s t

showxs : String
showxs = show (List _ ∋ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])

testShowxs : showxs ≡ "[1, 2, 3, 4]"
testShowxs = refl

checkEq : ∀ {ℓ} {t₁ t₂ : Set ℓ} (v₁ : t₁) (v₂ : t₂) →
          BuildHetRefl v₁ v₂ => v₁ ≅ v₂
checkEq _ _ = withI BuildHetRefl.get

testEq : _ ≅ _
testEq = checkEq (Map Int) (Map Int)

checkSf : ∀ {ℓ n} (vec : Vec (Heterogeneous (suc ℓ)) n) →
          BuildCtorSf vec => Vec _ n
checkSf _ = withI BuildCtorSf.get

testSf : Vec _ 1
testSf = checkSf ((Set , Int) ∷ [])

polyTrTest : P.TypeRep _ _
polyTrTest = P.getTypeRep ((, ⊤) ∷ []) ⊤

polyTrProof : polyTrTest ≡ stop zero
polyTrProof = refl
