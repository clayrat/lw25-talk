{-# OPTIONS --safe #-}
module Unif.Term where

open import Prelude

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Char
open import Data.List
open import Data.String

open import LFSet as LFSet
open import LFSet.Membership

Var : 𝒰
Var = String

Ctx : 𝒰
Ctx = LFSet Var

-- symbols

_==s_ : String → String → Bool
s₁ ==s s₂ = string→list s₁ =? string→list s₂

Sy : 𝒰
Sy = String

-- terms
-- TODO try embedding membership in the syntax

data Term : 𝒰 where
  ``_  : Var → Term
  _＋_ : Term → Term → Term
  sy   : Sy → Term

module Term-code where

  Code : Term → Term → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ＋ q₁) (p₂ ＋ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code (sy s₁)    (sy s₂)   = s₁ ＝ s₂
  Code _           _          = ⊥

  code-refl : (t : Term) → Code t t
  code-refl (`` x)   = refl
  code-refl (p ＋ q) = code-refl p , code-refl q
  code-refl (sy s)   = refl

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = `` x}      {t₂ = `` y}      c        = ap ``_ c
  decode {t₁ = p₁ ＋ q₁} {t₂ = p₂ ＋ q₂} (c₁ , c₂) = ap² _＋_ (decode c₁) (decode c₂)
  decode {t₁ = sy s₁}    {t₂ = sy s₂}    c        = ap sy c

``-inj : {x y : Var} → `` x ＝ `` y → x ＝ y
``-inj = Term-code.encode

sy-inj : ∀ {s₁ s₂} → sy s₁ ＝ sy s₂ → s₁ ＝ s₂
sy-inj = Term-code.encode

＋-inj : ∀ {p₁ q₁ p₂ q₂} → p₁ ＋ q₁ ＝ p₂ ＋ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
＋-inj e =
  let (c₁ , c₂) = Term-code.encode e in
  Term-code.decode c₁ , Term-code.decode c₂

``≠＋ : ∀ {x p q} → `` x ≠ p ＋ q
``≠＋ = Term-code.encode

``≠sy : ∀ {x s} → `` x ≠ sy s
``≠sy = Term-code.encode

＋≠sy : ∀ {p q s} → p ＋ q ≠ sy s
＋≠sy = Term-code.encode

_==tm_ : Term → Term → Bool
(`` x)      ==tm (`` y)     = x ==s y
(p₁ ＋ q₁) ==tm (p₂ ＋ q₂) = p₁ ==tm p₂ and q₁ ==tm q₂
(sy s₁)    ==tm (sy s₂)   = s₁ ==s s₂
_           ==tm _          = false

instance
  tm-eq-reflects : ∀ {x y} → Reflects (x ＝ y) (x ==tm y)
  tm-eq-reflects {x = `` x}      {y = `` y}     =
    Reflects.dmap (ap ``_) (contra ``-inj) Reflects-String-Path
  tm-eq-reflects {x = `` _}      {y = _ ＋ _}  = ofⁿ ``≠＋
  tm-eq-reflects {x = `` _}      {y = sy s₂}   = ofⁿ ``≠sy
  tm-eq-reflects {x = _ ＋ _}   {y = `` _}     = ofⁿ (``≠＋ ∘ _⁻¹)
  tm-eq-reflects {x = p₁ ＋ q₁} {y = p₂ ＋ q₂} =
    Reflects.dmap
      (λ where (e₁ , e₂) → ap² _＋_ e₁ e₂)
      (contra ＋-inj)
      (Reflects-× ⦃ rp = tm-eq-reflects ⦄ ⦃ rq = tm-eq-reflects ⦄)
  tm-eq-reflects {x = _ ＋ _}   {y = sy s₂}   = ofⁿ ＋≠sy
  tm-eq-reflects {x = sy s₁}    {y = `` _}     = ofⁿ (``≠sy ∘ _⁻¹)
  tm-eq-reflects {x = sy s₁}   {y = _ ＋ _}   = ofⁿ (＋≠sy ∘ _⁻¹)
  tm-eq-reflects {x = sy s₁}   {y = sy s₂}   =
    Reflects.dmap
        (ap sy)
        (contra sy-inj)
        (Reflects-String-Path {s₁ = s₁} {s₂ = s₂})

  Term-is-discrete : is-discrete Term
  Term-is-discrete {x} {y} .does = x ==tm y
  Term-is-discrete .proof = tm-eq-reflects

  H-Level-Term : ∀ {n} → H-Level (2 + n) Term
  H-Level-Term = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Term #-}

-- size

tm-size : Term → ℕ
tm-size (p ＋ q) = suc (tm-size p + tm-size q)
tm-size _        = 1

0<tm-size : ∀ {t} → 0 < tm-size t
0<tm-size {t = `` _}    = z<s
0<tm-size {t = _ ＋ _} = z<s
0<tm-size {t = sy s}   = z<s

-- substitution

sub1 : Var → Term → Term → Term
sub1 v t (`` x)    = if v ==s x then t else `` x
sub1 v t (p ＋ q) = sub1 v t p ＋ sub1 v t q
sub1 v t (sy s)   = sy s

-- vars

vars : Term → Ctx
vars (`` x)    = x ∷ []
vars (p ＋ q) = vars p ∪∷ vars q
vars (sy _)   = []

-- well-formedness
-- TODO this goes away if membership is embedded in the syntax

wf-tm : Ctx → Term → 𝒰
wf-tm c t = vars t ⊆ c
