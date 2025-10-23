{-# OPTIONS --safe #-}
module Unif.Unify where

open import Prelude
open import Meta.Effect
open Variadics _
open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.String
open import Data.Sum

open import LFSet as LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Induction.Nat.Lex as Box× using (□×_)

open import Unif.SubC
open import Unif.Term

Constr : 𝒰
Constr = Term × Term

constr-size : Constr → ℕ
constr-size (p , q) = tm-size p + tm-size q

constr-sizes : List Constr → ℕ
constr-sizes = List.rec 0 λ c → constr-size c +_

Input : 𝒰
Input = Ctx × List Constr

constr-vars : List Constr → Ctx
constr-vars = List.rec [] (λ where (l , r) → (vars l ∪∷ vars r) ∪∷_)

wf-input : Input → 𝒰
wf-input (ctx , lc) = All (λ x → wf-tm ctx (x .fst) × wf-tm ctx (x .snd)) lc

wf-constr-vars : ∀ {lc} → wf-input (constr-vars lc , lc)
wf-constr-vars {lc = []} = []
wf-constr-vars {lc = (l , r) ∷ lc} =
    (∈ₛ-∪∷←l ∘ ∈ₛ-∪∷←l , ∈ₛ-∪∷←l ∘ ∈ₛ-∪∷←r {s₁ = vars l})
  ∷ all-map
      (λ where {x = x , y} (wx , wy) →
                    ∈ₛ-∪∷←r {s₁ = vars l ∪∷ vars r} ∘ wx
                  , ∈ₛ-∪∷←r {s₁ = vars l ∪∷ vars r} ∘ wy)
      (wf-constr-vars {lc = lc})

subs1 : Var → Term → List Constr → List Constr
subs1 v t = map (bimap (sub1 v t) (sub1 v t))

sub-rem : ∀ {x c t}
        → wf-tm c t
        → x ∈ c
        → ∀ u → wf-tm (rem x c) u
        → wf-tm (rem x c) (sub1 x u t)
sub-rem {x} {c} {t = `` v}    wt x∈ u wr =
  Dec.elim
    {C = λ q → wf-tm (rem x c) (if ⌊ q ⌋ then u else (`` v))}
    (λ _ → wr)
    (λ x≠v → λ w → rem-∈-≠ (contra (λ e → e ⁻¹ ∙ sng-∈ w) x≠v)
                           (wt w))
    (x ≟ v)
sub-rem {x} {c} {t = p ＋ q} wt x∈ u wr =
  [ sub-rem {t = p} (wt ∘ ∈ₛ-∪∷←l) x∈ u wr
  , sub-rem {t = q} (wt ∘ ∈ₛ-∪∷←r {s₁ = vars p}) x∈ u wr
  ]ᵤ ∘ ∈ₛ-∪∷→ {xs = vars (sub1 x u p)}
sub-rem {x} {c} {t = sy s}   wt x∈ u wr =
  false! ⦃ Refl-x∉ₛ[] ⦄

-- TODO can also be written as `v ∈ vars t`
occurs : Var → Term → 𝒰
occurs v (`` x)    = v ＝ x
occurs v (p ＋ q) = occurs v p ⊎ occurs v q
occurs v (sy _)   = ⊥

occurs? : Var → Term → Bool
occurs? v (`` x)    = v ==s x
occurs? v (p ＋ q) = occurs? v p or occurs? v q
occurs? v (sy _)   = false

occurs-reflects : ∀ {v} {t}
                → Reflects (occurs v t) (occurs? v t)
occurs-reflects {t = `` x}    = Reflects-String-Path
occurs-reflects {t = p ＋ q} =
  Reflects-⊎ ⦃ rp = occurs-reflects {t = p} ⦄ ⦃ rq = occurs-reflects {t = q} ⦄
occurs-reflects {t = sy s}   = ofⁿ id

occurs-dec : ∀ v t → Dec (occurs v t)
occurs-dec v t .does  = occurs? v t
occurs-dec v t .proof = occurs-reflects {v} {t}

occurs-wf-tm : ∀ {v c t} → wf-tm c t → ¬ occurs v t → wf-tm (rem v c) t
occurs-wf-tm {t = `` x}    w noc =
  λ ne → rem-∈-≠ ((contra (λ e → e ⁻¹ ∙ sng-∈ ne) noc)) (w ne)
occurs-wf-tm {t = p ＋ q} w noc =
  [ occurs-wf-tm
      {t = p} (w ∘ ∈ₛ-∪∷←l)
      (contra inl noc)
  , occurs-wf-tm
      {t = q} (w ∘ ∈ₛ-∪∷←r {s₁ = vars p})
      (contra inr noc)
  ]ᵤ ∘ ∈ₛ-∪∷→ {xs = vars p}
occurs-wf-tm {t = sy s}   w noc =
  false! ⦃ Refl-x∉ₛ[] ⦄

-- the unification algorithm

Unify-ty : ℕ × ℕ → 𝒰
Unify-ty (x , y) =
    (inp : Input)
  → wf-input inp
  → x ＝ sizeₛ (inp .fst)
  → y ＝ constr-sizes (inp .snd)
  → Maybe (SubC Var Term)

unify-neq-loop : ∀ {x y}
               → (□× Unify-ty) (x , y)

               → (inp : Input)
               → wf-input inp
               
               → (tl tr : Term)
               → wf-tm (inp .fst) tl
               → wf-tm (inp .fst) tr

               → x ＝ sizeₛ (inp .fst)
               → y ＝ constr-sizes ((tl , tr) ∷ inp .snd)
               → Maybe (SubC Var Term)
unify-neq-loop ih (ctx , ls) wf (`` xl) tr wl wr ex ey =
  Dec.rec
    (λ _ → nothing)
    (λ noc →
         map (insS xl tr) $
         Box×.call ih
           (inl (<-≤-trans (<-≤-trans <-ascend (=→≤ (size-∈ (wl (hereₛ refl)) ⁻¹))) (=→≤ (ex ⁻¹))))
           (rem xl ctx , subs1 xl tr ls)
           (all→map (all-map
              (λ where {x = l , r} (wl' , wr') →
                            (  sub-rem {t = l} wl' (wl (hereₛ refl)) tr (occurs-wf-tm {t = tr} wr noc)
                             , sub-rem {t = r} wr' (wl (hereₛ refl)) tr (occurs-wf-tm {t = tr} wr noc)))
              wf))
           refl refl)
    (occurs-dec xl tr)
unify-neq-loop {x} {y} ih (ctx , ls) wf (pl ＋ ql) (pr ＋ qr) wl wr ex ey =
  Box×.call ih
     prf-<
     (ctx , ls')
     prf-wf
     refl refl
  where
  ls' : List Constr
  ls' = (pl , pr) ∷ (ql , qr) ∷ ls
  prf-< : (sizeₛ ctx , constr-sizes ls') Box×.<× (x , y)
  prf-< =
    inr ( ex ⁻¹
          , <-≤-trans (≤-<-trans (=→≤ (+-assoc (tm-size pl + tm-size pr) (tm-size ql + tm-size qr) (constr-sizes ls)))
                                      (<-≤-+ {m = tm-size pl + tm-size pr + (tm-size ql + tm-size qr)}
                                             (<-trans (≤-<-trans (=→≤ (+-interchange (tm-size pl) (tm-size pr) (tm-size ql) (tm-size qr)))
                                                                 (≤-<-+ (=→≤ refl) <-ascend)) <-ascend)
                                             (=→≤ refl)))
                 (=→≤ (ey ⁻¹)))
  prf-wf : wf-input (ctx , ls')
  prf-wf =
      (wl ∘ ∈ₛ-∪∷←l , wr ∘ ∈ₛ-∪∷←l)
    ∷ (wl ∘ ∈ₛ-∪∷←r {s₁ = vars pl}, wr ∘ ∈ₛ-∪∷←r {s₁ = vars pr})
    ∷ wf
unify-neq-loop ih (ctx , ls) wf tl          (`` xr)     wl wr ex ey =
  Dec.rec
    (λ _ → nothing)
    (λ noc →
        map (insS xr tl) $
        Box×.call ih
           (inl (<-≤-trans (<-≤-trans <-ascend (=→≤ (size-∈ (wr (hereₛ refl)) ⁻¹))) (=→≤ (ex ⁻¹))))
           (rem xr ctx , subs1 xr tl ls)
           (all→map (all-map
              (λ where {x = l , r} (wl' , wr') →
                            (  sub-rem {t = l} wl' (wr (hereₛ refl)) tl (occurs-wf-tm {t = tl} wl noc)
                             , sub-rem {t = r} wr' (wr (hereₛ refl)) tl (occurs-wf-tm {t = tl} wl noc)))
              wf))
           refl refl)
    (occurs-dec xr tl)
unify-neq-loop ih (ctx , ls) wf _ _    wl wr ex ey = nothing

unify-loop : ∀[ □× Unify-ty ⇒ Unify-ty ]
unify-loop     ih (ctx , [])             wf ex ey = just empS
unify-loop {x} ih (ctx , (tl , tr) ∷ ls) ((wl , wr) ∷ wf) ex ey =
  if tl =? tr then
    Box×.call ih
             (inr (ex ⁻¹ , <-≤-trans (<-+-0lr (<-+-r (0<tm-size {t = tl}))) (=→≤ (ey ⁻¹))))
             (ctx , ls)
             wf
             refl refl
    else unify-neq-loop ih (ctx , ls) wf tl tr wl wr ex ey

unify : List Constr → Maybe (SubC Var Term)
unify lc =
  Box×.fix× Unify-ty
    unify-loop
    (constr-vars lc , lc) 
    wf-constr-vars
    refl refl
