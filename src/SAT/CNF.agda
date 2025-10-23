{-# OPTIONS --no-exact-split #-}
module SAT.CNF where

open import Foundations.Prelude
open Variadics _
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Bool
open import Data.String
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
import Order.Diagram.Join.Reasoning as JR
open decminmax ℕ-dec-total
open JR ℕₚ max-joins

open import Induction.Nat.Strong as Box using (□_)

open import KVMapU

open import ListSet
open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Base 0ℓ

open import SAT.Formula0
open import SAT.Formula
open import SAT.NF

private variable
--  A : 𝒰
  Γ Δ : LFSet String

{-
_ : "(¬p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ ¬r) ∧ (p ∨ ¬q ∨ ¬r) ∧ (p ∨ q ∨ r)"
      ∈ (prettyF ∘ cnf <$> parseForm "p <=> (q <=> r)")
_ = hereₘ refl
-}

-- TODO psubst theorem

--mk-prop : State ℕ (Formulaᵢ ?)
--mk-prop .run-stateT n = suc n , Atom ("p_" ++ₛ show-ℕ n)

-- definitional CNF

open KVOps
open KVOps2

FM : Ctx → 𝒰
FM Γ = KVMap (Formulaᵢ Γ) (Formulaᵢ Γ × Formulaᵢ Γ)

-- should be computational no-op
wk-fm : Γ ⊆ Δ → FM Γ → FM Δ
wk-fm s = bimapm (wk s) wk-inj (λ where (x , y) → (wk s x , wk s y))

Trip : Ctx → 𝒰
Trip Γ = Formulaᵢ Γ × FM Γ × ℕ

-- induction on formula height
FHI-ty : ℕ → 𝒰
FHI-ty x = {Θ : Ctx} → (f : Formulaᵢ Θ) → x ＝ height f
                     → FM Θ → ℕ
                     → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Θ))

-- induction on a height of a product of formulas
FHI×-ty : ℕ → 𝒰
FHI×-ty x = {Θ : Ctx} → (p : Formulaᵢ Θ) → (q : Formulaᵢ Θ) → x ＝ 1 + max (height p) (height q)
                      → FM Θ → ℕ
                      → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Θ))

-- TODO try defining Box for Formulas?
-- we only need WF here for a recursive call on `wk _ q`
defstep : ({Θ : Ctx} → Formulaᵢ Θ → Formulaᵢ Θ → Formulaᵢ Θ)
        → ∀[ □ FHI-ty ⇒ FHI×-ty ]
defstep op ih {Θ} p q e defs n =
  let (Δp , (fm1 , defs1 , n1)) = Box.call ih (<-≤-trans (≤≃<suc $ l≤∪)
                                                         (=→≤ (e ⁻¹)))
                                              p refl defs n
      (Δq , (fm2 , defs2 , n2)) = Box.call ih (<-≤-trans (≤-<-trans (=→≤ (height-wk q))
                                                                    (≤≃<suc $ r≤∪ {x = height p}))
                                                         (=→≤ (e ⁻¹)))
                                              (wk (∈ₛ-∪∷←r {s₁ = Δp}) q) refl defs1 n1
      fm' = op (wk (∈ₛ-∪∷←r {s₁ = Δq}) fm1) fm2
    in
  Maybe.rec
    -- add a new atom
    (let x = "p_" ++ₛ show-ℕ n2
         v = Atom x (∈ₛ-∪∷←l {s₂ = Θ} (hereₛ {xs = Δq ∪∷ Δp} refl))
         s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((x ∷ Δq ∪∷ Δp) ∪∷ Θ)
         s = λ {x = z} → subst (z ∈_) (∪∷-assoc (x ∷ Δq)) ∘ thereₛ
       in
       x ∷ Δq ∪∷ Δp
     , v
     , (insertm (wk s fm') (v , Iff v (wk s fm')) $
        wk-fm s defs2)
     , suc n2)
    (λ (v , _) →
         let s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((Δq ∪∷ Δp) ∪∷ Θ)
             s = λ {x = z} → subst (z ∈_) (∪∷-assoc Δq)
           in
         (Δq ∪∷ Δp) , wk s v , wk-fm s defs2 , n2)
    (lookupm defs2 fm')

maincnf-loop : ∀[ □ FHI-ty ⇒ FHI-ty ]
maincnf-loop ih (And p q) e defs n = defstep And ih p q e defs n
maincnf-loop ih (Or  p q) e defs n = defstep Or ih p q e defs n
maincnf-loop ih (Iff p q) e defs n = defstep Iff ih p q e defs n
maincnf-loop ih  f        _ defs n = [] , (f , defs , n)

maincnf : Formulaᵢ Γ → FM Γ → ℕ
        → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ))
maincnf f defs n =
  Box.fix
    FHI-ty
    maincnf-loop
    f refl defs n

max-var-ix : String → String → ℕ → ℕ
max-var-ix pfx s n =
  let m = lengthₛ pfx
      l = lengthₛ s
    in
  if (l ≤? m) or not (substring 0 m s =ₛ pfx)
    then n
    else (Maybe.rec n (max n) $
          parseℕ $ substring m (l ∸ m) s)

mk-defcnf : (Formulaᵢ Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ)))
           → Formulaᵢ Γ            → Σ[ Δ ꞉ Ctx ] (CNF  (Δ ∪∷ Γ))
mk-defcnf fn fm =
  let fm' = nenf→form $ nenf0 fm
      n = suc (over-atomsᵢ (max-var-ix "p_") fm' 0)
      (Δ , fm'' , defs , _) = fn fm' emptym n
      deflist = map snd (valsm defs)
    in
  Δ , unions (simpcnf fm'' ∷ map simpcnf deflist)

defcnf : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf f =
  let Δc = mk-defcnf maincnf f in
  (Δc .fst , cnf→form (Δc . snd))

-- optimizations

-- WF again

subcnf : ({Θ : Ctx} → Formulaᵢ Θ → Formulaᵢ Θ → Formulaᵢ Θ)
       → ∀[ □ FHI-ty ⇒ FHI×-ty ]
subcnf op ih {Θ} p q e defs n =
  let (Δp , (fm1 , defs1 , n1)) = Box.call ih (<-≤-trans (≤≃<suc $ l≤∪)
                                                         (=→≤ (e ⁻¹)))
                                              p refl defs n
      (Δq , (fm2 , defs2 , n2)) = Box.call ih (<-≤-trans (≤-<-trans (=→≤ (height-wk q))
                                                                    (≤≃<suc $ r≤∪ {x = height p}))
                                                         (=→≤ (e ⁻¹)))
                                              (wk (∈ₛ-∪∷←r {s₁ = Δp}) q) refl defs1 n1
      s : (Δq ∪∷ Δp ∪∷ Θ) ⊆ ((Δq ∪∷ Δp) ∪∷ Θ)
      s = λ {x = z} → subst (z ∈_) (∪∷-assoc Δq)
    in
    Δq ∪∷ Δp
  , op (wk (s ∘ ∈ₛ-∪∷←r {s₁ = Δq}) fm1)
       (wk  s                      fm2)
  , wk-fm s defs2
  , n2

or-cnf-loop : ∀[ □ FHI-ty ⇒ FHI-ty ]
or-cnf-loop ih (Or p q) e defs n = subcnf Or ih p q e defs n
or-cnf-loop _   f       _ defs n = maincnf f defs n

or-cnf : Formulaᵢ Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ))
or-cnf f defs n =
  Box.fix
    FHI-ty
    or-cnf-loop
    f refl defs n

and-cnf-loop : ∀[ □ FHI-ty ⇒ FHI-ty ]
and-cnf-loop ih (And p q) e defs n = subcnf And ih p q e defs n
and-cnf-loop _   f        _ defs n = or-cnf f defs n

and-cnf : Formulaᵢ Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ))
and-cnf f defs n =
  Box.fix
    FHI-ty
    and-cnf-loop
    f refl defs n

defcnfs : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (CNF (Δ ∪∷ Γ))
defcnfs = mk-defcnf and-cnf

defcnf' : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf' f =
  let Δc = defcnfs f in
  (Δc .fst , cnf→form (Δc . snd))

-- 3-CNF

and-cnf3-loop : ∀[ □ FHI-ty ⇒ FHI-ty ]
and-cnf3-loop ih (And p q) e defs n = subcnf And ih p q e defs n
and-cnf3-loop _   f        _ defs n = maincnf f defs n

and-cnf3 : Formulaᵢ Γ → FM Γ → ℕ → Σ[ Δ ꞉ Ctx ] (Trip (Δ ∪∷ Γ))
and-cnf3 f defs n =
  Box.fix
    FHI-ty
    and-cnf3-loop
    f refl defs n

defcnf3 : Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))
defcnf3 f =
  let Δc = mk-defcnf and-cnf3 f in
  (Δc .fst , cnf→form (Δc . snd))

fm0 : String
fm0 = "p <=> (q <=> r)"

fm : String
fm = "(p \\/ (q /\\ ~r)) /\\ s"

{-
main : Main
main = run $ do put-str-ln $ ("naive cnf for " ++ₛ ppFᵢ id fm0)
                put-str-ln $ ppFᵢ cnf fm0
                let fms = ppFᵢ id fm
                put-str-ln $ ("def cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf fm
                put-str-ln $ ("optimized cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf' fm
                put-str-ln $ ("3-cnf for " ++ₛ fms)
                put-str-ln $ ppFΣᵢ defcnf3 fm
-}
