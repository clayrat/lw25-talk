{-# OPTIONS --no-exact-split #-}
module SAT.DPLLans where

open import Prelude
open Variadics _
open import Meta.Show
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty hiding (_≠_)
open import Data.Bool as Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.List.Instances.Map.Properties
open import Data.Sum
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Induction.Nat.Strong as Box using (□_)

open import Data.List.NonEmpty as List⁺

open import ListSet
open import KVMapU
open import FMap

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete as LFSet

open import SAT.Formula0 using (Var)
open import SAT.Sem
open import SAT.Appl
open import SAT.Formula
open import SAT.NF
open import SAT.CNF
open import SAT.DPans

private variable
  A : 𝒰
  v : Var
  Γ Δ Ξ : Ctx

open KVOps
open KVOps2

posneg-count : CNF Γ → Lit Γ → ℕ
posneg-count cls l =
  let m = length $ filter (List.has          l) cls
      n = length $ filter (List.has $ negate l) cls
    in
  m + n

pair∈ : {A : 𝒰} (l : List A) → List (Σ[ a ꞉ A ] (a ∈ l))
pair∈ l = map-with-∈ l _,_

pair∈-[] : {A : 𝒰} {l : List A} → pair∈ l ＝ [] → l ＝ []
pair∈-[] {l = []}    _ = refl
pair∈-[] {l = x ∷ l} p = false! p

posneg-rule : CNF Γ → (ls : List (Lit Γ)) → ls ≠ []
            → Σ[ l ꞉ Lit Γ ] (l ∈ ls)
posneg-rule {Γ} c ls ne =
  let ml = List⁺.from-list (pair∈ ls) in
  Maybe.elim (λ m → ml ＝ m → Σ[ l ꞉ Lit Γ ] (l ∈ ls))
    (λ e → absurd (ne (pair∈-[] (from-list-nothing e))))
    (λ pvs _ → snd $ foldr₁ (min-on fst) $
               map⁺ (λ where (l , l∈) → posneg-count c l , l , l∈) pvs)
    ml
    refl

splitting-rule : (c : CNF Γ) → ⌞ any positive (unions c) ⌟
               → Lit Γ
splitting-rule {Γ} clauses prf =
  posneg-rule clauses (unions clauses)
    (λ e → false! $ subst (So ∘ any positive) e prf) .fst

dpll-loop : ∀[ □ CSI-ty ⇒ CSI-ty ]
dpll-loop ih {Γ} e c =
  Dec.rec
    (λ _ → just emp)
    (λ cn → Dec.rec
              (λ _ → nothing)
              (λ nc → Maybe.rec
                        ([ (λ where (pr , (z , z∈pr , z∈Γ) , c′) →
                                       map (λ m → List.rec m (λ l → upd (unlit l) (positive l)) pr) $
                                       Box.call ih
                                         (<-≤-trans
                                             (<-≤-trans
                                               (<-≤-trans
                                                 (<-+-0lr (size-∈->0 (∈-∩∷← z∈Γ (∈-list z∈pr))))
                                                 (=→≤ (+-comm (sizeₛ _) (sizeₛ _))))
                                               (=→≤ (size-minus-∩∷ {ys = LFSet.from-list (map unlit pr)})))
                                             (=→≤ (e ⁻¹)))
                                         refl c′)
                         , (λ pn →
                               let l = splitting-rule c
                                         (true→so! ⦃ Reflects-any-bool ⦄
                                           (resolution-pos c ((λ {l} → pn {l})) cn nc))
                                 in
                              map [ upd (unlit l) (positive l)
                                  , upd (unlit l) (negative l) ]ᵤ $
                              Box.call ih
                                (<-≤-trans
                                   (<-≤-trans
                                      (≤≃<suc $ ≤-refl)
                                      (=→≤ (size-∈ (unlit∈ l) ⁻¹)))
                                   (=→≤ (e ⁻¹)))
                                refl (unit-propagate l c)
                                <+>
                              Box.call ih
                                ((<-≤-trans
                                   (<-≤-trans
                                      (≤≃<suc $ ≤-refl)
                                      (=→≤ (size-∈ (subst (_∈ Γ) (unlit-negate {x = l}) (unlit∈ l)) ⁻¹)))
                                   (=→≤ (e ⁻¹))))
                                refl (unit-propagate (negate l) c))
                         ]ᵤ (affirmative-negative-rule c))
                        (λ where (l , c′) →
                                   map (upd (unlit l) (positive l)) $
                                   Box.call ih
                                      (<-≤-trans
                                         (<-≤-trans
                                            (≤≃<suc $ ≤-refl)
                                            (=→≤ (size-∈ (unlit∈ l) ⁻¹)))
                                         (=→≤ (e ⁻¹)))
                                      refl c′)
                        (one-lit-rule c))
              ([] ∈? c))
    (Dec-is-nil? {xs = c})

dpll : CNF Γ → Maybe SatMap
dpll = Box.fix CSI-ty dpll-loop refl

dpllsat : Formulaᵢ Γ → Maybe SatMap
dpllsat = dpll ∘ snd ∘ defcnfs

{-
main : Main
main =
  run $
  do let m1 = dpllsat (chk f1)
     put-str-ln $ "IXLLF1: " ++ₛ show (map showmp m1)
     put-str-ln $ "IXLLF1-test: " ++ₛ show (map (eval-map f1) m1)
     put-str-ln $ "IXLLF1-dtest: " ++ₛ show (map (eval-map (ers $ snd $ defcnf' $ chk f1)) m1)
     
     let m2 = dpllsat (chk f2)
     put-str-ln $ "IXLLF2: " ++ₛ show (map showmp m2)
     put-str-ln $ "IXLLF2-test: " ++ₛ show (map (eval-map f2) m2)
     put-str-ln $ "IXLLF2-dtest: " ++ₛ show (map (eval-map (ers $ snd $ defcnf' $ chk f2)) m2)
-}
