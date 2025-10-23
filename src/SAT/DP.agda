module ch2.Ix.DP where

open import Prelude
open Variadics _
open import Meta.Show
open import Meta.Effect hiding (_>>_) renaming (_>>=_ to _>>=ᵐ_)
open import Meta.Effect.Bind.State
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Dec as Dec
open import Data.Dec.Sigma as DecΣ
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.List as List renaming (has to hasₗ)
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.Sum
open import Data.String

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Induction.Nat.Strong as Box using (□_)

open import Data.List.NonEmpty as List⁺

open import ListSet

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete as LFSet

open import ch2.Formula using (Var)
open import ch2.Sem
open import ch2.Appl
open import ch2.Ix.Formula
open import ch2.Ix.NF
open import ch2.Ix.CNF

private variable
  A : 𝒰
  v : Var
  Γ : Ctx

-- no-ops propagating context strengthenings
avoid-var : {v : Var} → (l : Lit Γ) → v ≠ unlit l → Lit (rem v Γ)
avoid-var (Pos a m) ne = Pos a (rem-∈-≠ (ne ∘ _⁻¹) m)
avoid-var (Neg a m) ne = Neg a (rem-∈-≠ (ne ∘ _⁻¹) m)

avoid-ctx : (l : Lit Γ) → {Δ : Ctx} → unlit l ∉ Δ → Lit (minus Γ Δ)
avoid-ctx (Pos a m) l∉ = Pos a (∈-minus m l∉)
avoid-ctx (Neg a m) l∉ = Neg a (∈-minus m l∉)

opaque
  unfolding mapₛ
  avoid-var-clause : {v : Var}
                   → (c : Clause Γ)
                   → v ∉ mapₛ unlit (LFSet.from-list c)
                   → Clause (rem v Γ)
  avoid-var-clause []      v∉ = []
  avoid-var-clause (l ∷ c) v∉ =
      avoid-var l (fst $ ∉ₛ-uncons v∉)
    ∷ avoid-var-clause c (snd $ ∉ₛ-uncons v∉)

  avoid-ctx-clause : (f : Clause Γ)
                   → {Δ : Ctx}
                   → mapₛ unlit (LFSet.from-list f) ∥ₛ Δ
                   → Clause (minus Γ Δ)
  avoid-ctx-clause []      d = []
  avoid-ctx-clause (l ∷ f) d =
      avoid-ctx l (fst $ ∥ₛ-∷-l← d)
    ∷ avoid-ctx-clause f (snd $ ∥ₛ-∷-l← d)


-- ==== 1-LITERAL RULE aka BCP aka UNIT PROPAGATION ====

unit-clause : CNF Γ → Maybe (Lit Γ)
unit-clause  []               = nothing
unit-clause (        []  ∷ c) = unit-clause c
unit-clause ((x ∷    []) ∷ c) = just x
unit-clause ((x ∷ y ∷ f) ∷ c) = unit-clause c

{-
reflects-unit-clause : (c : CNF Γ) → ReflectsΣ (λ l → (l ∷ []) ∈ c) (unit-clause c)
reflects-unit-clause  []               = ofⁿ λ _ → false!
reflects-unit-clause (        []  ∷ c) =
  ReflectsΣ.dmap
    (λ _ → there)
    (λ _ → contra (any-¬here false!))
    (reflects-unit-clause c)
reflects-unit-clause ((x ∷    []) ∷ c) = ofʲ x (here refl)
reflects-unit-clause ((x ∷ y ∷ f) ∷ c) =
  ReflectsΣ.dmap
    (λ _ → there)
    (λ _ → contra (any-¬here (false! ∘ ∷-tail-inj)))
    (reflects-unit-clause c)

dec-unit-clause : (c : CNF Γ) → DecΣ (λ (l : Lit Γ) → (l ∷ []) ∈ c)
dec-unit-clause c .doesm  = unit-clause c
dec-unit-clause c .proofm = reflects-unit-clause c
-}

delete-var : (v : Var) → Clause Γ → Clause (rem v Γ)
delete-var v [] = []
delete-var v (l ∷ c) =
  Dec.rec
    (λ _ → delete-var v c)
    (λ ne → avoid-var l ne ∷ delete-var v c)
    (v ≟ unlit l)

-- TODO reformulate w/ Var ?

unit-propagate : (l : Lit Γ) → CNF Γ → CNF (rem (unlit l) Γ)
unit-propagate l []      = []
unit-propagate l (f ∷ c) =
  if hasₗ l f
    then unit-propagate l c
    else delete-var (unlit l) f ∷ unit-propagate l c

one-lit-rule : CNF Γ → Maybe (Σ[ l ꞉ Lit Γ ] (CNF (rem (unlit l) Γ)))
one-lit-rule clauses = map (λ l → l , unit-propagate l clauses) (unit-clause clauses)

{-
dec-one-lit-rule : (c : CNF Γ)
                 → DecΣ (λ (l : Lit Γ) → (l ∷ []) ∈ c × CNF (rem (unlit l) Γ))
dec-one-lit-rule c =
  DecΣ.dmap
    (λ l l∈ → l∈ , unit-propagate l c)
    (λ l → contra fst)
    (dec-unit-clause c)
-}

-- ==== AFFIRMATIVE-NEGATIVE aka PURE LITERAL RULE ====

delete-clauses : CNF Γ → (Δ : Ctx) → CNF (minus Γ Δ)
delete-clauses []      Δ = []
delete-clauses (f ∷ c) Δ =
  Dec.rec
    (λ d →   avoid-ctx-clause f (λ {x} → d {x}) -- ugh
           ∷ delete-clauses c Δ)
    (λ _ → delete-clauses c Δ)
    (LFSet.Dec-disjoint {s = mapₛ unlit $ LFSet.from-list f} {t = Δ})

affirmative-negative-rule : (c : CNF Γ) → (Σ[ Δ ꞉ Ctx ] (Δ ≬ Γ) × CNF (minus Γ Δ))
                                        ⊎ (∀ {l} → l ∈ unions c → negate l ∈ unions c)
affirmative-negative-rule clauses =
  let (neg0 , pos) = partition negative (unions clauses)
      neg = image negate neg0
      posonly = diff pos neg
      negonly = diff neg pos
      pr = union posonly (image negate negonly)
    in
  Dec.rec
    (λ pr=[] → inr $
               let (ww , qq) = union-empty pr=[]
                   pp = partition-filter {p = negative} {xs = unions clauses}
                 in
               λ {l} l∈ → Dec.rec
                            (λ p → ope→subset (filter-OPE {p = negative}) $
                                   subst (negate l ∈_) (ap fst pp) $
                                   image-∈ negate-inj $
                                   diff-⊆ ww $
                                   subst (_∈ pos) (negate-invol ⁻¹) $
                                   subst (l ∈_) (ap snd pp ⁻¹) $
                                   ∈-filter p l∈)
                            (λ np → ope→subset (filter-OPE {p = positive}) $
                                    subst (negate l ∈_) (ap snd pp) $
                                    diff-⊆ (image-empty qq) $
                                    ∈-image $
                                    subst (l ∈_) (ap fst pp ⁻¹) $
                                    ∈-filter (subst So (not-invol _) (not-so np)) l∈)
                            (Dec-So {b = positive l}))
    (λ pr≠[] →
         let Δ = mapₛ unlit (LFSet.from-list pr)
             (l , l∈pr) = length>0→Σ ([ id
                                      , (λ e → absurd (contra length=0→nil pr≠[] (e ⁻¹)))
                                      ]ᵤ (≤→<⊎= z≤))
             l∈Δ = ∈-mapₛ (∈-list l∈pr)
           in
         inl ( Δ , (unlit l , l∈Δ , map-unlit-⊆ pr l∈Δ)
              , delete-clauses clauses Δ))
    (Dec-is-nil? {xs = pr})

--- ==== RESOLUTION ====

-- TODO clause thm?

-- we deviate from the HoPLaAR algorithm here
-- by adding another `negate l ∈? c` check to drop trivial clauses from `pos`
-- to simplify termination by making the context always decreasing
resolve-part : (l : Lit Γ) → CNF Γ
             → CNF (rem (unlit l) Γ)
             × CNF (rem (unlit l) Γ)
             × CNF (rem (unlit l) Γ)
resolve-part l []       = [] , [] , []
resolve-part l (c ∷ cl) =
  let (p , n , o) = resolve-part l cl in
  Dec.rec
    (λ l∈c →
          Dec.rec
            (λ n∈c → p)
            (λ n∉c →   avoid-var-clause (remₗ l c)
                         (λ u∈ → rec! (λ m m∈ → [ (λ l=m → ∉-rem-= {xs = c}
                                                             (subst (_∈ remₗ l c)
                                                                    (l=m ⁻¹)
                                                                    (list-∈ m∈)))
                                                , (λ l=nm → n∉c (ope→subset filter-OPE
                                                                    (subst (_∈ remₗ l c)
                                                                           (negate-swap l=nm)
                                                                           (list-∈ m∈))))
                                                ]ᵤ ∘ unlit-eq)
                                      (mapₛ-∈ u∈))
                     ∷ p)
            (negate l ∈? c)
        , n
        , o)
    (λ l∉c →
       Dec.rec
         (λ n∈c →   p
                  ,   avoid-var-clause (remₗ (negate l) c)
                        (λ u∈ → rec! (λ m m∈ → [ (λ l=m → l∉c (ope→subset filter-OPE
                                                                  (subst (_∈ remₗ (negate l) c)
                                                                         (l=m ⁻¹)
                                                                         (list-∈ m∈))) )
                                                , (λ l=nm → ∉-rem-= {xs = c}
                                                             (subst (_∈ remₗ (negate l) c)
                                                                    (negate-swap l=nm)
                                                                    (list-∈ m∈)))
                                                ]ᵤ ∘ unlit-eq)
                                     (mapₛ-∈ u∈))
                    ∷ n
                  , o)
         (λ n∉c →   p
                  , n
                  ,   map-with-∈ c
                        (λ a a∈ → avoid-var a
                                    ([ (λ e → l∉c (subst (_∈ c) e a∈))
                                     , (λ e → n∉c (subst (_∈ c) e a∈))
                                     ]ᵤ ∘ unlit-eq ∘ _⁻¹))
                    ∷ o)
         (negate l ∈? c))
    (l ∈? c)

resolve-on : (l : Lit Γ) → CNF Γ → CNF (rem (unlit l) Γ)
resolve-on p clauses =
  let (pos , neg , other) = resolve-part p clauses
      res = filter nontrivial? $ map² union pos neg
    in
  union other res

resolution-blowup : CNF Γ → Lit Γ → ℕ × Lit Γ
resolution-blowup cls l =
  let m = length $ filter (List.has          l) cls
      n = length $ filter (List.has $ negate l) cls
    in
  (m · n ∸ m ∸ n , l)

resolution-rule : (c : CNF Γ) → ⌞ any positive (unions c) ⌟
                → Σ[ l ꞉ Lit Γ ] (CNF (rem (unlit l) Γ))
resolution-rule {Γ} clauses prf =
  let mpvs = List⁺.from-list $ filter positive (unions clauses) in
  Maybe.elim (λ m → mpvs ＝ m → Σ[ l ꞉ Lit Γ ] (CNF (rem (unlit l) Γ)))
    (λ e → absurd ((so-not $
                    List.none-filter {p = positive} {xs = unions clauses} $
                    from-list-nothing e) prf))
    (λ pvs _ → let p = snd $ foldr₁ (min-on fst) $
                       map⁺ (resolution-blowup clauses) pvs
                 in
               p , resolve-on p clauses)
    mpvs
    refl

resolution-pos : (c : CNF Γ)
               → (∀ {l} → l ∈ unions c → negate l ∈ unions c)
               → c ≠ []
               → [] ∉ c
               → Any (So ∘ positive) (unions c)
resolution-pos  []           _  cne _   = absurd (cne refl)
resolution-pos ([]      ∷ _) _  _   enc = absurd (enc (here refl))
resolution-pos ((l ∷ _) ∷ _) pn _   _   =
  Dec.rec
    here
    (  List.∈→Any (pn (here refl))
     ∘ not-so
     ∘ contra (subst So negative-negate))
    (Dec-So {b = positive l})

-- induction on context size
CSI-ty : ℕ → 𝒰
CSI-ty x = {Γ : Ctx} → x ＝ sizeₛ Γ
                     → CNF Γ → Bool

dp-loop : ∀[ □ CSI-ty ⇒ CSI-ty ]
dp-loop ih {Γ} e c =
  Dec.rec
    (λ _ → true)
    (λ cn → Dec.rec
              (λ _ → false)
              (λ nc → Maybe.rec
                        ([ (λ where (Δ , (z , z∈Δ , z∈Γ) , c′) →
                                       Box.call ih
                                         (<-≤-trans
                                             (<-≤-trans
                                               (<-≤-trans
                                                 (<-+-0lr (size-∈->0 (∈-∩∷← z∈Γ z∈Δ)))
                                                 (=→≤ (+-comm (sizeₛ _) (sizeₛ _))))
                                               (=→≤ (size-minus-∩∷ {ys = Δ})))
                                             (=→≤ (e ⁻¹)))
                                         refl c′)
                         , (λ pn →
                               let (l , rc) = resolution-rule c
                                                (true→so! ⦃ Reflects-any-bool ⦄
                                                  (resolution-pos c ((λ {l} → pn {l})) cn nc))
                                 in
                               Box.call ih
                                 (<-≤-trans
                                    (<-≤-trans
                                       (≤≃<suc $ ≤-refl)
                                       (=→≤ (rem-size-∈ (unlit∈ l) ⁻¹)))
                                    (=→≤ (e ⁻¹)))
                                 refl rc)
                         ]ᵤ (affirmative-negative-rule c))
                        (λ where (l , c′) →
                                    Box.call ih
                                      (<-≤-trans
                                         (<-≤-trans
                                            (≤≃<suc $ ≤-refl)
                                            (=→≤ (rem-size-∈ (unlit∈ l) ⁻¹)))
                                         (=→≤ (e ⁻¹)))
                                      refl c′)
                        (one-lit-rule c))
              ([] ∈? c))
    (Dec-is-nil? {xs = c})

dp : CNF Γ → Bool
dp = Box.fix CSI-ty dp-loop refl

dpsat : Formulaᵢ Γ → Bool
dpsat = dp ∘ snd ∘ defcnfs

dptaut : Formulaᵢ Γ → Bool
dptaut = not ∘ dpsat ∘ Not

{-
main : Main
main =
  run $
  do -- put-str-ln $ "prime 11  : " ++ₛ (show $ tautology $ prime 11)
     put-str-ln $ "prime(DP) 16: " ++ₛ ppFBᵢ dptaut (prime 16)
--     put-str-ln $ "prime 13DP: " ++ₛ ppFBᵢ dptaut (prime 13)
--     put-str-ln $ "prime 17DP: " ++ₛ ppFBᵢ dptaut (prime 17)
-}
