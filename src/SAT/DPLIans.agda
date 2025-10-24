{-# OPTIONS --no-exact-split #-}
module SAT.DPLIans where

open import Prelude
open import Foundations.Base
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
open import Data.Maybe.Correspondences.Unary.Any renaming (Any to Anyₘ ; any←map to any←mapₘ)
open import Data.Maybe.Correspondences.Unary.All renaming (All to Allₘ ; all-map to all-mapₘ ; all→map to all→mapₘ)
open import Data.Maybe.Instances.Bind.Properties
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Correspondences.Binary.Suffix
open import Data.List.Operations.Properties as List
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete renaming (rem to remₗ)
open import Data.List.Instances.Map.Properties
open import Data.Sum
open import Data.String
open import Data.Fin.Inductive
open import Data.Fin.Inductive.Operations
open import Data.Fin.Inductive.Operations.Properties
open import Data.Vec.Inductive hiding (_++_) renaming (replicate to replicateᵥ)
open import Data.Vec.Inductive.Operations hiding (_++_ ; replicate) renaming (lookup to lookupᵥ)
open import Data.Vec.Inductive.Operations.Properties renaming (map-++ to map-++ᵥ)
open import Data.Vec.Inductive.Instances.Map

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total
open import Order.Constructions.Lex.Vec

open import Induction.Nat.Strong as Box using (□_)
open import Induction.Nat.VLex as Box∷× using (□∷×_)

open import Data.List.NonEmpty as List⁺

open import ListSet
open import KVMapU
open import FMap -- TODO switch to KVMap

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
open import SAT.DPLLans

private variable
  A : 𝒰
  v : Var
  Γ Δ Ξ : Ctx

-- iterative

data Trailmix : 𝒰 where
  guessed deduced : Trailmix

tmxeq : Trailmix → Trailmix → Bool
tmxeq guessed guessed = true
tmxeq deduced deduced = true
tmxeq _ _ = false

is-guessed : Trailmix → 𝒰
is-guessed guessed = ⊤
is-guessed deduced = ⊥

is-guessed? : Trailmix → Bool
is-guessed? guessed = true
is-guessed? deduced = false

instance
  Reflects-is-guessed : ∀ {t} → Reflects (is-guessed t) (is-guessed? t)
  Reflects-is-guessed {t = guessed} = ofʸ tt
  Reflects-is-guessed {t = deduced} = ofⁿ id

guessed≠deduced : guessed ≠ deduced
guessed≠deduced p = subst is-guessed p tt

instance
  Reflects-Trailmix-Path : ∀ {t₁ t₂} → Reflects (t₁ ＝ t₂) (tmxeq t₁ t₂)
  Reflects-Trailmix-Path {(guessed)} {(guessed)} = ofʸ refl
  Reflects-Trailmix-Path {(guessed)} {(deduced)} = ofⁿ guessed≠deduced
  Reflects-Trailmix-Path {(deduced)} {(guessed)} = ofⁿ (guessed≠deduced ∘ _⁻¹)
  Reflects-Trailmix-Path {(deduced)} {(deduced)} = ofʸ refl

  Trailmix-is-discrete : is-discrete Trailmix
  Trailmix-is-discrete = reflects-path→is-discrete!

Trail : Ctx → 𝒰
Trail Γ = List (Lit Γ × Trailmix)

trail-lits : Trail Γ → List (Lit Γ)
trail-lits = map fst

trail-lits-++ : {tr1 tr2 : Trail Γ} → trail-lits (tr1 ++ tr2) ＝ trail-lits tr1 ++ trail-lits tr2
trail-lits-++ {tr1} {tr2} = map-++ fst tr1 tr2

trail-has : Trail Γ → Lit Γ → Bool
trail-has tr l = List.has l (trail-lits tr)

trail-pvars : Trail Γ → List (Var × Bool)
trail-pvars = map < unlit , positive > ∘ trail-lits

trail-pvars-++ : {tr1 tr2 : Trail Γ} → trail-pvars (tr1 ++ tr2) ＝ trail-pvars tr1 ++ trail-pvars tr2
trail-pvars-++ {tr1} {tr2} =
    ap (map < unlit , positive >) (trail-lits-++ {tr1 = tr1} {tr2 = tr2})
  ∙ map-++ < unlit , positive > (trail-lits tr1) (trail-lits tr2)

count-guessed : Trail Γ → ℕ
count-guessed = count (is-guessed? ∘ snd)

polarize : Ctx → LFSet (Var × Bool)
polarize Γ = mapₛ (_, true) Γ ∪∷ mapₛ (_, false) Γ

size-polarize : sizeₛ (polarize Γ) ＝ sizeₛ Γ + sizeₛ Γ
size-polarize =
    size-∪∷-∥ₛ
      (λ x∈t x∈f →
          rec! (λ xt xt∈ xte →
                 rec! (λ xf xf∈ xfe →
                        false! (ap snd xte ⁻¹ ∙ ap snd xfe))
                      (mapₛ-∈ x∈f))
               (mapₛ-∈ x∈t))
  ∙ ap² _+_ (size-map-inj (ap fst))
            (size-map-inj (ap fst))

-- TODO duplication but it's probably more hassle to fiddle with eliminators
trail-pvars⊆ : {tr : Trail Γ} → trail-pvars tr ⊆ polarize Γ
trail-pvars⊆ {Γ} {x = xl , false} x∈ =
  let (y , y∈ , ye) = List.map-∈Σ _ x∈ in
  ∈ₛ-∪∷←r {s₁ = mapₛ (_, true) Γ}
          (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y)))
trail-pvars⊆ {Γ} {x = xl , true}  x∈ =
  let (y , y∈ , ye) = List.map-∈Σ _ x∈ in
  ∈ₛ-∪∷←l (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y)))

-- TODO duplication again!
lit-set⊆ : {l : LFSet (Lit Γ)} → mapₛ < unlit , positive > l ⊆ polarize Γ
lit-set⊆ {Γ} {x = xl , false} x∈ =
  rec! (λ y y∈ ye →
           ∈ₛ-∪∷←r {s₁ = mapₛ (_, true) Γ}
                   (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y))))
    (mapₛ-∈ x∈)
lit-set⊆ {Γ} {x = xl , true}  x∈ =
  rec! (λ y y∈ ye →
           ∈ₛ-∪∷←l (∈-mapₛ (subst (_∈ Γ) (ap fst ye ⁻¹) (unlit∈ y))))
    (mapₛ-∈ x∈)

lit-set-size : {l : LFSet (Lit Γ)} → sizeₛ l ≤ 2 · sizeₛ Γ
lit-set-size {Γ} =
    =→≤ (size-map-inj unlit-positive-inj ⁻¹)
  ∙ size-⊆ lit-set⊆
  ∙ =→≤ (size-polarize ∙ ap (sizeₛ Γ +_) (+-zero-r (sizeₛ Γ) ⁻¹))

-- a proper trail mentions each literal once
Trail-Inv : Trail Γ → 𝒰
Trail-Inv = Uniq ∘ trail-pvars

emp-trailinv : Trail-Inv {Γ} []
emp-trailinv = []ᵘ

opaque
  unfolding Suffix
  suffix-trailinv : {tr0 tr : Trail Γ}
                  → Suffix tr0 tr
                  → Trail-Inv tr
                  → Trail-Inv tr0
  suffix-trailinv (pr , e) ti =
    ++→uniq (subst Uniq (ap trail-pvars (e ⁻¹) ∙ trail-pvars-++ {tr1 = pr}) ti) .snd .fst

trail-inv≤ : {tr : Trail Γ} → Trail-Inv tr → length tr ≤ 2 · sizeₛ Γ
trail-inv≤ {Γ} {tr} ti =
    =→≤ (  map-length ⁻¹ ∙ map-length ⁻¹
         ∙ size-unique ti ⁻¹
         ∙ ap sizeₛ (from-list-map {xs = trail-lits tr}) ⁻¹
         ∙ size-map-inj unlit-positive-inj)
  ∙ lit-set-size

backtrack : Trail Γ → Maybe (Lit Γ × Trail Γ)
backtrack []                   = nothing
backtrack ((_ , deduced) ∷ xs) = backtrack xs
backtrack ((p , guessed) ∷ xs) = just (p , xs)

All-deduced : Trail Γ → 𝒰
All-deduced tr = All (λ q → ¬ is-guessed (q. snd)) tr

backtrack-++-l : ∀ {pr tr : Trail Γ}
               → All-deduced pr
               → backtrack (pr ++ tr) ＝ backtrack tr
backtrack-++-l {pr = []}                  []     = refl
backtrack-++-l {pr = (l , guessed) ∷ pr} (d ∷ a) = absurd (d tt)
backtrack-++-l {pr = (l , deduced) ∷ pr} (d ∷ a) = backtrack-++-l a

Backtrack-suffix : Trail Γ → Lit Γ × Trail Γ → 𝒰
Backtrack-suffix {Γ} tr (p , tr′) =
  Σ[ pr ꞉ Trail Γ ] (  All-deduced pr
                     × (tr ＝ pr ++ (p , guessed) ∷ tr′))

opaque
  unfolding Suffix
  bsuffix→suffix : {tr tr' : Trail Γ} {p : Lit Γ}
                          → Backtrack-suffix {Γ} tr (p , tr') → Suffix ((p , guessed) ∷ tr') tr
  bsuffix→suffix (pr , _ , e) = (pr , e ⁻¹)

backtrack-suffix : {tr : Trail Γ} → Allₘ (Backtrack-suffix tr) (backtrack tr)
backtrack-suffix {tr = []}                 = nothing
backtrack-suffix {tr = (p , guessed) ∷ tr} =
  just ([] , [] , refl)
backtrack-suffix {tr = (p , deduced) ∷ tr} =
  all-mapₘ (λ where (pr , apr , e) →
                      ( (p , deduced) ∷ pr)
                      , id ∷ apr
                      , ap ((p , deduced) ∷_) e) $
  backtrack-suffix {tr = tr}

bsuffix→count-guessed : {tr tr' : Trail Γ} {p : Lit Γ}
                      → Backtrack-suffix tr (p , tr')
                      → count-guessed tr ＝ suc (count-guessed tr')
bsuffix→count-guessed {tr'} (pr , apr , e) =
    ap count-guessed e
  ∙ count-++ _ pr _
  ∙ ap (_+ (suc (count-guessed tr')))
       (none→count _ pr (all-map (not-so ∘ contra (so→true! ⦃ Reflects-is-guessed ⦄)) apr))

unassigned : CNF Γ → Trail Γ → List (Lit Γ)
unassigned cls trail =
  subtract
    (unions (image (image abs) cls))
    (image (abs ∘ fst) trail)

unassigned-∉ : {c : CNF Γ} {tr : Trail Γ} {l : Lit Γ}
             → l ∈ unassigned c tr
             → l ∉ trail-lits tr × negate l ∉ trail-lits tr
unassigned-∉ {c} {tr} {l} l∈u =
  let (l∈u , l∉ta) = subtract-∈ l∈u
      (ls , ls∈ , l∈′) = unions-∈ l∈u
      (zs , zs∈ , lse) = image-∈Σ {xs = c} ls∈
      (q , q∈ , zse) = image-∈Σ {xs = zs} (subst (l ∈_) lse l∈′)
    in
    (λ l∈t → l∉ta $
             ⊆-nub {R = λ _ _ → Reflects-lit Reflects-String-Path} $
             subst (_∈ map (abs ∘ fst) tr) (abs-idem ∙ zse ⁻¹) $
             subst (abs (abs q) ∈_) (happly map-pres-comp tr ⁻¹) $
             List.∈-map _ $
             subst (_∈ trail-lits tr) zse l∈t)
  , (λ nl∈t → l∉ta $
              ⊆-nub {R = λ _ _ → Reflects-lit Reflects-String-Path} $
              subst (_∈ map (abs ∘ fst) tr) (abs-negate ∙ abs-idem ∙ zse ⁻¹) $
              subst (abs (negate (abs q)) ∈_) (happly map-pres-comp tr ⁻¹) $
              List.∈-map abs $
              subst (λ q → negate q ∈ trail-lits tr) zse nl∈t)

-- TODO I'll drop the lookup structure as our kvmaps are lists internally anyway
-- and it's a hassle to keep it in sync with the trail

is-fresh-unit-clause : Trail Γ → Clause Γ → Bool
is-fresh-unit-clause tr []          = false
is-fresh-unit-clause tr (l ∷ [])    = not (trail-has tr l)
is-fresh-unit-clause tr (_ ∷ _ ∷ _) = false

fresh-unit-clause-prop : {tr : Trail Γ} {c : Clause Γ}
                       → ⌞ is-fresh-unit-clause tr c ⌟
                       → Σ[ l ꞉ Lit Γ ] (c ＝ l ∷ []) × (l ∉ trail-lits tr)
fresh-unit-clause-prop {tr} {c = l ∷ []} ifuc =
  l , refl , so→false! ifuc

tail-of : Lit Γ → List (Lit Γ) → List (Lit Γ)
tail-of x ls = List.tail (span (λ q → not (Lit-= _=?_ q x)) ls .snd)

tail-of-∷ : {z : Lit Γ} {xs : List (Lit Γ)}
          → tail-of z (z ∷ xs) ＝ xs
tail-of-∷ {z} =
  ap (λ q → List.tail (q .snd))
     (if-false $
      subst So (not-invol _ ⁻¹) $
      true→so! ⦃ Reflects-lit Reflects-String-Path {lx = z} ⦄ refl)

tail-of-++-r : {z : Lit Γ} {xs ys : List (Lit Γ)}
             → z ∉ xs → tail-of z (xs ++ ys) ＝ tail-of z ys
tail-of-++-r {z} {xs} z∉ =
  ap (λ q → List.tail (q .snd))
     (span-++-r xs $
      all-map (λ {x} →
                    not-so
                  ∘ contra (  _⁻¹
                            ∘ so→true! ⦃ Reflects-lit Reflects-String-Path {lx = x} ⦄)) $
      ¬Any→All¬ z∉)

-- a proper trail only guesses each variable once
Trail-Inv2 : Trail Γ → 𝒰
Trail-Inv2 tr =
  ∀ x → (x , guessed) ∈ tr
      → negate x ∉ tail-of x (trail-lits tr)

emp-trailinv2 : Trail-Inv2 {Γ = Γ} []
emp-trailinv2 x = false!

guessed-vars : Trail Γ → List Var
guessed-vars = map unlit ∘ trail-lits ∘ filter (is-guessed? ∘ snd)

-- TODO should this be Inv2 instead?
-- TODO copypaste
uniq-guessed : {tr : Trail Γ}
             → Trail-Inv tr → Trail-Inv2 tr
             → Uniq (guessed-vars tr)
uniq-guessed {tr = []}                  ti1        ti2 = []ᵘ
uniq-guessed {tr = (x , guessed) ∷ tr} (ni ∷ᵘ ti1) ti2 =
  contra (λ x∈ → let (y , y∈ , ye) = List.map-∈Σ unlit x∈
                     ((z , ztr) , z∈ , ze) = List.map-∈Σ fst y∈
                   in
                 [ (λ y=x → List.∈-map _ $
                            subst (_∈ map fst tr) (ze ⁻¹ ∙ y=x) $
                            List.∈-map _ $
                            ope→subset filter-OPE z∈)
                 , (λ y=nx → absurd (ti2 x (here refl) $
                                     subst (negate x ∈_)
                                           (tail-of-∷ {z = x} {xs = trail-lits tr} ⁻¹) $
                                     subst (_∈ trail-lits tr)
                                           (ze ⁻¹ ∙ y=nx) $
                                     List.∈-map _ $
                                     ope→subset filter-OPE z∈))
                 ]ᵤ (unlit-eq {x = y} {y = x} (ye ⁻¹)))
         ni ∷ᵘ uniq-guessed ti1
                  λ z z∈ →
                     subst (negate z ∉_)
                           (tail-of-++-r
                              (¬any-∷
                                 (contra (λ z=x → List.∈-map _ $
                                                  List.∈-map _ $
                                                  subst (λ q → (q , guessed) ∈ tr) z=x z∈)
                                         ni)
                                 false!)) $
                     ti2 z (there z∈)
uniq-guessed {tr = (x , deduced) ∷ tr} (ni ∷ᵘ ti1)  ti2 =
  uniq-guessed ti1
    λ z z∈ →
       subst (negate z ∉_)
             (tail-of-++-r
                (¬any-∷
                   (contra (λ z=x → List.∈-map _ $
                                    List.∈-map _ $
                                    subst (λ q → (q , guessed) ∈ tr) z=x z∈)
                           ni)
                   false!)) $
       ti2 z (there z∈)

count-guessed-size : {tr : Trail Γ}
                   → Trail-Inv tr → Trail-Inv2 tr
                   → count-guessed tr ≤ sizeₛ Γ
count-guessed-size {Γ} {tr} ti1 ti2 =
    =→≤ (  length-filter _ tr ⁻¹
         ∙ map-length {f = fst} ⁻¹
         ∙ map-length {f = unlit} ⁻¹
         ∙ size-unique (uniq-guessed ti1 ti2) ⁻¹)
  ∙ size-⊆ λ x∈ →
              let x∈' = list-∈ {xs = guessed-vars tr} x∈
                  (y , y∈ , ye) = List.map-∈Σ unlit x∈'
                in
              subst (_∈ Γ) (ye ⁻¹) (unlit∈ y)

USP-suffix : Trail Γ → Trail Γ → 𝒰
USP-suffix {Γ} tr' tr =
  Σ[ pr ꞉ Trail Γ ] (  All-deduced pr
                     × (tr' ＝ pr ++ tr))

uspsuffix→len : {tr tr' : Trail Γ}
              → USP-suffix tr' tr
              → length tr ≤ length tr'
uspsuffix→len {tr} (pr , a , e) =
    ≤-+-l
  ∙ =→≤ (  ++-length pr tr ⁻¹
         ∙ ap length (e ⁻¹) )

uspsuffix→count-guessed : {tr tr' : Trail Γ}
                        → USP-suffix tr' tr
                        → count-guessed tr ＝ count-guessed tr'
uspsuffix→count-guessed {tr} (pr , a , e) =
    ap (_+ count-guessed tr)
       (none→count _ pr
          (all-map false→so! a) ⁻¹)
  ∙ count-++ _ pr tr ⁻¹
  ∙ ap count-guessed (e ⁻¹)

Rejstk : Ctx → 𝒰
Rejstk Γ = Vec (LFSet (Lit Γ)) (sizeₛ Γ)

-- iterated backtrack
drop-guessed : Trail Γ → ℕ → Trail Γ
drop-guessed tr 0 = tr
drop-guessed tr (suc n) =
  Maybe.rec
    []
    (λ ptr → drop-guessed (ptr .snd) n)
    (backtrack tr)

drop-guessed-++-l : ∀ {pr tr : Trail Γ} {n}
                  → All-deduced pr
                  → 0 < n
                  → drop-guessed (pr ++ tr) n ＝ drop-guessed tr n
drop-guessed-++-l {n = zero} a nz = false! nz
drop-guessed-++-l {n = suc n} a _ = ap (Maybe.rec [] (λ ptr → drop-guessed (ptr .snd) n)) (backtrack-++-l a)

Rejstk-Inv : Rejstk Γ → Trail Γ → 𝒰
Rejstk-Inv {Γ} rj tr =
  ∀ x (f : Fin (sizeₛ Γ))
      → x ∈ lookupᵥ rj f
      → negate x ∈ (trail-lits $ drop-guessed tr (count-guessed tr ∸ fin→ℕ f))

emp-rejstkinv : Rejstk-Inv (replicateᵥ (sizeₛ Γ) []) []
emp-rejstkinv x f x∈ =
  false! ⦃ Refl-x∉ₛ[] ⦄ $
  subst (x ∈ₛ_) (lookup-replicate f) x∈

bump-at-fun : ∀ {n} → Lit Γ → Vec (LFSet (Lit Γ)) n → ℕ → Fin n → LFSet (Lit Γ)
bump-at-fun l r k f =
  if fin→ℕ f <? k
    then lookupᵥ r f
    else if fin→ℕ f == k
           then l ∷ lookupᵥ r f
           else []

bump-at : Fin (sizeₛ Γ) → Lit Γ → Rejstk Γ → Rejstk Γ
bump-at f l r =
  tabulate (bump-at-fun l r (fin→ℕ f))

USP-ty : ℕ → 𝒰
USP-ty x = {Γ : Ctx}
         → CNF Γ → (tr : Trail Γ)
         → x ＝ 2 · sizeₛ Γ ∸ length tr
         → Trail-Inv tr
         → Trail-Inv2 tr
         → CNF Γ × (Σ[ tr' ꞉ Trail Γ ] (  Trail-Inv tr'
                                        × Trail-Inv2 tr'
                                        × USP-suffix tr' tr))

unit-subpropagate-loop : ∀[ □ USP-ty ⇒ USP-ty ]
unit-subpropagate-loop {x} ih {Γ} cls tr e ti ti2 =
  Dec.rec (λ _ → cls' , tr , ti , ti2 , [] , [] , refl)
          (λ ne → let (cls0 , tr0 , ti0 , ti20 , (pr0 , a0 , e0)) =
                          Box.call ih (prf ne) cls' tr' refl ti' ti2'
                  in ( cls0 , tr0 , ti0 , ti20
                     , pr0 ++ map (_, deduced) newunits
                     , all-++ a0 (all→map (all-trivial (λ _ → id)))
                     , e0 ∙ ++-assoc pr0 _ tr ⁻¹))
          (Dec-is-nil? {xs = newunits})
  where
  cls' = map (filter (not ∘ trail-has tr ∘ negate)) cls
  newunits = unions (filter (is-fresh-unit-clause tr) cls')
  tr' = map (_, deduced) newunits ++ tr

  -- propositional (proof) part
  -- TODO streamline
  ti' : Trail-Inv tr'
  ti' = subst Uniq (happly map-pres-comp tr') $
        subst Uniq (map-++ (< unlit , positive > ∘ fst) _ tr ⁻¹) $
        subst (λ q → Uniq (q (map (_, deduced) newunits) ++ q tr)) (map-pres-comp {f = fst} {g = < unlit , positive >} ⁻¹) $
        subst (λ q → Uniq (map < unlit , positive > q ++ trail-pvars tr)) (happly map-pres-comp newunits) $
        subst (λ q → Uniq (q ++ trail-pvars tr)) (happly map-pres-comp newunits) $
        uniq→++
          (uniq-map unlit-positive-inj $
           nub-unique {R = λ _ _ → Lit-is-discrete .proof}
                      {xs = concat (filter (is-fresh-unit-clause tr) cls')})
          ti
          λ {x} x∈nu x∈tr →
           let (z , z∈ , ze) = List.map-∈Σ < unlit , positive > x∈nu
               (zs , zs∈ , z∈') = ∈-concat {xss = filter (is-fresh-unit-clause tr) cls'}
                                  (ope→subset {ys = concat (filter (is-fresh-unit-clause tr) cls')}
                                    (nub-ope {cmp = _=?_}) z∈)
               (fzs , _) = filter-∈ {p = is-fresh-unit-clause tr} {xs = cls'} zs∈
               (lz , zse , ll) = fresh-unit-clause-prop {c = zs} fzs
              in
            ll (map-∈ _ unlit-positive-inj $
                subst (_∈ trail-pvars tr)
                      (ze ∙ ap < unlit , positive > (any-¬there false! (subst (z ∈_) zse z∈')))
                      x∈tr)

  ti2' : Trail-Inv2 tr'
  ti2' x x∈ =
    subst (λ q → negate x ∉ tail-of x q)
           (trail-lits-++ {tr1 = map (_, deduced) newunits} {tr2 = tr} ⁻¹) $
    [ (λ am → absurd (guessed≠deduced $ ap snd $ List.Any→Σ∈ (any←map am) .snd .snd))
    , (λ x∈' →
          subst (negate x ∉_)
                (tail-of-++-r
                   (λ x∈m → ++→uniq (subst Uniq
                                           (trail-pvars-++ {tr1 = map (_, deduced) newunits} {tr2 = tr})
                                           ti')
                              .snd .snd
                              (List.∈-map _ x∈m)
                              (List.∈-map _ (List.∈-map _ x∈'))) ⁻¹) $
          ti2 x x∈')
    ]ᵤ (any-split x∈)

  prf : newunits ≠ [] → 2 · sizeₛ Γ ∸ length tr' < x
  prf ne =
    <-≤-trans
      (<-∸-2l-≃ (trail-inv≤ ti') ⁻¹ $
       <-≤-trans
         (<-+-0lr (<-≤-trans
                     (≱→< $ contra (length=0→nil ∘ ≤0→=0) ne)
                     (=→≤ (map-length ⁻¹))))
         (=→≤ (++-length _ tr ⁻¹)))
      (=→≤ (e ⁻¹))

unit-propagate-iter : {Γ : Ctx}
                    → CNF Γ → (tr : Trail Γ) → Trail-Inv tr → Trail-Inv2 tr
                    → CNF Γ × (Σ[ tr' ꞉ Trail Γ ] (  Trail-Inv tr'
                                                   × Trail-Inv2 tr'
                                                   × USP-suffix tr' tr))
unit-propagate-iter cls tr ti ti2 =
  Box.fix USP-ty unit-subpropagate-loop cls tr refl ti ti2

trail→map : Trail Γ → SatMap
trail→map =
  List.rec emp λ (l , _) → upd (unlit l) (positive l)

TSI-ty : {Γ : Ctx} → Vec ℕ (sizeₛ Γ) × ℕ → 𝒰
TSI-ty {Γ} (x , y) =
    (tr : Trail Γ)
  → (ti : Trail-Inv tr)
  → (ti2 : Trail-Inv2 tr)
  → (rj : Rejstk Γ)
  → Rejstk-Inv rj tr
  → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
  → y ＝ 2 · sizeₛ Γ ∸ length tr
  → Maybe SatMap

dpli-loop-backtrack : ∀ {x y}
                    → (□∷× TSI-ty) (x , y)
                    → (tr : Trail Γ)
                    → (ti : Trail-Inv tr)
                    → (ti2 : Trail-Inv2 tr)
                    → (rj : Rejstk Γ)
                    → Rejstk-Inv rj tr
                    → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
                    → y ＝ 2 · sizeₛ Γ ∸ length tr

                    → (p : Lit Γ)
                    → (trr : Trail Γ)
                    → backtrack tr ＝ just (p , trr)

                    → Maybe SatMap
dpli-loop-backtrack {Γ} {x} {y} ih tr ti ti2 rj ri ex ey p trr eb =
  Box∷×.call ih prf
    ((negate p , deduced) ∷ trr)
    ti'' ti2''
    (bump-at bfin p rj)
    ri''
    refl refl
  where
  bsf : Backtrack-suffix tr (p , trr)
  bsf = all-unjust (subst (λ q → Allₘ (Backtrack-suffix tr) q)
                          eb
                          (backtrack-suffix {tr = tr}))
  bcg : count-guessed tr ＝ suc (count-guessed trr)
  bcg = bsuffix→count-guessed bsf
  cg< : count-guessed trr < sizeₛ Γ
  cg< = <≃suc≤ $   =→≤ (bcg ⁻¹) ∙ count-guessed-size ti ti2
  bfin : Fin (sizeₛ Γ)
  bfin = ℕ→fin (count-guessed trr) cg<
  pr = bsf .fst
  etr = bsf .snd .snd ⁻¹
  udptr :   Uniq (trail-pvars pr)
          × Uniq (trail-pvars ((p , guessed) ∷ trr))
          × (trail-pvars pr ∥ trail-pvars ((p , guessed) ∷ trr))
  udptr = ++→uniq {xs = trail-pvars pr}
                  (subst Uniq
                         (trail-pvars-++ {tr1 = pr}) $
                   subst (Uniq ∘ trail-pvars)
                         (etr ⁻¹)
                         ti)
  uptr = udptr .snd .fst
  dtr = udptr .snd .snd
  ti'' : Trail-Inv ((negate p , deduced) ∷ trr)
  ti'' = contra (map-∈ _ unlit-positive-inj)
                (λ np∈ → ti2 p (subst ((p , guessed) ∈_)
                                       etr
                                       (any-++-r (here refl)))
                                (subst (λ q → negate p ∈ₗ tail-of p (trail-lits q))
                                       etr $
                                 subst (λ q → negate p ∈ (tail-of p q))
                                       (trail-lits-++ {tr1 = pr} ⁻¹) $
                                 subst (negate p ∈_)
                                       (tail-of-++-r (λ p∈ → dtr (List.∈-map _ p∈)
                                                                 (here refl)) ⁻¹) $
                                 subst (negate p ∈_)
                                       (tail-of-∷ {z = p} ⁻¹)
                                       np∈))
         ∷ᵘ (snd $ uniq-uncons $ suffix-trailinv (bsuffix→suffix bsf) ti)
  ti2'' : Trail-Inv2 ((negate p , deduced) ∷ trr)
  ti2'' z z∈ =
    let z∈' = any-¬here (λ e → absurd (guessed≠deduced (ap snd e))) z∈ in
    contra (λ n∈ → subst (λ q → negate z ∈ tail-of z (trail-lits q))
                         etr $
                   subst (λ q → negate z ∈ tail-of z q)
                         (trail-lits-++ {tr1 = pr} ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = trail-lits pr}
                                       (λ z∈ → dtr (List.∈-map _ z∈)
                                                   (List.∈-map _ $ there $ List.∈-map _ z∈')) ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = p ∷ []}
                                       (¬any-∷ (contra (λ z=p → List.∈-map _ $
                                                                List.∈-map _ $
                                                                subst (λ q → (q , guessed) ∈ trr)
                                                                      z=p
                                                                      z∈')
                                                       (uniq-uncons uptr .fst))
                                               false!) ⁻¹) $
                   subst (negate z ∈_)
                         (tail-of-++-r {xs = negate p ∷ []}
                                       (¬any-∷ (contra (λ z=np → List.∈-map _ $
                                                                 List.∈-map _ $
                                                                 subst (λ q → (q , guessed) ∈ trr)
                                                                       z=np
                                                                       z∈')
                                                       (uniq-uncons ti'' .fst) )
                                               false!)) $
                   n∈) $
    ti2 z $
    subst ((z , guessed) ∈_)
          etr $
    any-++-r $
    there z∈'
  ri'' : Rejstk-Inv (bump-at bfin p rj) ((negate p , deduced) ∷ trr)
  ri'' x f x∈ =
    Dec.elim
      {C = λ q → x ∈ₛ (if ⌊ q ⌋
                         then lookupᵥ rj f
                         else if fin→ℕ f == fin→ℕ bfin
                                then p ∷ lookupᵥ rj f
                                else [])
               → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr)
                                                     (count-guessed trr ∸ fin→ℕ f))}
      (λ lt x∈ →
           let lt' = <-≤-trans lt (=→≤ (ℕ→fin→ℕ _ cg<)) in
           subst (λ q → negate x ∈ trail-lits q)
                  (drop-guessed-++-l {pr = (negate p , deduced) ∷ []} {tr = trr} {n = count-guessed trr ∸ fin→ℕ f}
                     (id ∷ [])
                     (∸>0≃> ⁻¹ $ lt') ⁻¹) $
           subst (λ q → negate x ∈ trail-lits (Maybe.rec [] (λ ptr → drop-guessed (ptr .snd) (count-guessed trr ∸ fin→ℕ f)) q))
                 eb $
           subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                     (ap (  _∸ fin→ℕ f) bcg
                          ∙ +∸-assoc 1 (count-guessed trr) (fin→ℕ f)
                              (<-weaken _ _ lt') ⁻¹) $
           ri x f x∈)
      (λ ge →
           Dec.elim
               {C = λ q → x ∈ₛ (if ⌊ q ⌋ then p ∷ lookupᵥ rj f else [])
                        → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr)
                                                              (count-guessed trr ∸ fin→ℕ f))}
               (λ e →
                  let e' = e ∙ ℕ→fin→ℕ _ cg< in
                  [ (λ x=p →
                        subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr) q))
                               (≤→∸=0 (=→≤ (e' ⁻¹)) ⁻¹) $
                        here (ap negate x=p))
                  , (λ x∈' →
                        subst (λ q → negate x ∈ trail-lits (drop-guessed ((negate p , deduced) ∷ trr) q))
                               (≤→∸=0 (=→≤ (e' ⁻¹)) ⁻¹) $
                        there $
                        subst (λ q → negate x ∈ trail-lits (Maybe.rec [] snd q))
                              eb $
                        subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                              (ap (  _∸ fin→ℕ f) bcg
                                   ∙ +∸-assoc 1 (count-guessed trr) (fin→ℕ f)
                                       (=→≤ e') ⁻¹
                                   ∙ ap suc (≤→∸=0 (=→≤ (e' ⁻¹)))
                                   ∙ +-zero-r 1) $
                        ri x f x∈')
                  ]ᵤ ∘ ∈ₛ-∷→)
               (λ ne → false! ⦃ Refl-x∉ₛ[] ⦄)
               (ℕ-is-discrete {x = fin→ℕ f} {y = fin→ℕ bfin}))
      (<-dec {x = fin→ℕ f} {x = fin→ℕ bfin})
      (subst (x ∈_)
             (lookup-tabulate {f = bump-at-fun p rj (fin→ℕ bfin)} f)
             x∈)
  prf : (  map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                (bump-at bfin p rj)
         , 2 · sizeₛ Γ ∸ suc (length trr))
          Box∷×.<∷× (x , y)
  prf =
    (inl (subst (Vec-lex< _<_
                (mapᵥ (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                      (bump-at bfin p rj)))
              (ex ⁻¹) $
        Vec-lex<-prefix-lup bfin
          (λ j jlt →
               lookup-map {xs = bump-at bfin p rj} j
             ∙ ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                  (  lookup-tabulate j
                   ∙ if-true (true→so! jlt))
             ∙ lookup-map {xs = rj} j ⁻¹)
          (≤-<-trans
            (=→≤ (lookup-map {xs = bump-at bfin p rj} bfin))
            (<-≤-trans
               (≤-<-trans
                 (=→≤ (ap (λ q → 2 · sizeₛ Γ ∸ sizeₛ q)
                          (  lookup-tabulate bfin
                           ∙ if-false (false→so! (<-irr {n = fin→ℕ bfin}))
                           ∙ if-true (true→so! (the (fin→ℕ bfin ＝ fin→ℕ bfin) refl)))))
                 (<-∸-2l-≃ {m = 2 · sizeₛ Γ} {n = sizeₛ (p ∷ lookupᵥ rj bfin)} {p = sizeₛ (lookupᵥ rj bfin)}
                           lit-set-size ⁻¹ $
                 <-≤-trans <-ascend
                   (=→≤ (  ap (suc ∘ sizeₛ)
                              (rem-∉-eq
                                 (λ p∈s →
                                     ti2 p
                                       (subst ((p , guessed) ∈_)
                                              etr
                                              (any-++-r (here refl)))
                                       (subst (λ q → negate p ∈ tail-of p (trail-lits q))
                                              etr $
                                        subst (λ q → negate p ∈ tail-of p q)
                                              (trail-lits-++ {tr1 = pr} ⁻¹) $
                                        subst (negate p ∈_)
                                              (tail-of-++-r (λ p∈ → dtr (List.∈-map _ p∈)
                                                            (here refl)) ⁻¹) $
                                        subst (negate p ∈_)
                                              (tail-of-∷ {z = p} ⁻¹) $
                                        subst (λ q → negate p ∈ trail-lits (Maybe.rec [] (λ ptr → ptr .snd) q))
                                               eb $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr q))
                                              (+-cancel-∸-r 1 (count-guessed trr)) $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr (q ∸ count-guessed trr)))
                                              bcg $
                                        subst (λ q → negate p ∈ trail-lits (drop-guessed tr (count-guessed tr ∸ q)))
                                              (ℕ→fin→ℕ (count-guessed trr) cg<) $
                                        ri p bfin p∈s)
                                        )
                                 ⁻¹)
                         ∙ size-∷ ⁻¹))))
               (=→≤ (lookup-map {xs = rj} bfin ⁻¹))))))

dpli-loop-guess : (cls : CNF Γ)
                → ∀ {x y}
                → (□∷× TSI-ty) (x , y)
                → (tr : Trail Γ)
                → (ti : Trail-Inv tr)
                → (ti2 : Trail-Inv2 tr)
                → (rj : Rejstk Γ)
                → Rejstk-Inv rj tr
                → x ＝ map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
                → y ＝ 2 · sizeₛ Γ ∸ length tr

                → (cls' : CNF Γ)
                → (tr'  : Trail Γ)
                → Trail-Inv tr'
                → Trail-Inv2 tr'
                → USP-suffix tr' tr
                → (ps : List (Lit Γ))
                → ps ≠ []
                → ps ＝ unassigned cls tr'

                → Maybe SatMap
dpli-loop-guess {Γ} cls {x} {y} ih tr ti ti2 rj ri ex ey cls' tr' ti' ti2' us' ps ne eps =
  Box∷×.call ih prf
    ((p , guessed) ∷ tr')
    ti''
    ti2''
    rj
    ri''
    refl refl
  where
  pp∈ : Σ[ l ꞉ Lit Γ ] (l ∈ ps)
  pp∈ = posneg-rule cls' ps ne
  p = pp∈ .fst
  p∈ = pp∈ .snd
  pnp∉ : p ∉ trail-lits tr' × negate p ∉ trail-lits tr'
  pnp∉ = unassigned-∉ {c = cls} (subst (p ∈_) eps p∈)
  p∉ = pnp∉ .fst
  np∉ = pnp∉ .snd
  ti'' : Trail-Inv ((p , guessed) ∷ tr')
  ti'' = contra (map-∈ _ unlit-positive-inj) p∉ ∷ᵘ ti'
  ti2'' : Trail-Inv2 ((p , guessed) ∷ tr')
  ti2'' z z∈ =
    [ (λ z=p' → subst (λ q → negate z ∉ tail-of z (q ∷ trail-lits tr'))
                      (ap fst z=p') $
                subst (negate z ∉_)
                      (tail-of-∷ {z = z} {xs = trail-lits tr'} ⁻¹) $
                subst (λ q → negate q ∉ trail-lits tr')
                      (ap fst z=p' ⁻¹) $
                np∉)
    , (λ z∈' → subst (negate z ∉_)
                     (tail-of-++-r {xs = p ∷ []}
                                   (¬any-∷ (contra (λ z=p → List.∈-map _ $
                                                            List.∈-map _ $
                                                            subst (λ q → (q , guessed) ∈ tr')
                                                                  z=p
                                                                  z∈')
                                                   (uniq-uncons ti'' .fst))
                                           false!) ⁻¹) $
               ti2' z z∈')
   ]ᵤ (any-uncons z∈)
  ri'' : Rejstk-Inv rj ((p , guessed) ∷ tr')
  ri'' x f x∈ =
    let nx∈ = ri x f x∈ in
    Dec.rec
      (λ le →
          subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
                (≤→∸=0 le ⁻¹) $
          there $
          subst (λ q → negate x ∈ trail-lits q)
                 (us' .snd .snd ⁻¹) $
          subst (negate x ∈_)
                (trail-lits-++ {tr1 = us' .fst} ⁻¹) $
          any-++-r {xs = trail-lits (us' .fst)} $
          subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                (≤→∸=0 (=→≤ (uspsuffix→count-guessed us') ∙ ≤-ascend ∙ le)) $
          nx∈)
      (λ ge →
          let le' = ≤≃<suc ⁻¹ $ ≱→< ge in
          subst (λ q → negate x ∈ trail-lits (drop-guessed ((p , guessed) ∷ tr') q))
                (+∸-assoc _ _ _ le') $
          subst (λ q → negate x ∈ trail-lits (drop-guessed tr' (q ∸ fin→ℕ f)))
                (uspsuffix→count-guessed us') $
          subst (λ q → negate x ∈ trail-lits (drop-guessed q (count-guessed tr ∸ fin→ℕ f)))
                (us' .snd .snd ⁻¹) $
          [ (λ lt' →
                subst (λ q → negate x ∈ trail-lits q)
                      (drop-guessed-++-l
                         {pr = us' .fst} {n = count-guessed tr ∸ fin→ℕ f}
                         (us' .snd .fst)
                         (∸>0≃> ⁻¹ $ <-≤-trans lt' (=→≤ (uspsuffix→count-guessed us' ⁻¹)))
                         ⁻¹) $
                nx∈)
          , (λ e' →
               let e'' = ≤→∸=0 (=→≤ (uspsuffix→count-guessed us' ∙ e' ⁻¹)) in
               subst (λ q → negate x ∈ trail-lits (drop-guessed (us' .fst ++ tr) q))
                     (e'' ⁻¹) $
               subst (negate x ∈_)
                     (trail-lits-++ {tr1 = us' .fst} ⁻¹) $
               any-++-r {xs = trail-lits (us' .fst)} $
               subst (λ q → negate x ∈ trail-lits (drop-guessed tr q))
                     e'' $
               nx∈)
          ]ᵤ (≤→<⊎= le'))
      (≤-dec {x = suc (count-guessed tr')} {x = fin→ℕ f})
  prf : (  map (λ q → 2 · sizeₛ Γ ∸ sizeₛ q) rj
         , 2 · sizeₛ Γ ∸ suc (length tr'))
          Box∷×.<∷× (x , y)
  prf = inr (  ex ⁻¹
             , <-≤-trans
                  (<-∸-2l-≃ (trail-inv≤ {tr = (p , guessed) ∷ tr'}
                                        ti'') ⁻¹ $
                   ≤≃<suc $ (uspsuffix→len us'))
                  (=→≤ (ey ⁻¹)))

dpli-loop : CNF Γ → ∀[ □∷× (TSI-ty {Γ}) ⇒ TSI-ty ]
dpli-loop {Γ} cls {x = x , y} ih tr ti ti2 rj ri ex ey =
  let (cls' , tr' , ti' , ti2' , us') = unit-propagate-iter cls tr ti ti2 in
  if List.has [] cls' then
    Maybe.elim (λ m → backtrack tr ＝ m → Maybe SatMap)
      (λ _ → nothing)
      (λ where (p , trr) eb →
                  dpli-loop-backtrack ih tr ti ti2 rj ri ex ey p trr eb)
      (backtrack tr) refl
  else
    let ps = unassigned cls tr' in
    Dec.rec (λ _ → just $ trail→map tr')
            (λ ne → dpli-loop-guess cls ih tr  ti  ti2  rj ri ex ey
                                    cls'   tr' ti' ti2' us' ps ne refl)
            (Dec-is-nil? {xs = ps})

dpli : CNF Γ → Maybe SatMap
dpli {Γ} c =
  Box∷×.fix∷× TSI-ty
    (dpli-loop c)
    []
    (emp-trailinv {Γ = Γ})
    emp-trailinv2
    (replicateᵥ (sizeₛ Γ) [])
    emp-rejstkinv
    refl
    refl

dplisat : Formulaᵢ Γ → Maybe SatMap
dplisat = dpli ∘ snd ∘ defcnfs

dplitaut : Formulaᵢ Γ → Bool
dplitaut = not ∘ is-just? ∘ dplisat ∘ Not

main : Main
main =
  run $
  do put-str-ln $ "prime(DPLI) 13: " ++ₛ ppFBᵢ dplitaut (prime 13)
     put-str-ln $ "prime(DPLI) 14: " ++ₛ ppFBᵢ dplitaut (prime 14)
     {-
     let m1 = dplisat (chk f1)
     put-str-ln $ "IXLIF1: " ++ₛ show (map showmp m1)
     put-str-ln $ "IXLIF1-test: " ++ₛ show (map (eval-map f1) m1)
     put-str-ln $ "IXLIF1-dtest: " ++ₛ show (map (eval-map (ers $ snd $ defcnf' $ chk f1)) m1)

     let m2 = dplisat (chk f2)
     put-str-ln $ "IXLIF2: " ++ₛ show (map showmp m2)
     put-str-ln $ "IXLIF2-test: " ++ₛ show (map (eval-map f2) m2)
     put-str-ln $ "IXLIF2-dtest: " ++ₛ show (map (eval-map (ers $ snd $ defcnf' $ chk f2)) m2)
     -}
