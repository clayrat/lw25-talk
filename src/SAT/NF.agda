{-# OPTIONS --no-exact-split #-}
module SAT.NF where

open import Prelude hiding (_≠_)
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Meta.Show
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Rel
open import Data.Sum

open import Data.List.NonEmpty as List⁺

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import ListSet
open import SAT.Formula0
open import SAT.Sem
open import SAT.Formula

private variable
  A B : 𝒰
  Γ : LFSet A
  
psimplify1 : Formulaᵢ Γ → Formulaᵢ Γ
psimplify1 (Not False)   = True
psimplify1 (Not True)    = False
psimplify1 (Not (Not x)) = x
psimplify1 (And False y) = False
psimplify1 (And True y)  = y
psimplify1 (And x False) = False
psimplify1 (And x True)  = x
psimplify1 (Or False y)  = y
psimplify1 (Or True y)   = True
psimplify1 (Or x False)  = x
psimplify1 (Or x True)   = True
psimplify1 (Imp False y) = True
psimplify1 (Imp True y)  = y
psimplify1 (Imp x False) = Not x
psimplify1 (Imp x True)  = True
psimplify1 (Iff False y) = Not y
psimplify1 (Iff True y)  = y
psimplify1 (Iff x False) = Not x
psimplify1 (Iff x True)  = x
psimplify1  f            = f

psimplify : Formulaᵢ Γ → Formulaᵢ Γ
psimplify (Not x)   = psimplify1 (Not (psimplify x))
psimplify (And x y) = psimplify1 (And (psimplify x) (psimplify y))
psimplify (Or x y)  = psimplify1 (Or (psimplify x) (psimplify y))
psimplify (Imp x y) = psimplify1 (Imp (psimplify x) (psimplify y))
psimplify (Iff x y) = psimplify1 (Iff (psimplify x) (psimplify y))
psimplify  f        = f

{-
_ : Imp (Not (Atom "x")) (Not (Atom "y")) ∈ (psimplify <$> parseForm "(true => (x <=> false)) => ~(y \\/ false /\\ z)")
_ = hereₘ refl

_ : True ∈ (psimplify <$> parseForm "((x => y) => true) \\/ ~false")
_ = hereₘ refl
-}

data Lit (Γ : LFSet A) : 𝒰 where
  Pos : (a : A) → a ∈ Γ → Lit Γ
  Neg : (a : A) → a ∈ Γ → Lit Γ

unlit : {Γ : LFSet A}
      → Lit Γ → A
unlit (Pos a _) = a
unlit (Neg a _) = a

is-pos : Lit Γ → Type
is-pos (Pos x _) = ⊤
is-pos (Neg x _) = ⊥

pos≠neg : {Γ : LFSet A} {x y : A} {mx : x ∈ Γ} {my : y ∈ Γ}
        → Pos x mx ≠ Neg y my
pos≠neg p = subst is-pos p tt

Lit-= : {Γ : LFSet A}
      → (A → A → Bool)
      → Lit Γ → Lit Γ → Bool
Lit-= e (Pos x _) (Pos y _) = e x y
Lit-= e (Pos x _) (Neg y _) = false
Lit-= e (Neg x _) (Pos y _) = false
Lit-= e (Neg x _) (Neg y _) = e x y

Reflects-lit : {Γ : LFSet A} {e : A → A → Bool}
             → (∀ {x y} → Reflects (x ＝ y) (e x y))
             → ∀ {lx ly : Lit Γ} → Reflects (lx ＝ ly) (Lit-= e lx ly)
Reflects-lit re {lx = Pos x mx} {ly = Pos y my} = Reflects.dmap (λ x → ap² Pos x (to-pathᴾ (hlevel 1 _ my))) (contra (ap unlit)) re
Reflects-lit re {lx = Pos x mx} {ly = Neg y my} = ofⁿ pos≠neg
Reflects-lit re {lx = Neg x mx} {ly = Pos y my} = ofⁿ (pos≠neg ∘ _⁻¹)
Reflects-lit re {lx = Neg x mx} {ly = Neg y my} = Reflects.dmap (λ x → ap² Neg x (to-pathᴾ (hlevel 1 _ my))) (contra (ap unlit)) re

instance
  Lit-is-discrete : {Γ : LFSet A} → ⦃ d : is-discrete A ⦄ → is-discrete (Lit Γ)
  Lit-is-discrete ⦃ d ⦄ {x} {y} .does  = Lit-= (λ x y → d {x = x} {y = y} .does) x y
  Lit-is-discrete ⦃ d ⦄         .proof = Reflects-lit (d .proof)

  Show-lit : {Γ : LFSet A} → ⦃ s : Show A ⦄ → Show (Lit Γ)
  Show-lit = default-show λ where
                              (Pos x _) → show x
                              (Neg x _) → "¬" ++ₛ show x

negative : Lit Γ → Bool
negative (Neg _ _) = true
negative  _        = false

positive : Lit Γ → Bool
positive = not ∘ negative

abs : Lit Γ → Lit Γ
abs (Neg p mp) = Pos p mp
abs (Pos p mp) = Pos p mp

abs-idem : {l : Lit Γ}
         → abs (abs l) ＝ abs l
abs-idem {l = Pos a m} = refl
abs-idem {l = Neg a m} = refl

negate : Lit Γ → Lit Γ
negate (Neg p mp) = Pos p mp
negate (Pos p mp) = Neg p mp

abs-negate : {l : Lit Γ}
           → abs (negate l) ＝ abs l
abs-negate {l = Pos a m} = refl
abs-negate {l = Neg a m} = refl

restrict : {Γ : LFSet A}
         → (l : Lit Γ) → Lit (sng (unlit l))
restrict (Pos a _) = Pos a (hereₛ refl)
restrict (Neg a _) = Neg a (hereₛ refl)

wk-lit : {Γ Δ : LFSet A} → Γ ⊆ Δ → Lit Γ → Lit Δ
wk-lit f (Pos a m) = Pos a (f m)
wk-lit f (Neg a m) = Neg a (f m)

wk-lit-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
           → Injective (wk-lit s)
wk-lit-inj {s = s} {x = Pos a x} {y = Pos b y} e =
  ap² Pos (ap unlit e) (to-pathᴾ (hlevel 1 _ y))
wk-lit-inj {s = s} {x = Pos a x} {y = Neg b y} e =
  absurd (pos≠neg e)
wk-lit-inj {s = s} {x = Neg a x} {y = Pos b y} e =
  absurd (pos≠neg (e ⁻¹))
wk-lit-inj {s = s} {x = Neg a x} {y = Neg b y} e =
  ap² Neg (ap unlit e) (to-pathᴾ (hlevel 1 _ y))

negate-invol : {l : Lit Γ}
             → negate (negate l) ＝ l
negate-invol {l = Pos a m} = refl
negate-invol {l = Neg a m} = refl

negate-swap : {l m : Lit Γ}
            → l ＝ negate m
            → m ＝ negate l
negate-swap e = negate-invol ⁻¹ ∙ ap negate (e ⁻¹)             

negative-negate : {l : Lit Γ}
                → negative (negate l) ＝ positive l
negative-negate {l = Pos a x} = refl
negative-negate {l = Neg a x} = refl

-- TODO should probably generalized to involutive→injective (or embedding?)
negate-inj : {Γ : LFSet A}
           → Injective (negate {Γ = Γ})
negate-inj {x} {y} e = negate-invol {l = x} ⁻¹ ∙ ap negate e ∙ negate-invol {l = y}

unlit-eq : {Γ : LFSet A} {x y : Lit Γ}
         → unlit x ＝ unlit y
         → (x ＝ y) ⊎ (x ＝ negate y)
unlit-eq {x = Pos a x} {y = Pos b y} e =
  inl (ap² Pos e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Pos a x} {y = Neg b y} e =
  inr (ap² Pos e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Neg a x} {y = Pos b y} e =
  inr (ap² Neg e (to-pathᴾ (hlevel 1 _ y)))
unlit-eq {x = Neg a x} {y = Neg b y} e =
  inl (ap² Neg e (to-pathᴾ (hlevel 1 _ y)))

unlit-negate : {Γ : LFSet A} {x : Lit Γ}
             → unlit x ＝ unlit (negate x)
unlit-negate {x = Pos a x} = refl
unlit-negate {x = Neg a x} = refl

unlit-positive-inj : {Γ : LFSet A}
                   → Injective < unlit {Γ = Γ} , positive >
unlit-positive-inj {x = Pos a x} {y = Pos b y} e =
  ap² Pos (ap fst e) (to-pathᴾ (hlevel 1 _ y))
unlit-positive-inj {x = Pos a x} {y = Neg b y} e =
  false! (ap snd e)
unlit-positive-inj {x = Neg a x} {y = Pos b y} e =
  false! (ap snd e)
unlit-positive-inj {x = Neg a x} {y = Neg b y} e =
  ap² Neg (ap fst e) (to-pathᴾ (hlevel 1 _ y))
             
unlit∈ : (l : Lit Γ) → unlit l ∈ Γ
unlit∈ (Pos a m) = m
unlit∈ (Neg a m) = m

map-unlit-⊆ : {Γ : LFSet A}
            → ⦃ d : is-discrete A ⦄
            → (ls : List (Lit Γ)) → mapₛ unlit (LFSet.from-list ls) ⊆ Γ
map-unlit-⊆ {Γ} ls =
    rec! (λ l _ e → subst (_∈ Γ) (e ⁻¹) (unlit∈ l))
  ∘ mapₛ-∈ {s = LFSet.from-list ls}

lit→form : {Γ : LFSet A}
         → Lit Γ → Formulaᵢ Γ
lit→form (Pos a m) = Atom a m
lit→form (Neg a m) = Not (Atom a m)

-- applies to both Clauses and Conjuncts
nontrivial? : {Γ : LFSet A}
            → ⦃ d : is-discrete A ⦄
            → List (Lit Γ) → Bool
nontrivial? c =
  let (p , n) = partition positive c in
  is-nil? $ intersect p $ image negate n

-- nontrivial = no literal is included both positively and negatively
Reflects-nontrivial? : {Γ : LFSet A}
                     → ⦃ di : is-discrete A ⦄
                     → {c : List (Lit Γ)}
                     → Reflects ({l : Lit Γ} → l ∈ c → negate l ∈ c → ⊥)
                                (nontrivial? c)
Reflects-nontrivial? ⦃ di ⦄ {c} =
  let (p , n) = partition positive c
      e = partition-filter {p = positive} {xs = c}
      (ep , en) = ×-path-inv e
      op = subst (λ q → OPE q c) (ep ⁻¹) filter-OPE
      on = subst (λ q → OPE q c) (en ⁻¹) filter-OPE
    in
  Reflects.dmap
    (λ d {l} l∈ n∈ →
       Dec.rec
         (λ lp → d (subst (l ∈_) (ep ⁻¹) $
                    ∈-filter lp l∈)
                   (subst (λ q → l ∈ image negate q) (en ⁻¹) $
                    ⊆-nub {R = λ _ _ → Reflects-lit (di .proof)} $
                    subst (λ q → q ∈ map negate (filter (not ∘ positive) c)) negate-invol $      
                    List.∈-map negate $
                    ∈-filter (subst So (negative-negate ⁻¹ ∙ not-invol _ ⁻¹) lp) n∈))
         (λ ln → let ln′ = not-so-≃ ⁻¹ $ ln in
                 d (subst (negate l ∈_) (ep ⁻¹) $
                    ∈-filter (subst (So ∘ not) (negative-negate ⁻¹) ln′) n∈)
                   (⊆-nub {R = λ _ _ → Reflects-lit (di .proof)} $
                    List.∈-map negate $
                    subst (l ∈_) (en ⁻¹) $
                    ∈-filter ln′ l∈))
         (Dec-So {b = positive l}))
    (contra λ d l∈p l∈n →
              d (ope→subset op l∈p)
                (ope→subset on $
                 map-∈ negate negate-inj $
                 subst (_∈ map negate n) (negate-invol ⁻¹) $
                 ope→subset nub-ope l∈n))
    Reflects-intersect-disjoint 

Dec-nontrivial? : {Γ : LFSet A}
                → ⦃ di : is-discrete A ⦄
                → (c : List (Lit Γ))
                → Dec ({l : Lit Γ} → l ∈ c → negate l ∈ c → ⊥)
Dec-nontrivial? c .does  = nontrivial? c
Dec-nontrivial? c .proof = Reflects-nontrivial?

{-
trivial? : {Γ : LFSet A}
         → ⦃ d : is-discrete A ⦄
         → List (Lit Γ) → Bool
trivial? c =
  let (p , n) = partition positive c in
  is-cons? $ intersect p $ image negate n
-}

-- NNF

data NNF (Γ : LFSet A) : 𝒰 where
  LitF   : Lit Γ → NNF Γ
  TrueF  : NNF Γ
  FalseF : NNF Γ
  AndF   : NNF Γ → NNF Γ → NNF Γ
  OrF    : NNF Γ → NNF Γ → NNF Γ

nnf→form : {Γ : LFSet A} → NNF Γ → Formulaᵢ Γ
nnf→form (LitF l)   = lit→form l
nnf→form  TrueF     = True
nnf→form  FalseF    = False
nnf→form (AndF x y) = And (nnf→form x) (nnf→form y)
nnf→form (OrF x y)  = Or (nnf→form x) (nnf→form y)

mutual
  nnf : Formulaᵢ Γ → NNF Γ
  nnf  False     = FalseF
  nnf  True      = TrueF
  nnf (Atom a m) = LitF (Pos a m)
  nnf (Not x)    = nnfNot x
  nnf (And x y)  = AndF (nnf x) (nnf y)
  nnf (Or x y)   = OrF (nnf x) (nnf y)
  nnf (Imp x y)  = OrF (nnfNot x) (nnf y)
  nnf (Iff x y)  = OrF (AndF (nnf x) (nnf y)) (AndF (nnfNot x) (nnfNot y))

  nnfNot : Formulaᵢ Γ → NNF Γ
  nnfNot  False     = TrueF
  nnfNot  True      = FalseF
  nnfNot (Atom a m) = LitF (Neg a m)
  nnfNot (Not x)    = nnf x
  nnfNot (And x y)  = OrF (nnfNot x) (nnfNot y)
  nnfNot (Or x y)   = AndF (nnfNot x) (nnfNot y)
  nnfNot (Imp x y)  = AndF (nnf x) (nnfNot y)
  nnfNot (Iff x y)  = OrF (AndF (nnf x) (nnfNot y)) (AndF (nnfNot x) (nnf y))

nnf0 : Formulaᵢ Γ → NNF Γ
nnf0 = nnf ∘ psimplify

{-
fm : Maybe Form
fm = parseForm "(p <=> q) <=> ~(r => s)"

fm′ : Maybe Form
fm′ = (nnf→form ∘ nnf0) <$> fm

_ : "(p ∧ q ∨ ¬p ∧ ¬q) ∧ r ∧ ¬s ∨ (p ∧ ¬q ∨ ¬p ∧ q) ∧ (¬r ∨ s)" ∈ (prettyF <$> fm′)
_ = hereₘ refl

_ : true ∈ map² (λ a b → tautology (Iff a b)) fm fm′
_ = hereₘ refl
-}

-- NENF

data NENF (Γ : LFSet A) : 𝒰 where
  LitEF   : Lit Γ → NENF Γ
  TrueEF  : NENF Γ
  FalseEF : NENF Γ
  AndEF   : NENF Γ → NENF Γ → NENF Γ
  OrEF    : NENF Γ → NENF Γ → NENF Γ
  IffEF   : NENF Γ → NENF Γ → NENF Γ

nenf→form : NENF Γ  → Formulaᵢ Γ
nenf→form (LitEF l)   = lit→form l
nenf→form  TrueEF     = True
nenf→form  FalseEF    = False
nenf→form (AndEF x y) = And (nenf→form x) (nenf→form y)
nenf→form (OrEF x y)  = Or (nenf→form x) (nenf→form y)
nenf→form (IffEF x y) = Iff (nenf→form x) (nenf→form y)

mutual
  nenf : Formulaᵢ Γ → NENF Γ
  nenf  False    = FalseEF
  nenf  True     = TrueEF
  nenf (Atom a m)  = LitEF (Pos a m)
  nenf (Not x)   = nenfNot x
  nenf (And x y) = AndEF (nenf x) (nenf y)
  nenf (Or x y)  = OrEF (nenf x) (nenf y)
  nenf (Imp x y) = OrEF (nenfNot x) (nenf y)
  nenf (Iff x y) = IffEF (nenf x) (nenf y)

  nenfNot : Formulaᵢ Γ → NENF Γ
  nenfNot  False    = TrueEF
  nenfNot  True     = FalseEF
  nenfNot (Atom a m)  = LitEF (Neg a m)
  nenfNot (Not x)   = nenf x
  nenfNot (And x y) = OrEF (nenfNot x) (nenfNot y)
  nenfNot (Or x y)  = AndEF (nenfNot x) (nenfNot y)
  nenfNot (Imp x y) = AndEF (nenf x) (nenfNot y)
  nenfNot (Iff x y) = IffEF (nenf x) (nenfNot y)

nenf0 : Formulaᵢ Γ → NENF Γ
nenf0 = nenf ∘ psimplify

{-
_ : true ∈ (tautology <$> parseForm "(p => p') /\\ (q => q') => (p /\\ q => p' /\\ q')")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "(p => p') /\\ (q => q') => (p \\/ q => p' \\/ q')")
_ = hereₘ refl
-}

-- TODO (anti)monotonicity

-- DNF
-- satisfiability checking for a formula in DNF is easy

list-conj : List (Formulaᵢ Γ) → Formulaᵢ Γ
list-conj = Maybe.rec True (foldr₁ And) ∘ List⁺.from-list

list-conjΣ : List (Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)) → Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)
list-conjΣ =
    Maybe.rec ([] , True)
              (foldr₁ (λ where (Γ , f) (Δ , g) →
                                 (Γ ∪∷ Δ) , And (wk  ∈ₛ-∪∷←l           f)
                                                (wk (∈ₛ-∪∷←r {s₁ = Γ}) g)))
  ∘ List⁺.from-list

list-disj : List (Formulaᵢ Γ) → Formulaᵢ Γ
list-disj = Maybe.rec False (foldr₁ Or) ∘ List⁺.from-list

list-disjΣ : List (Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)) → Σ[ Γ ꞉ Ctx ] (Formulaᵢ Γ)
list-disjΣ =
    Maybe.rec ([] , False)
              (foldr₁ (λ where (Γ , f) (Δ , g) →
                                 (Γ ∪∷ Δ) , Or (wk  ∈ₛ-∪∷←l           f)
                                               (wk (∈ₛ-∪∷←r {s₁ = Γ}) g)))
  ∘ List⁺.from-list

mklits : {Γ : LFSet A}
       → List (Formulaᵢ Γ) → Val A → Formulaᵢ Γ
mklits pvs v = list-conj $ map (λ p → if evalᵢ p v then p else Not p) pvs
  --   map (λ p → if eval p v then p else Not p) pvs

all-sat-vals : ⦃ d : is-discrete A ⦄
             → (Val A → Bool)
             → Val A → List A → List (Val A)
all-sat-vals s v  []      = if s v then v ∷ [] else []
all-sat-vals s v (p ∷ ps) =
     all-sat-vals s (modify p false v) ps
  ++ all-sat-vals s (modify p true v) ps

dnf-naive : {Γ : LFSet A}
          → ⦃ d : is-discrete A ⦄
          → Formulaᵢ Γ → Formulaᵢ Γ
dnf-naive f =
  let ps = atomsᵢ f
      sv = all-sat-vals (evalᵢ f) (λ _ → false) ps
    in
  list-disj $
  map (mklits (map-with-∈ ps (λ a a∈ → Atom a (atomsᵢ-⊆ {f = f}
                                                        (ope→subset (nub-ope {cmp = _=?_}) a∈))
                                              ))) sv

{-
fm1 : String
fm1 = "(p \\/ q /\\ r) /\\ (~p \\/ ~r)"

fmP : Maybe Form
fmP = parseForm fm1
-}

{-
_ : "(p ∨ q ∧ r) ∧ (¬p ∨ ¬r)" ∈ (prettyF <$> fmP)
_ = hereₘ refl

_ : "¬p ∧ q ∧ r ∨ p ∧ ¬q ∧ ¬r ∨ p ∧ q ∧ ¬r" ∈ (prettyF ∘ dnf-naive <$> fmP)
_ = hereₘ refl
-}

distribAnd : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ
distribAnd (Or p q)  r       = Or (distribAnd p r) (distribAnd q r)
distribAnd  p       (Or q r) = Or (distribAnd p q) (distribAnd p r)
distribAnd  p        q       = And p q

rawdnf : Formulaᵢ Γ → Formulaᵢ Γ
rawdnf (And x y) = distribAnd (rawdnf x) (rawdnf y)
rawdnf (Or x y)  = Or (rawdnf x) (rawdnf y)
rawdnf  f        = f

{-
_ : "(p ∧ ¬p ∨ p ∧ ¬r) ∨ (q ∧ r) ∧ ¬p ∨ (q ∧ r) ∧ ¬r" ∈ (prettyF ∘ rawdnf <$> fmP)
_ = hereₘ refl
-}

-- TODO use LFSet

Conjunct : LFSet A → 𝒰
Conjunct Γ = List (Lit Γ)

DNF : LFSet A → 𝒰
DNF Γ = List (Conjunct Γ)

dnf→form : DNF Γ → Formulaᵢ Γ
dnf→form = list-disj ∘ map (list-conj ∘ map lit→form)

distrib : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → DNF Γ → DNF Γ → DNF Γ
distrib s1 s2 = nub _=?_ $ map² union s1 s2 -- TODO better names / API

purednf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → NNF Γ → DNF Γ
purednf (LitF l)   = (l ∷ []) ∷ []
purednf  TrueF     = [] ∷ []
purednf  FalseF    = []
purednf (AndF x y) = distrib (purednf x) (purednf y)
purednf (OrF x y)  = union (purednf x) (purednf y)

{-
_ : (  (Pos "p" ∷ Neg "p" ∷ [])
     ∷ (Pos "p" ∷ Neg "r" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "p" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "r" ∷ [])
     ∷ []) ∈ (purednf ∘ nnf <$> fmP)
_ = hereₘ refl

_ : (  (Pos "p" ∷ Neg "r" ∷ [])
     ∷ (Pos "q" ∷ Pos "r" ∷ Neg "p" ∷ [])
     ∷ []) ∈ (filter (not ∘ trivial?) ∘ purednf ∘ nnf <$> fmP)
_ = hereₘ refl
-}

simpdnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → DNF Γ
simpdnf f =
  let djs = filter nontrivial? $ purednf $ nnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) djs)) djs

dnf : {Γ : LFSet A}
    → ⦃ d : is-discrete A ⦄
    → Formulaᵢ Γ → Formulaᵢ Γ
dnf = dnf→form ∘ simpdnf

{-
fmpD : Maybe Form
fmpD = dnf <$> fmP
-}
{-
_ : "p ∧ ¬r ∨ q ∧ r ∧ ¬p" ∈ (prettyF <$> fmpD)
_ = hereₘ refl

_ : true ∈ (map² (λ x y → tautology $ Iff x y) fmP fmpD)
_ = hereₘ refl
-}

-- CNF
-- tautology checking for a formula in CNF is easy

Clause : LFSet A → 𝒰
Clause Γ = List (Lit Γ)

CNF : LFSet A → 𝒰
CNF Γ = List (Clause Γ)

cnf→form : CNF Γ → Formulaᵢ Γ
cnf→form = list-conj ∘ map (list-disj ∘ map lit→form)

purecnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → CNF Γ
purecnf = image (image negate) ∘ purednf ∘ nnfNot

simpcnf : {Γ : LFSet A}
        → ⦃ d : is-discrete A ⦄
        → Formulaᵢ Γ → CNF Γ
simpcnf f =
  let cjs = filter nontrivial? $ purecnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) cjs)) cjs

cnf : {Γ : LFSet A}
    → ⦃ d : is-discrete A ⦄
    → Formulaᵢ Γ → Formulaᵢ Γ
cnf = cnf→form ∘ simpcnf

{-
fmpC : Maybe Form
fmpC = cnf <$> fmP
-}
{-
_ : "(p ∨ q) ∧ (p ∨ r) ∧ (¬p ∨ ¬r)" ∈ (prettyF <$> fmpC)
_ = hereₘ refl

_ : true ∈ (map² (λ x y → tautology $ Iff x y) fmP fmpC)
_ = hereₘ refl
-}

-- main : Main
-- main = run $ do put-str-ln $ Maybe.rec "" truth-table fmP
