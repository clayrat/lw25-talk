{-# OPTIONS --no-exact-split #-}
module SAT.NF0 where

open import Foundations.Prelude
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Meta.Show
open import Logic.Discreteness
open import System.Everything hiding (_<$>_)

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List
open import Data.List.Operations.Discrete

open import Data.List.NonEmpty as List⁺

open import ListSet
open import SAT.Formula0
open import SAT.Sem

private variable
  A : 𝒰

psimplify1 : Formula A → Formula A
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

psimplify : Formula A → Formula A
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

data Lit (A : 𝒰) : 𝒰 where
  Pos : A → Lit A
  Neg : A → Lit A

unlit : Lit A → A
unlit (Pos a) = a
unlit (Neg a) = a

is-pos : Lit A → Type
is-pos (Pos x) = ⊤
is-pos (Neg x) = ⊥

pos≠neg : {x y : A} → Pos x ≠ Neg y
pos≠neg p = subst is-pos p tt

Lit-= : (A → A → Bool)
      → Lit A → Lit A → Bool
Lit-= e (Pos x) (Pos y) = e x y
Lit-= e (Pos x) (Neg y) = false
Lit-= e (Neg x) (Pos y) = false
Lit-= e (Neg x) (Neg y) = e x y

Reflects-lit : {e : A → A → Bool}
             → (∀ {x y} → Reflects (x ＝ y) (e x y))
             → ∀ {lx ly} → Reflects (lx ＝ ly) (Lit-= e lx ly)
Reflects-lit re {lx = Pos x} {ly = Pos y} = Reflects.dmap (ap Pos) (contra (ap unlit)) re
Reflects-lit re {lx = Pos x} {ly = Neg y} = ofⁿ pos≠neg
Reflects-lit re {lx = Neg x} {ly = Pos y} = ofⁿ (pos≠neg ∘ _⁻¹)
Reflects-lit re {lx = Neg x} {ly = Neg y} = Reflects.dmap (ap Neg) (contra (ap unlit)) re

instance
  Lit-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Lit A)
  Lit-is-discrete ⦃ d ⦄ {x} {y} .does  = Lit-= (λ x y → d {x = x} {y = y} .does) x y
  Lit-is-discrete ⦃ d ⦄         .proof = Reflects-lit (d .proof)

  Show-lit : ⦃ s : Show A ⦄ → Show (Lit A)
  Show-lit = default-show λ where
                              (Pos x) → show x
                              (Neg x) → "¬" ++ₛ show x

negative : Lit A → Bool
negative (Neg _) = true
negative  _      = false

positive : Lit A → Bool
positive = not ∘ negative

abs : Lit A → Lit A
abs (Neg p) = Pos p
abs (Pos p) = Pos p

negate : Lit A → Lit A
negate (Neg p) = Pos p
negate (Pos p) = Neg p

lit→form : Lit A → Formula A
lit→form (Pos a) = Atom a
lit→form (Neg a) = Not (Atom a)

trivial? : ⦃ d : is-discrete A ⦄
         → List (Lit A) → Bool
trivial? c =
  let (p , n) = partition positive c in
  is-cons? $ intersect p $ image negate n

-- NNF

data NNF (A : 𝒰) : 𝒰 where
  LitF   : Lit A → NNF A
  TrueF  : NNF A
  FalseF : NNF A
  AndF   : NNF A → NNF A → NNF A
  OrF    : NNF A → NNF A → NNF A

nnf→form : NNF A → Formula A
nnf→form (LitF l)   = lit→form l
nnf→form  TrueF     = True
nnf→form  FalseF    = False
nnf→form (AndF x y) = And (nnf→form x) (nnf→form y)
nnf→form (OrF x y)  = Or (nnf→form x) (nnf→form y)

mutual
  nnf : Formula A → NNF A
  nnf  False    = FalseF
  nnf  True     = TrueF
  nnf (Atom a)  = LitF (Pos a)
  nnf (Not x)   = nnfNot x
  nnf (And x y) = AndF (nnf x) (nnf y)
  nnf (Or x y)  = OrF (nnf x) (nnf y)
  nnf (Imp x y) = OrF (nnfNot x) (nnf y)
  nnf (Iff x y) = OrF (AndF (nnf x) (nnf y)) (AndF (nnfNot x) (nnfNot y))

  nnfNot : Formula A → NNF A
  nnfNot  False    = TrueF
  nnfNot  True     = FalseF
  nnfNot (Atom a)  = LitF (Neg a)
  nnfNot (Not x)   = nnf x
  nnfNot (And x y) = OrF (nnfNot x) (nnfNot y)
  nnfNot (Or x y)  = AndF (nnfNot x) (nnfNot y)
  nnfNot (Imp x y) = AndF (nnf x) (nnfNot y)
  nnfNot (Iff x y) = OrF (AndF (nnf x) (nnfNot y)) (AndF (nnfNot x) (nnf y))

nnf0 : Formula A → NNF A
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

data NENF (A : 𝒰) : 𝒰 where
  LitEF   : Lit A → NENF A
  TrueEF  : NENF A
  FalseEF : NENF A
  AndEF   : NENF A → NENF A → NENF A
  OrEF    : NENF A → NENF A → NENF A
  IffEF   : NENF A → NENF A → NENF A

nenf→form : NENF A → Formula A
nenf→form (LitEF l)   = lit→form l
nenf→form  TrueEF     = True
nenf→form  FalseEF    = False
nenf→form (AndEF x y) = And (nenf→form x) (nenf→form y)
nenf→form (OrEF x y)  = Or (nenf→form x) (nenf→form y)
nenf→form (IffEF x y) = Iff (nenf→form x) (nenf→form y)

mutual
  nenf : Formula A → NENF A
  nenf  False    = FalseEF
  nenf  True     = TrueEF
  nenf (Atom a)  = LitEF (Pos a)
  nenf (Not x)   = nenfNot x
  nenf (And x y) = AndEF (nenf x) (nenf y)
  nenf (Or x y)  = OrEF (nenf x) (nenf y)
  nenf (Imp x y) = OrEF (nenfNot x) (nenf y)
  nenf (Iff x y) = IffEF (nenf x) (nenf y)

  nenfNot : Formula A → NENF A
  nenfNot  False    = TrueEF
  nenfNot  True     = FalseEF
  nenfNot (Atom a)  = LitEF (Neg a)
  nenfNot (Not x)   = nenf x
  nenfNot (And x y) = OrEF (nenfNot x) (nenfNot y)
  nenfNot (Or x y)  = AndEF (nenfNot x) (nenfNot y)
  nenfNot (Imp x y) = AndEF (nenf x) (nenfNot y)
  nenfNot (Iff x y) = IffEF (nenf x) (nenfNot y)

nenf0 : Formula A → NENF A
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

list-conj : List (Formula A) → Formula A
list-conj = Maybe.rec True (foldr₁ And) ∘ from-list

list-disj : List (Formula A) → Formula A
list-disj = Maybe.rec False (foldr₁ Or) ∘ from-list

mklits : List (Formula A) → Val A → Formula A
mklits pvs v = list-conj $ map (λ p → if eval p v then p else Not p) pvs

all-sat-vals : ⦃ d : is-discrete A ⦄
             → (Val A → Bool)
             → Val A → List A → List (Val A)
all-sat-vals s v  []      = if s v then v ∷ [] else []
all-sat-vals s v (p ∷ ps) =
     all-sat-vals s (modify p false v) ps
  ++ all-sat-vals s (modify p true v) ps

dnf-naive : ⦃ d : is-discrete A ⦄
          → Formula A → Formula A
dnf-naive f =
  let ps = atoms f
      sv = all-sat-vals (eval f) (λ _ → false) ps
    in
  list-disj $
  map (mklits (map Atom ps)) sv

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

distribAnd : Formula A → Formula A → Formula A
distribAnd (Or p q)  r       = Or (distribAnd p r) (distribAnd q r)
distribAnd  p       (Or q r) = Or (distribAnd p q) (distribAnd p r)
distribAnd  p        q       = And p q

rawdnf : Formula A → Formula A
rawdnf (And x y) = distribAnd (rawdnf x) (rawdnf y)
rawdnf (Or x y)  = Or (rawdnf x) (rawdnf y)
rawdnf  f        = f

{-
_ : "(p ∧ ¬p ∨ p ∧ ¬r) ∨ (q ∧ r) ∧ ¬p ∨ (q ∧ r) ∧ ¬r" ∈ (prettyF ∘ rawdnf <$> fmP)
_ = hereₘ refl
-}

-- TODO use LFSet

Conjunct : 𝒰 → 𝒰
Conjunct A = List (Lit A)

DNF : 𝒰 → 𝒰
DNF A = List (Conjunct A)

dnf→form : DNF A → Formula A
dnf→form = list-disj ∘ map (list-conj ∘ map lit→form)

distrib : ⦃ d : is-discrete A ⦄
        → DNF A → DNF A → DNF A
distrib s1 s2 = nub _=?_ $ map² union s1 s2 -- TODO better names / API

purednf : ⦃ d : is-discrete A ⦄
        → NNF A → DNF A
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

simpdnf : ⦃ d : is-discrete A ⦄
        → Formula A → DNF A
simpdnf f =
  let djs = filter (not ∘ trivial?) $ purednf $ nnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) djs)) djs

dnf : ⦃ d : is-discrete A ⦄
    → Formula A → Formula A
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

Clause : 𝒰 → 𝒰
Clause A = List (Lit A)

CNF : 𝒰 → 𝒰
CNF A = List (Clause A)

cnf→form : CNF A → Formula A
cnf→form = list-conj ∘ map (list-disj ∘ map lit→form)

purecnf : ⦃ d : is-discrete A ⦄
        → Formula A → CNF A
purecnf = image (image negate) ∘ purednf ∘ nnfNot

simpcnf : ⦃ d : is-discrete A ⦄
        → Formula A → CNF A
simpcnf f =
  let cjs = filter (not ∘ trivial?) $ purecnf f in
  filter (λ c → not (any (λ c′ → psubset? c′ c) cjs)) cjs

cnf : ⦃ d : is-discrete A ⦄
    → Formula A → Formula A
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
