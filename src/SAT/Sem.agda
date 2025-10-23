module SAT.Sem where

open import Foundations.Prelude
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Logic.Discreteness

open import System.Everything hiding (_<$>_)

open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Unsafe.Data.String.Properties.Unsafe

open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import SAT.Formula0

private variable
  A B : 𝒰

Val : 𝒰 → 𝒰
Val A = A → Bool

eval : Formula A → Val A → Bool
eval  False    v = false
eval  True     v = true
eval (Atom a)  v = v a
eval (Not x)   v = not (eval x v)
eval (And x y) v = eval x v and eval y v
eval (Or x y)  v = eval x v or eval y v
eval (Imp x y) v = eval x v implies eval y v
eval (Iff x y) v = eval x v equals eval y v

{-
frm1 : String
frm1 = "p /\\ q => q /\\ r"

_ : Imp (And (Atom "p") (Atom "q")) (And (Atom "q") (Atom "r")) ∈ parseForm frm1
_ = hereₘ refl

ev1 : Val Var
ev1 v = (v =ₛ "p") or (v =ₛ "r")

_ : true ∈ (flip eval ev1 <$> parseForm frm1)
_ = hereₘ refl

ev2 : Val Var
ev2 v = (v =ₛ "p") or (v =ₛ "q")

_ : false ∈ (flip eval ev2 <$> parseForm frm1)
_ = hereₘ refl

-}

{-
atomsR : {A : 𝒰}
       → Formula A → List A
atomsR False = []
atomsR True = []
atomsR (Atom a) = a ∷ []
atomsR (Not x) = atomsR x
atomsR (And x y) = atomsR x ++ atomsR y
atomsR (Or x y) = atomsR x ++ atomsR y
atomsR (Imp x y) = atomsR x ++ atomsR y
atomsR (Iff x y) = atomsR x ++ atomsR y
-}

{-
atoms⊆ : {A : 𝒰}
       → (f : Formula A)
       → atoms f ⊆ atomsR f
atoms⊆ (Atom a)  m = m
atoms⊆ (Not x)   m = atoms⊆ x m
atoms⊆ (And x y) m = {!!}
atoms⊆ (Or x y)  m = {!!}
atoms⊆ (Imp x y) m = {!!}
atoms⊆ (Iff x y) m = {!!}
-}
{-

eval-agree : {A : 𝒰} {v1 v2 : Val A}
             (f : Formula A)
           → (∀ {x} → x ∈ atoms f → v1 x ＝ v2 x)
           → eval f v1 ＝ eval f v2
eval-agree  False    e = refl
eval-agree  True     e = refl
eval-agree (Atom a)  e = e (here refl)
eval-agree (Not x)   e = ap not (eval-agree x e)
eval-agree (And x y) e = ap² _and_ (eval-agree x λ {x} m → e {!!} )
                                   (eval-agree y λ {x} m → e {!!})
eval-agree (Or x y)  e = {!!}
eval-agree (Imp x y) e = {!!}
eval-agree (Iff x y) e = {!!}
-}

{-
frm2 : String
frm2 = "p /\\ q \\/ s => ~p \\/ (r <=> s)"

_ : ("p" ∷ "q" ∷ "s" ∷ "r" ∷ []) ∈ (atoms <$> parseForm frm2)
_ = hereₘ refl
-}

modify : ⦃ d : is-discrete A ⦄
       → A → Bool → Val A → Val A
modify x a v y = if y =? x then a else v y

on-all-vals : ⦃ d : is-discrete A ⦄
            → (Val A → B)
            → (B → B → B)
            → Val A → List A → B
on-all-vals     sf c v []       = sf v
on-all-vals {A} sf c v (a ∷ as) =
  c (on-all-vals sf c (modify a false v) as)
    (on-all-vals sf c (modify a true v) as)

-- truth tables

truth-table-doc : Form → Doc
truth-table-doc fm =
  let pvs = atoms fm
      width = suc $ List.rec 5 (max ∘ lengthₛ) pvs
      fixw : String → String
      fixw s = s ++ₛ replicateₛ (width ∸ lengthₛ s) ' '
      truthstring : Bool → String
      truthstring p = fixw (if p then "⊤" else "⊥")
      separator = replicateₛ (width · length pvs + 9) '-'
      row : Val Var → List (List String)
      row v = let lis = (truthstring ∘ v) <$> pvs
                  ans = truthstring (eval fm v)
                 in
              (lis ∷r ans) ∷ []
      rows = on-all-vals row _++_ (λ _ → false) pvs
      rowstr : List String → String
      rowstr r = let (lis , ans) = split-at (pred (length r)) r in
                 List.rec ("| " ++ₛ from-just "" (headᵐ ans)) _++ₛ_ lis
    in
  vcat (  textD (List.rec "| formula" (λ s → fixw s ++ₛ_) pvs)
        ∷ textD separator
        ∷ vcat (textD ∘ rowstr <$> rows)
        ∷ textD separator
        ∷ [])

truth-table : Form → String
truth-table = render ∘ truth-table-doc

-- tautology / satisfiability

-- satisfied by all valuations
tautology : ⦃ d : is-discrete A ⦄
          → Formula A → Bool
tautology f = on-all-vals (eval f) _and_ (λ _ → false) (atoms f)

-- satisfied by no valuation
unsatisfiable : ⦃ d : is-discrete A ⦄
              → Formula A → Bool
unsatisfiable = tautology ∘ Not

-- satisfied by some valuation(s)
satisfiable : ⦃ d : is-discrete A ⦄
            → Formula A → Bool
satisfiable = not ∘ unsatisfiable

-- substitution

-- TODO use substitution types from unification?
Subst : 𝒰 → 𝒰
Subst A = A → Maybe (Formula A)

psubst : Subst A → Formula A → Formula A
psubst sf = on-atoms λ p → from-just (Atom p) (sf p)

sngl : Var → Form → Subst Var
sngl p f q = if q =ₛ p then just f else nothing

{-
sub1 : Subst Var
sub1 = sngl "p" (And (Atom "p") (Atom "q"))

frm3 : String
frm3 = "p /\\ q /\\ p /\\ q"

_ : "(p ∧ q) ∧ q ∧ (p ∧ q) ∧ q" ＝ ppF (psubst sub1) frm3
_ = refl
-}

eval-subst-sngl : {x : Var} {p q : Form} {v : Val Var}
                → eval (psubst (sngl x q) p) v ＝ eval p (modify x (eval q v) v)
eval-subst-sngl     {p = False}          = refl
eval-subst-sngl     {p = True}           = refl
eval-subst-sngl {x} {p = Atom a} {q} {v} =
  Dec.elim
   {C = λ z → eval (psubst (sngl x q) (Atom a)) v ＝ (if ⌊ z ⌋ then eval q v else v a)}
   (λ a=x → ap (λ z → eval (from-just (Atom a) z) v)
               (if-true {b = a =ₛ x}
                        (subst So (string→list-=ₛ {s₁ = a} ⁻¹) (true→so! a=x))))
   (λ a≠x → ap (λ z → eval (from-just (Atom a) z) v)
               (if-false {b = a =ₛ x}
                         (subst (So ∘ not) (string→list-=ₛ {s₁ = a} ⁻¹) (false→so! a≠x))))
   (a ≟ x)
eval-subst-sngl     {p = Not x}          =
  ap not (eval-subst-sngl {p = x})
eval-subst-sngl     {p = And x y}        =
  ap² _and_ (eval-subst-sngl {p = x}) (eval-subst-sngl {p = y})
eval-subst-sngl     {p = Or x y}         =
  ap² _or_ (eval-subst-sngl {p = x}) (eval-subst-sngl {p = y})
eval-subst-sngl     {p = Imp x y}        =
  ap² _implies_ (eval-subst-sngl {p = x}) (eval-subst-sngl {p = y})
eval-subst-sngl     {p = Iff x y}        =
  ap² _equals_ (eval-subst-sngl {p = x}) (eval-subst-sngl {p = y})

-- TODO eval-tautology

{-
_ : true ∈ (tautology <$> parseForm "(p => q) \\/ (q => p)")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "p \\/ (q <=> r) <=> (p \\/ q <=> p \\/ r)")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "p /\\ q <=> ((p <=> q) <=> p \\/ q)")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "(p => q) <=> (~q => ~p)")
_ = hereₘ refl

_ : true ∈ (tautology <$> parseForm "(p => ~q) <=> (q => ~p)")
_ = hereₘ refl

_ : false ∈ (tautology <$> parseForm "(p => q) <=> (q => p)")
_ = hereₘ refl
-}

-- TODO eval-singl-agree

{-
imp-bot-forms : List String
imp-bot-forms = "true <=> false => false"
              ∷ "~p <=> p => false"
              ∷ "p /\\ q <=> (p => q => false) => false"
              ∷ "p \\/ q <=> (p => false) => q"
              ∷ "(p <=> q) <=> ((p => q) => (q => p) => false) => false"
              ∷ []

_ : All (true ∈_) ((map tautology ∘ parseForm) <$> imp-bot-forms)
_ = hereₘ refl ∷ hereₘ refl ∷ hereₘ refl ∷ hereₘ refl ∷ hereₘ refl ∷ []
-}

-- duality (kinda pointless)

data FormulaD (A : 𝒰) : 𝒰 where
  FalseD : FormulaD A
  TrueD  : FormulaD A
  AtomD  : A → FormulaD A
  NotD   : FormulaD A → FormulaD A
  AndD   : FormulaD A → FormulaD A → FormulaD A
  OrD    : FormulaD A → FormulaD A → FormulaD A

emb : FormulaD A → Formula A
emb  FalseD    = False
emb  TrueD     = True
emb (AtomD a)  = Atom a
emb (NotD x)   = Not (emb x)
emb (AndD x y) = And (emb x) (emb y)
emb (OrD x y)  = Or (emb x) (emb y)

dual : FormulaD A → FormulaD A
dual  FalseD    = TrueD
dual  TrueD     = FalseD
dual (AtomD a)  = AtomD a
dual (NotD x)   = NotD (dual x)
dual (AndD x y) = OrD (dual x) (dual y)
dual (OrD x y)  = AndD (dual x) (dual y)

dual-inv : (f : FormulaD A)
         → dual (dual f) ＝ f
dual-inv FalseD     = refl
dual-inv TrueD      = refl
dual-inv (AtomD a)  = refl
dual-inv (NotD x)   = ap NotD (dual-inv x)
dual-inv (AndD x y) = ap² AndD (dual-inv x) (dual-inv y)
dual-inv (OrD x y)  = ap² OrD (dual-inv x) (dual-inv y)

-- TODO
{-
eval-dual : {A : 𝒰}
          → (f : FormulaD A) {v : Val A}
          → eval (emb (dual f)) v ＝ not (eval (emb f) (not ∘ v))
-}
--- + corollary

{-
main : Main
main = run $ do s ← get-line
                Maybe.rec (put-str-ln "parse error!")
                          (λ f → do put-str-ln $ "truth table for:" ++ₛ prettyF f
                                    put-str-ln $ truth-table f
                                    put-str-ln $ "tautology = " ++ₛ (if tautology f then "YES" else "NO"))
                          (parseForm s)
-}
