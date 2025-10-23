module SAT.Formula where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect using (Effect; Bind-Id ; map)
open Variadics _
open import Logic.Discreteness
open import Functions.Embedding
open import System.Everything

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Sum
open import Data.Nat
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.List
open import Data.List.Correspondences.Unary.Any

open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total

open import Level.Bounded
import Induction.Nat.Strong as INS
open import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface as SZ

open import LFSet
open import LFSet.Membership

open import Base 0ℓ
open import Text.Pretty 80 public renaming (text to textD ; char to charD ; parens to parensD)

open import SAT.Formula0 hiding (Doc ; textD ; charD ; _◆_ ; _◈_ ; sep ; render)
open import SAT.Sem

private variable
  A B : 𝒰
  Γ Δ : LFSet A

data Formulaᵢ (Γ : LFSet A) : 𝒰 where
  False : Formulaᵢ Γ
  True  : Formulaᵢ Γ
  Atom  : (a : A) → a ∈ Γ → Formulaᵢ Γ          -- ideally membership shoud be erased
  Not   : Formulaᵢ Γ → Formulaᵢ Γ
  And   : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ
  Or    : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ
  Imp   : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ
  Iff   : Formulaᵢ Γ → Formulaᵢ Γ → Formulaᵢ Γ

wk : {Γ Δ : LFSet A}
   → Γ ⊆ Δ → Formulaᵢ Γ → Formulaᵢ Δ
wk s  False     = False
wk s  True      = True
wk s (Atom a m) = Atom a (s m)
wk s (Not x)    = Not (wk s x)
wk s (And x y)  = And (wk s x) (wk s y)
wk s (Or x y)   = Or (wk s x) (wk s y)
wk s (Imp x y)  = Imp (wk s x) (wk s y)
wk s (Iff x y)  = Iff (wk s x) (wk s y)

height : {Γ : LFSet A} → Formulaᵢ Γ → ℕ
height  False     = 0
height  True      = 0
height (Atom _ _) = 0
height (Not x)    = 1 + height x
height (And x y)  = 1 + max (height x) (height y)
height (Or x y)   = 1 + max (height x) (height y)
height (Imp x y)  = 1 + max (height x) (height y)
height (Iff x y)  = 1 + max (height x) (height y)

height-wk : {Γ Δ : LFSet A}
          → {s : Γ ⊆ Δ}
          → (f : Formulaᵢ Γ) → height (wk s f) ＝ height f
height-wk  False     = refl
height-wk  True      = refl
height-wk (Atom a m) = refl
height-wk (Not f)    = ap suc (height-wk f)
height-wk (And p q)  = ap² (λ x y → 1 + max x y) (height-wk p) (height-wk q)
height-wk (Or  p q)  = ap² (λ x y → 1 + max x y) (height-wk p) (height-wk q)
height-wk (Imp p q)  = ap² (λ x y → 1 + max x y) (height-wk p) (height-wk q)
height-wk (Iff p q)  = ap² (λ x y → 1 + max x y) (height-wk p) (height-wk q)

-- sem

evalᵢ : {Γ : LFSet A}
      → Formulaᵢ Γ → Val A → Bool
evalᵢ  False     v = false
evalᵢ  True      v = true
evalᵢ (Atom a _) v = v a
evalᵢ (Not x)    v = not (evalᵢ x v)
evalᵢ (And x y)  v = evalᵢ x v and evalᵢ y v
evalᵢ (Or x y)   v = evalᵢ x v or evalᵢ y v
evalᵢ (Imp x y)  v = evalᵢ x v implies evalᵢ y v
evalᵢ (Iff x y)  v = evalᵢ x v equals evalᵢ y v


module Fcodeᵢ where

  Code : Formulaᵢ Γ → Formulaᵢ Γ → 𝒰
  Code  False       False        = ⊤
  Code  True        True         = ⊤
  Code (Atom a1 _)   (Atom a2 _) = a1 ＝ a2
  Code (Not x1)    (Not x2)      = Code x1 x2
  Code (And x1 y1) (And x2 y2)   = Code x1 x2 × Code y1 y2
  Code (Or x1 y1)  (Or x2 y2)    = Code x1 x2 × Code y1 y2
  Code (Imp x1 y1) (Imp x2 y2)   = Code x1 x2 × Code y1 y2
  Code (Iff x1 y1) (Iff x2 y2)   = Code x1 x2 × Code y1 y2
  Code  _           _            = ⊥

  code-refl : (F : Formulaᵢ Γ) → Code F F
  code-refl  False      = tt
  code-refl  True       = tt
  code-refl (Atom a _)  = refl
  code-refl (Not f)     = code-refl f
  code-refl (And f1 f2) = code-refl f1 , code-refl f2
  code-refl (Or f1 f2)  = code-refl f1 , code-refl f2
  code-refl (Imp f1 f2) = code-refl f1 , code-refl f2
  code-refl (Iff f1 f2) = code-refl f1 , code-refl f2

  encode : {F G : Formulaᵢ Γ} → F ＝ G → Code F G
  encode {F} e = subst (Code F) e (code-refl F)

  decode : {F G : Formulaᵢ Γ} → Code F G → F ＝ G
  decode     {F = False}      {G = False}       tt       = refl
  decode     {F = True}       {G = True}        tt       = refl
  decode     {F = Atom a1 m1} {G = Atom a2 m2}  c        =
    ap² (λ x y → Atom x y) c (to-pathᴾ (hlevel 1 _ m2))
  decode     {F = Not F}      {G = Not G}       c        =
    ap Not (decode {F = F} c)
  decode {Γ} {F = And F1 F2}  {G = And G1 G2}  (c1 , c2) =
    ap² {C = λ _ _ → Formulaᵢ Γ}
        And (decode {F = F1} c1) (decode {F = F2} c2)
  decode {Γ} {F = Or F1 F2}   {G = Or G1 G2}   (c1 , c2) =
    ap² {C = λ _ _ → Formulaᵢ Γ}
        Or (decode {F = F1} c1) (decode {F = F2} c2)
  decode {Γ} {F = Imp F1 F2}  {G = Imp G1 G2}  (c1 , c2) =
    ap² {C = λ _ _ → Formulaᵢ Γ}
        Imp (decode {F = F1} c1) (decode {F = F2} c2)
  decode {Γ} {F = Iff F1 F2}  {G = Iff G1 G2}  (c1 , c2) =
    ap² {C = λ _ _ → Formulaᵢ Γ}
        Iff (decode {F = F1} c1) (decode {F = F2} c2)

Formᵢ-= : {Γ : LFSet A}
       → (A → A → Bool)
       → Formulaᵢ Γ → Formulaᵢ Γ → Bool
Formᵢ-= e  False        False      = true
Formᵢ-= e  True         True       = true
Formᵢ-= e (Atom a1 _)  (Atom a2 _) = e a1 a2
Formᵢ-= e (Not x1)     (Not x2)    = Formᵢ-= e x1 x2
Formᵢ-= e (And x1 y1)  (And x2 y2) = Formᵢ-= e x1 x2 and Formᵢ-= e y1 y2
Formᵢ-= e (Or x1 y1)   (Or x2 y2)  = Formᵢ-= e x1 x2 and Formᵢ-= e y1 y2
Formᵢ-= e (Imp x1 y1)  (Imp x2 y2) = Formᵢ-= e x1 x2 and Formᵢ-= e y1 y2
Formᵢ-= e (Iff x1 y1)  (Iff x2 y2) = Formᵢ-= e x1 x2 and Formᵢ-= e y1 y2
Formᵢ-= e  _            _          = false

instance
  Reflects-Formᵢ-= : {Γ : LFSet A} {e : A → A → Bool} ⦃ r : ∀ {x y} → Reflects (x ＝ y) (e x y) ⦄
                     {f g : Formulaᵢ Γ}
                   → Reflects (f ＝ g) (Formᵢ-= e f g)
  Reflects-Formᵢ-=       {f = False}      {g = False}     = ofʸ refl
  Reflects-Formᵢ-=       {f = False}      {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = Atom a2 _} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = False}      {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = True}      = ofʸ refl
  Reflects-Formᵢ-=       {f = True}       {g = Atom a2 _} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = True}       {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}  {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}  {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-= ⦃ r ⦄ {f = Atom a1 m1} {g = Atom a2 m2} =
    Reflects.dmap (λ e → ap² Atom e (to-pathᴾ (hlevel 1 _ m2)))
                  (contra Fcodeᵢ.encode) r
  Reflects-Formᵢ-=       {f = Atom a1 _}   {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}   {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}   {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}   {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Atom a1 _}   {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = Atom a2 _}   = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = Not x2}    =
    Reflects.dmap (ap Not)
                  (contra (Fcodeᵢ.decode ∘ Fcodeᵢ.encode))
                  (Reflects-Formᵢ-= {f = x1} {g = x2})
  Reflects-Formᵢ-=       {f = Not x1}    {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Not x1}    {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = Atom a2 _}   = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = And x2 y2} =
    Reflects.dmap ((λ e1 → ap² And e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcodeᵢ.encode e in
                                Fcodeᵢ.decode c1 , Fcodeᵢ.decode c2
                  )
                  (Reflects-× ⦃ rp = Reflects-Formᵢ-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Formᵢ-= {f = y1} {g = y2} ⦄)
  Reflects-Formᵢ-=       {f = And x1 y1} {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = And x1 y1} {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = Atom a2 _}   = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = Or x2 y2}  =
    Reflects.dmap ((λ e1 → ap² Or e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcodeᵢ.encode e in
                                Fcodeᵢ.decode c1 , Fcodeᵢ.decode c2
                  )
                  (Reflects-× ⦃ rp = Reflects-Formᵢ-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Formᵢ-= {f = y1} {g = y2} ⦄)
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Or x1 y1}  {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = Atom a2 _}   = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = Or x2 y2}  = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = Imp x2 y2} =
    Reflects.dmap ((λ e1 → ap² Imp e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcodeᵢ.encode e in
                                Fcodeᵢ.decode c1 , Fcodeᵢ.decode c2
                  )
                  (Reflects-× ⦃ rp = Reflects-Formᵢ-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Formᵢ-= {f = y1} {g = y2} ⦄)
  Reflects-Formᵢ-=       {f = Imp x1 y1} {g = Iff x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = False}     = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = True}      = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = Atom x2 _} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = Not x2}    = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = And x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = Or  x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = Imp x2 y2} = ofⁿ Fcodeᵢ.encode
  Reflects-Formᵢ-=       {f = Iff x1 y1} {g = Iff x2 y2} =
    Reflects.dmap ((λ e1 → ap² Iff e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcodeᵢ.encode e in
                                Fcodeᵢ.decode c1 , Fcodeᵢ.decode c2
                  )
                  (Reflects-× ⦃ rp = Reflects-Formᵢ-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Formᵢ-= {f = y1} {g = y2} ⦄)
  {-# OVERLAPPABLE Reflects-Formᵢ-= #-}

  Formᵢ-is-discrete : {Γ : LFSet A} ⦃ d : is-discrete A ⦄ → is-discrete (Formulaᵢ Γ)
  Formᵢ-is-discrete ⦃ d ⦄ {x} {y} .does  = Formᵢ-= (λ x y → d {x = x} {y = y} .does) x y
  Formᵢ-is-discrete               .proof = Reflects-Formᵢ-=

wk-inj : {Γ Δ : LFSet A} {s : Γ ⊆ Δ}
       -- not necessary but makes proof more compact by skipping impossible cases
       → ⦃ d : is-discrete A ⦄
       → Injective (wk s)
wk-inj {Γ} {s} ⦃ d ⦄ {x} {y} = aux x y ∘ true→so!
  where
  aux : (x y : Formulaᵢ Γ)
      → ⌞ Formᵢ-= (λ p q → ⌊ d {x = p} {y = q} ⌋) (wk s x) (wk s y) ⌟
      → x ＝ y
  aux  False        False       e = refl
  aux  True         True        e = refl
  aux (Atom a1 m1) (Atom a2 m2) e = ap² Atom (the (a1 ＝ a2) (so→true! e)) (to-pathᴾ (hlevel 1 _ m2))
  aux (Not p1)     (Not p2)     e = ap Not (aux p1 p2 e)
  aux (And p1 q1)  (And p2 q2)  e =
    let e12 = and-so-≃ $ e in
    ap² {C = λ _ _ → Formulaᵢ Γ} And (aux p1 p2 (e12 .fst)) (aux q1 q2 (e12 .snd))
  aux (Or p1 q1)   (Or p2 q2)   e =
    let e12 = and-so-≃ $ e in
    ap² {C = λ _ _ → Formulaᵢ Γ} Or (aux p1 p2 (e12 .fst)) (aux q1 q2 (e12 .snd))
  aux (Imp p1 q1)  (Imp p2 q2)  e =
    let e12 = and-so-≃ $ e in
    ap² {C = λ _ _ → Formulaᵢ Γ} Imp (aux p1 p2 (e12 .fst)) (aux q1 q2 (e12 .snd))
  aux (Iff p1 q1)  (Iff p2 q2)  e =
    let e12 = and-so-≃ $ e in
    ap² {C = λ _ _ → Formulaᵢ Γ} Iff (aux p1 p2 (e12 .fst)) (aux q1 q2 (e12 .snd))

elim-formulaᵢ
  : (P : (Γ : LFSet A) → Formulaᵢ Γ → 𝒰)
  → ({Γ : LFSet A} → P Γ False)
  → ({Γ : LFSet A} → P Γ True)
  → (∀ {Γ : LFSet A} a (a∈ : a ∈ Γ) → P Γ (Atom a a∈))
  → (∀ {Γ : LFSet A} {x} → P Γ x → P Γ (Not x))
  → (∀ {Γ : LFSet A} {x y} → P Γ x → P Γ y → P Γ (And x y))
  → (∀ {Γ : LFSet A} {x y} → P Γ x → P Γ y → P Γ (Or x y))
  → (∀ {Γ : LFSet A} {x y} → P Γ x → P Γ y → P Γ (Imp x y))
  → (∀ {Γ : LFSet A} {x y} → P Γ x → P Γ y → P Γ (Iff x y))
  → {Γ : LFSet A} → ∀ x → P Γ x
elim-formulaᵢ P pf pt pa pn pand por pimp piff  False      = pf
elim-formulaᵢ P pf pt pa pn pand por pimp piff  True       = pt
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Atom a a∈) = pa a a∈
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Not x)     =
  pn (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (And x y)   =
  pand (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Or x y)    =
  por (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
      (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Imp x y)   =
  pimp (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Iff x y)   =
  piff (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)

{-
elim-formulaᵢ
  : {Γ : LFSet A} (P : Formulaᵢ Γ → 𝒰)
  → P False
  → P True
  → (∀ a (a∈ : a ∈ Γ) → P (Atom a a∈))
  → (∀ {x} → P x → P (Not x))
  → (∀ {x y} → P x → P y → P (And x y))
  → (∀ {x y} → P x → P y → P (Or x y))
  → (∀ {x y} → P x → P y → P (Imp x y))
  → (∀ {x y} → P x → P y → P (Iff x y))
  → ∀ x → P x
elim-formulaᵢ P pf pt pa pn pand por pimp piff  False      = pf
elim-formulaᵢ P pf pt pa pn pand por pimp piff  True       = pt
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Atom a a∈) = pa a a∈
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Not x)     =
  pn (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (And x y)   =
  pand (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Or x y)    =
  por (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
      (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Imp x y)   =
  pimp (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
elim-formulaᵢ P pf pt pa pn pand por pimp piff (Iff x y)   =
  piff (elim-formulaᵢ P pf pt pa pn pand por pimp piff x)
       (elim-formulaᵢ P pf pt pa pn pand por pimp piff y)
-}

-- atom-set

{-
atomsrₛ : Formula A → LFSet A
atomsrₛ  False    = []
atomsrₛ  True     = []
atomsrₛ (Atom x)  = x ∷ []
atomsrₛ (Not x)   = atomsrₛ x
atomsrₛ (And x y) = atomsrₛ x ∪∷ atomsrₛ y
atomsrₛ (Or x y)  = atomsrₛ x ∪∷ atomsrₛ y
atomsrₛ (Imp x y) = atomsrₛ x ∪∷ atomsrₛ y
atomsrₛ (Iff x y) = atomsrₛ x ∪∷ atomsrₛ y
-}

chk : (f : Formula A) → Formulaᵢ (atomsₛ f)
chk  False    = False
chk  True     = True
chk (Atom a)  = Atom a (hereₛ refl)
chk (Not x)   = Not (chk x)
chk (And x y) =
  And (wk ∈ₛ-∪∷←l (chk x)) (wk (∈ₛ-∪∷←r {s₁ = atomsₛ x}) (chk y))
chk (Or x y)  =
  Or (wk ∈ₛ-∪∷←l (chk x)) (wk (∈ₛ-∪∷←r {s₁ = atomsₛ x}) (chk y))
chk (Imp x y) =
  Imp (wk ∈ₛ-∪∷←l (chk x)) (wk (∈ₛ-∪∷←r {s₁ = atomsₛ x}) (chk y))
chk (Iff x y) =
  Iff (wk ∈ₛ-∪∷←l (chk x)) (wk (∈ₛ-∪∷←r {s₁ = atomsₛ x}) (chk y))

ers : {Γ : LFSet A}
    → Formulaᵢ Γ → Formula A
ers  False     = False
ers  True      = True
ers (Atom a _) = Atom a
ers (Not x)    = Not (ers x)
ers (And x y)  = And (ers x) (ers y)
ers (Or x y)   = Or (ers x) (ers y)
ers (Imp x y)  = Imp (ers x) (ers y)
ers (Iff x y)  = Iff (ers x) (ers y)

on-atomsᵢ : {Γ Δ : LFSet A}
         → ({Γ : LFSet A} → (a : A) → a ∈ Γ → Formulaᵢ Δ) → Formulaᵢ Γ → Formulaᵢ Δ
on-atomsᵢ {Γ} {Δ} f =
 elim-formulaᵢ (λ _ _ → Formulaᵢ Δ)
   False True f
   Not And Or Imp Iff

{-
on-atomsᵢ f  False    = False
on-atomsᵢ f  True     = True
on-atomsᵢ f (Atom a m) = f a
on-atomsᵢ f (Not x)   = Not (on-atomsᵢ f x)
on-atomsᵢ f (And x y) = And (on-atomsᵢ f x) (on-atomsᵢ f y)
on-atomsᵢ f (Or x y)  = Or (on-atomsᵢ f x) (on-atomsᵢ f y)
on-atomsᵢ f (Imp x y) = Imp (on-atomsᵢ f x) (on-atomsᵢ f y)
on-atomsᵢ f (Iff x y) = Iff (on-atomsᵢ f x) (on-atomsᵢ f y)
-}

over-atomsᵢ : {Γ : LFSet A}
           → (A → B → B) → Formulaᵢ Γ → B → B
over-atomsᵢ {B} f =
 elim-formulaᵢ (λ _ _ → B → B)
   id id (λ a _ → f a)
   id
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)

{-
over-atomsᵢ f  False    b = b
over-atomsᵢ f  True     b = b
over-atomsᵢ f (Atom a m)  b = f a b
over-atomsᵢ f (Not x)   b = over-atomsᵢ f x b
over-atomsᵢ f (And x y) b = over-atomsᵢ f x (over-atomsᵢ f y b)
over-atomsᵢ f (Or x y)  b = over-atomsᵢ f x (over-atomsᵢ f y b)
over-atomsᵢ f (Imp x y) b = over-atomsᵢ f x (over-atomsᵢ f y b)
over-atomsᵢ f (Iff x y) b = over-atomsᵢ f x (over-atomsᵢ f y b)
-}

atom-listᵢ : {Γ : LFSet A}
           → (A → List B) → Formulaᵢ Γ → List B
atom-listᵢ f fm = over-atomsᵢ (λ h → f h ++_) fm []

atoms-listᵢ : {Γ : LFSet A}
            → Formulaᵢ Γ → List A
atoms-listᵢ = atom-listᵢ (_∷ [])

atom-unionᵢ : {Γ : LFSet A}
            → ⦃ d : is-discrete B ⦄
            → (A → List B) → Formulaᵢ Γ → List B
atom-unionᵢ f fm = nub _=?_ $ atom-listᵢ f fm

atomsᵢ : {Γ : LFSet A}
       → ⦃ d : is-discrete A ⦄
       → Formulaᵢ Γ → List A
atomsᵢ f = nub _=?_ $ atoms-listᵢ f

atomsᵢ-⊆ : {Γ : LFSet A}
         → ⦃ d : is-discrete A ⦄
         → {f : Formulaᵢ Γ}
         → atoms-listᵢ f ⊆ Γ
atomsᵢ-⊆ {A} {f} =
  elim-formulaᵢ (λ g q → (zs : List A) → zs ⊆ g → over-atomsᵢ _∷_ q zs ⊆ g)
     (λ zs → id)
     (λ zs → id)
     (λ {Γ} a a∈ zs zs⊆ →
         [ (λ e → subst (_∈ Γ) (e ⁻¹) a∈)
         , zs⊆ ]ᵤ ∘ any-uncons)
     (λ ih zs zs⊆ → ih zs zs⊆)
     (λ {Γ} {x} {y} ihl ihr zs zs⊆ →
         ihl (over-atomsᵢ _∷_ y zs) (ihr zs zs⊆))
     (λ {Γ} {x} {y} ihl ihr zs zs⊆ →
         ihl (over-atomsᵢ _∷_ y zs) (ihr zs zs⊆))
     (λ {Γ} {x} {y} ihl ihr zs zs⊆ →
         ihl (over-atomsᵢ _∷_ y zs) (ihr zs zs⊆))
     (λ {Γ} {x} {y} ihl ihr zs zs⊆ →
         ihl (over-atomsᵢ _∷_ y zs) (ihr zs zs⊆))
     f
     [] false!
{-
atomsᵢ-⊆ {f = False}               = false!
atomsᵢ-⊆ {f = True}                = false!
atomsᵢ-⊆ {Γ} {f = Atom a m} {x = z} z∈ =
  subst (_∈ Γ) ([ _⁻¹ , false! ]ᵤ (any-uncons z∈)) m
atomsᵢ-⊆ {f = Not x}    {x = z} z∈ = atomsᵢ-⊆ {f = x} z∈
atomsᵢ-⊆ {f = And x y}  {x = z} z∈ =
  let ih1 = atomsᵢ-⊆ {f = y}
      ih2 = atomsᵢ-⊆ {f = x}
    in
  {!ih2 ?!}
atomsᵢ-⊆ {f = Or x y}   {x = z} z∈ = {!!}
atomsᵢ-⊆ {f = Imp x y}  {x = z} z∈ = {!!}
atomsᵢ-⊆ {f = Iff x y}  {x = z} z∈ = {!!}
-}

Ctx : 𝒰
Ctx = LFSet Var


-- printer

prettyFormᵢ : {Γ : Ctx}
            → ℕ → Formulaᵢ Γ → Doc
prettyFormᵢ p False      = textD "false"
prettyFormᵢ p True       = textD "true"
prettyFormᵢ p (Atom v _) = textD v
prettyFormᵢ p (Not x)    = brk (10 <? p) $ charD '¬' ◆ prettyFormᵢ 11 x
prettyFormᵢ p (And x y)  = brk (8 <? p) $ sep $ (prettyFormᵢ 9 x ◈ charD '∧') ∷ prettyFormᵢ 8 y ∷ []
prettyFormᵢ p (Or x y)   = brk (6 <? p) $ sep $ (prettyFormᵢ 7 x ◈ charD '∨') ∷ prettyFormᵢ 6 y ∷ []
prettyFormᵢ p (Imp x y)  = brk (4 <? p) $ sep $ (prettyFormᵢ 5 x ◈ charD '⇒') ∷ prettyFormᵢ 4 y ∷ []
prettyFormᵢ p (Iff x y)  = brk (2 <? p) $ sep $ (prettyFormᵢ 3 x ◈ charD '⇔') ∷ prettyFormᵢ 2 y ∷ []

prettyFᵢ : {Γ : Ctx}
         → Formulaᵢ Γ → String
prettyFᵢ = render ∘ prettyFormᵢ 0

-- TODO generalize?

ppFᵢ : ({Γ : Ctx} → Formulaᵢ Γ → Formulaᵢ Γ) → String → String
ppFᵢ f s =
  Maybe.rec
    "parse error"
    (prettyFᵢ ∘ f ∘ chk)
    (parseForm s)

ppFΣᵢ : ({Γ : Ctx} → Formulaᵢ Γ → Σ[ Δ ꞉ Ctx ] (Formulaᵢ (Δ ∪∷ Γ))) → String → String
ppFΣᵢ f s =
  Maybe.rec
    "parse error"
    -- TODO print new vars for debug too?
    (prettyFᵢ ∘ snd ∘ f ∘ chk)
    (parseForm s)

ppFBᵢ : ({Γ : Ctx} → Formulaᵢ Γ → Bool) → Formula Var → String
ppFBᵢ f = Prelude.show ∘ f ∘ chk

-- tests

{-
ctx1 : LFSet String
ctx1 = "p" ∷ "q" ∷ "r" ∷ []

f1 : Formulaᵢ ctx1
f1 = Imp (Or (Atom "p" (hereₛ refl))
             (Atom "q" (thereₛ $ hereₛ refl)))
         (Atom "r" (thereₛ $ thereₛ $ hereₛ refl))

_ : "p \\/ q => r" ∈F
_ = f1 !

_ : prettyF f1 ＝ "p ∨ q ⇒ r"
_ = refl

f2 : Form
f2 = Iff (Imp (Atom "p") (Atom "q"))
         (Or (And (Atom "r") (Atom "s"))
             (Iff (Atom "t")
                  (And (Not (Not (Atom "u")))
                       (Atom "v"))))

_ : "p => q <=> r /\\ s \\/ (t <=> ~ ~u /\\ v)" ∈F
_ = f2 !

_ : prettyF f2 ＝ "p ⇒ q ⇔ r ∧ s ∨ (t ⇔ ¬(¬u) ∧ v)"
_ = refl

main : Main
main = run $ do
  put-str-ln "f1"
  put-str-ln $ prettyF f1
  put-str-ln "f2"
  put-str-ln $ prettyF f2
  put-str-ln "f2∧f2"
  put-str-ln $ prettyF (And f2 f2)
  put-str-ln "(f2∨f2)∧f2"
  put-str-ln $ prettyF (And (Or f2 f2) f2)
-}
