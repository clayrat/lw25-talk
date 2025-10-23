module SAT.Formula0 where

open import Foundations.Prelude
open import Meta.Effect using (Effect; Bind-Id)
open Variadics _
open import Logic.Discreteness
open import System.Everything

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec
open import Data.Nat
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.List
open import Data.List.Correspondences.Unary.Any

open import Level.Bounded
import Induction.Nat.Strong as INS
open import Data.List.NonEmpty as List⁺
open import Data.List.Sized.Interface as SZ

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Base 0ℓ
open import Text.Pretty 80 public renaming (text to textD ; char to charD ; parens to parensD)

private variable
  A B : 𝒰

data Formula (A : 𝒰) : 𝒰 where
  False : Formula A
  True  : Formula A
  Atom  : A → Formula A
  Not   : Formula A → Formula A
  And   : Formula A → Formula A → Formula A
  Or    : Formula A → Formula A → Formula A
  Imp   : Formula A → Formula A → Formula A
  Iff   : Formula A → Formula A → Formula A

module Fcode where

  Code : Formula A → Formula A → 𝒰
  Code  False       False      = ⊤
  Code  True        True       = ⊤
  Code (Atom a1)   (Atom a2)   = a1 ＝ a2
  Code (Not x1)    (Not x2)    = Code x1 x2
  Code (And x1 y1) (And x2 y2) = Code x1 x2 × Code y1 y2
  Code (Or x1 y1)  (Or x2 y2)  = Code x1 x2 × Code y1 y2
  Code (Imp x1 y1) (Imp x2 y2) = Code x1 x2 × Code y1 y2
  Code (Iff x1 y1) (Iff x2 y2) = Code x1 x2 × Code y1 y2
  Code  _           _          = ⊥

  code-refl : (F : Formula A) → Code F F
  code-refl  False      = tt
  code-refl  True       = tt
  code-refl (Atom a)    = refl
  code-refl (Not f)     = code-refl f
  code-refl (And f1 f2) = code-refl f1 , code-refl f2
  code-refl (Or f1 f2)  = code-refl f1 , code-refl f2
  code-refl (Imp f1 f2) = code-refl f1 , code-refl f2
  code-refl (Iff f1 f2) = code-refl f1 , code-refl f2

  encode : {F G : Formula A} → F ＝ G → Code F G
  encode {F} e = subst (Code F) e (code-refl F)

  decode : {F G : Formula A} → Code F G → F ＝ G
  decode {F = False}     {G = False}      tt       = refl
  decode {F = True}      {G = True}       tt       = refl
  decode {F = Atom a1}   {G = Atom a2}    c        = ap Atom c
  decode {F = Not F}     {G = Not G}      c        = ap Not (decode c)
  decode {F = And F1 F2} {G = And G1 G2} (c1 , c2) = ap² And (decode c1) (decode c2)
  decode {F = Or F1 F2}  {G = Or G1 G2}  (c1 , c2) = ap² Or (decode c1) (decode c2)
  decode {F = Imp F1 F2} {G = Imp G1 G2} (c1 , c2) = ap² Imp (decode c1) (decode c2)
  decode {F = Iff F1 F2} {G = Iff G1 G2} (c1 , c2) = ap² Iff (decode c1) (decode c2)

Form-= : (A → A → Bool)
       → Formula A → Formula A → Bool
Form-= e  False       False      = true
Form-= e  True        True       = true
Form-= e (Atom a1)   (Atom a2)   = e a1 a2
Form-= e (Not x1)    (Not x2)    = Form-= e x1 x2
Form-= e (And x1 y1) (And x2 y2) = Form-= e x1 x2 and Form-= e y1 y2
Form-= e (Or x1 y1)  (Or x2 y2)  = Form-= e x1 x2 and Form-= e y1 y2
Form-= e (Imp x1 y1) (Imp x2 y2) = Form-= e x1 x2 and Form-= e y1 y2
Form-= e (Iff x1 y1) (Iff x2 y2) = Form-= e x1 x2 and Form-= e y1 y2
Form-= e  _           _          = false

instance
  Reflects-Form-= : {e : A → A → Bool} ⦃ r : ∀ {x y} → Reflects (x ＝ y) (e x y) ⦄
                    {f g : Formula A}
                  → Reflects (f ＝ g) (Form-= e f g)
  Reflects-Form-=       {f = False}     {g = False}     = ofʸ refl
  Reflects-Form-=       {f = False}     {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = False}     {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = True}      = ofʸ refl
  Reflects-Form-=       {f = True}      {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = True}      {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-= ⦃ r ⦄ {f = Atom a1}   {g = Atom a2}   =
    Reflects.dmap (ap Atom) (contra Fcode.encode) r
  Reflects-Form-=       {f = Atom a1}   {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Atom a1}   {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = Not x2}    =
    Reflects.dmap (ap Not)
                  (contra (Fcode.decode ∘ Fcode.encode))
                  (Reflects-Form-= {f = x1} {g = x2})
  Reflects-Form-=       {f = Not x1}    {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Not x1}    {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = And x2 y2} =
    Reflects.dmap ((λ e1 → ap² And e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcode.encode e in
                                Fcode.decode c1 , Fcode.decode c2)
                  (Reflects-× ⦃ rp = Reflects-Form-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Form-= {f = y1} {g = y2} ⦄)
  Reflects-Form-=       {f = And x1 y1} {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = And x1 y1} {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = Or x2 y2}  =
    Reflects.dmap ((λ e1 → ap² Or e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcode.encode e in
                                Fcode.decode c1 , Fcode.decode c2)
                  (Reflects-× ⦃ rp = Reflects-Form-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Form-= {f = y1} {g = y2} ⦄)
  Reflects-Form-=       {f = Or x1 y1}  {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Or x1 y1}  {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = Atom a2}   = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = Or x2 y2}  = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Imp x1 y1} {g = Imp x2 y2} =
    Reflects.dmap ((λ e1 → ap² Imp e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcode.encode e in
                                Fcode.decode c1 , Fcode.decode c2)
                  (Reflects-× ⦃ rp = Reflects-Form-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Form-= {f = y1} {g = y2} ⦄)
  Reflects-Form-=       {f = Imp x1 y1} {g = Iff x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = False}     = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = True}      = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = Atom x}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = Not x2}    = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = And x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = Or  x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = Imp x2 y2} = ofⁿ Fcode.encode
  Reflects-Form-=       {f = Iff x1 y1} {g = Iff x2 y2} =
    Reflects.dmap ((λ e1 → ap² Iff e1) $²_)
                  (contra λ e → let (c1 , c2) = Fcode.encode e in
                                Fcode.decode c1 , Fcode.decode c2)
                  (Reflects-× ⦃ rp = Reflects-Form-= {f = x1} {g = x2} ⦄
                              ⦃ rq = Reflects-Form-= {f = y1} {g = y2} ⦄)
  {-# OVERLAPPABLE Reflects-Form-= #-}

  Form-is-discrete : ⦃ d : is-discrete A ⦄ → is-discrete (Formula A)
  Form-is-discrete ⦃ d ⦄ {x} {y} .does  = Form-= (λ x y → d {x = x} {y = y} .does) x y
  Form-is-discrete               .proof = Reflects-Form-=

elim-formula
  : (P : Formula A → 𝒰)
  → P False
  → P True
  → (∀ a → P (Atom a))
  → (∀ {x} → P x → P (Not x))
  → (∀ {x y} → P x → P y → P (And x y))
  → (∀ {x y} → P x → P y → P (Or x y))
  → (∀ {x y} → P x → P y → P (Imp x y))
  → (∀ {x y} → P x → P y → P (Iff x y))
  → ∀ x → P x
elim-formula P pf pt pa pn pand por pimp piff  False    = pf
elim-formula P pf pt pa pn pand por pimp piff  True     = pt
elim-formula P pf pt pa pn pand por pimp piff (Atom a)  = pa a
elim-formula P pf pt pa pn pand por pimp piff (Not x)   =
  pn (elim-formula P pf pt pa pn pand por pimp piff x)
elim-formula P pf pt pa pn pand por pimp piff (And x y) =
  pand (elim-formula P pf pt pa pn pand por pimp piff x)
       (elim-formula P pf pt pa pn pand por pimp piff y)
elim-formula P pf pt pa pn pand por pimp piff (Or x y)  =
  por (elim-formula P pf pt pa pn pand por pimp piff x)
      (elim-formula P pf pt pa pn pand por pimp piff y)
elim-formula P pf pt pa pn pand por pimp piff (Imp x y) =
  pimp (elim-formula P pf pt pa pn pand por pimp piff x)
       (elim-formula P pf pt pa pn pand por pimp piff y)
elim-formula P pf pt pa pn pand por pimp piff (Iff x y) =
  piff (elim-formula P pf pt pa pn pand por pimp piff x)
       (elim-formula P pf pt pa pn pand por pimp piff y)

on-atoms : (A → Formula B) → Formula A → Formula B
on-atoms {B} f =
 elim-formula (λ _ → Formula B)
   False True f
   Not And Or Imp Iff

over-atoms : (A → B → B) → Formula A → B → B
over-atoms {B} f =
 elim-formula (λ _ → B → B)
   id id f
   id
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)
   (λ px py → px ∘ py)

atom-list : (A → List B) → Formula A → List B
atom-list f fm = over-atoms (λ h → f h ++_) fm []

atoms-list : Formula A → List A
atoms-list = atom-list (_∷ [])

atom-union : ⦃ d : is-discrete B ⦄
           → (A → List B) → Formula A → List B
atom-union f fm = nub _=?_ $ atom-list f fm

atoms : ⦃ d : is-discrete A ⦄
      → Formula A → List A
atoms = atom-union (_∷ [])

-- TODO move to Sem ?

atomsₛ : Formula A → LFSet A
atomsₛ {A} =
  elim-formula (λ _ → LFSet A)
    [] [] sng
    id _∪∷_ _∪∷_ _∪∷_ _∪∷_

atoms-⊆ : ⦃ d : is-discrete A ⦄
        → {f : Formula A}
        → atoms-list f ⊆ atomsₛ f
atoms-⊆ {A} {f} =
  elim-formula (λ q → (zs : List A) → over-atoms _∷_ q zs ⊆ (LFSet.from-list zs ∪∷ atomsₛ q))
     (λ zs {x = q} →
        subst (q ∈_) (∪∷-id-r (LFSet.from-list zs) ⁻¹) ∘ ∈-list)
     (λ zs {x = q} →
        subst (q ∈_) (∪∷-id-r (LFSet.from-list zs) ⁻¹) ∘ ∈-list)
     (λ a zs {x = q} →
          subst (q ∈_) (  ∪∷-id-r (a ∷ LFSet.from-list zs) ⁻¹
                        ∙ ∪∷-swap {s = LFSet.from-list zs})
        ∘ ∈-list)
     id
     (λ {x} {y} hx hy zs {x = q} →
        subst (q ∈_)
              (  ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs) ⁻¹
               ∙ ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ y})) ∘
        ⊆-∪∷-r (hy zs ∘ list-∈) ∘
        hx (over-atoms _∷_ y zs) {x = q})
     (λ {x} {y} hx hy zs {x = q} →
        subst (q ∈_)
              (  ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs) ⁻¹
               ∙ ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ y})) ∘
        ⊆-∪∷-r (hy zs ∘ list-∈) ∘
        hx (over-atoms _∷_ y zs) {x = q})
     (λ {x} {y} hx hy zs {x = q} →
        subst (q ∈_)
              (  ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs) ⁻¹
               ∙ ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ y})) ∘
        ⊆-∪∷-r (hy zs ∘ list-∈) ∘
        hx (over-atoms _∷_ y zs) {x = q})
     (λ {x} {y} hx hy zs {x = q} →
        subst (q ∈_)
              (  ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs) ⁻¹
               ∙ ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ y})) ∘
        ⊆-∪∷-r (hy zs ∘ list-∈) ∘
        hx (over-atoms _∷_ y zs) {x = q})
     f
     []

atoms-⊇ : ⦃ d : is-discrete A ⦄
        → {f : Formula A}
        → atomsₛ f ⊆ atoms-list f
atoms-⊇ {A} {f} =
  elim-formula (λ q → (zs : List A) → (LFSet.from-list zs ∪∷ atomsₛ q) ⊆ over-atoms _∷_ q zs)
     (λ zs {x = q} →
        list-∈ ∘ subst (q ∈_) (∪∷-id-r (LFSet.from-list zs)))
     (λ zs {x = q} →
        list-∈ ∘ subst (q ∈_) (∪∷-id-r (LFSet.from-list zs)))
     (λ a zs {x = q} →
        list-∈ ∘ subst (q ∈_) (  ∪∷-swap {s = LFSet.from-list zs} ⁻¹
                               ∙ ∪∷-id-r (a ∷ LFSet.from-list zs)))
     id
     (λ {x} {y} hx hy zs {x = q} →
        hx (over-atoms _∷_ y zs) {x = q} ∘
        ⊆-∪∷-r (∈-list ∘ hy zs) ∘
        subst (q ∈_)
              (  ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ x})
               ∙ ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs)))
     (λ {x} {y} hx hy zs {x = q} →
        hx (over-atoms _∷_ y zs) {x = q} ∘
        ⊆-∪∷-r (∈-list ∘ hy zs) ∘
        subst (q ∈_)
              (  ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ x})
               ∙ ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs)))
     (λ {x} {y} hx hy zs {x = q} →
        hx (over-atoms _∷_ y zs) {x = q} ∘
        ⊆-∪∷-r (∈-list ∘ hy zs) ∘
        subst (q ∈_)
              (  ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ x})
               ∙ ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs)))
     (λ {x} {y} hx hy zs {x = q} →
        hx (over-atoms _∷_ y zs) {x = q} ∘
        ⊆-∪∷-r (∈-list ∘ hy zs) ∘
        subst (q ∈_)
              (  ap (LFSet.from-list zs ∪∷_) (∪∷-comm {x = atomsₛ x})
               ∙ ∪∷-assoc {y = atomsₛ y} (LFSet.from-list zs)))
     f
     []

-- String vars

Var : 𝒰
Var = String

Form : 𝒰
Form = Formula Var

-- TODO LFSet

-- parser

-- TODO we probably don't need this
record PForm (P : Parameters 0ℓ) (n : ℕ) : 𝒰 (Effect.adj (Parameters.M P) 0ℓ) where
  field patom : Parser P (Form 0↑ℓ) n
        pcst  : Parser P (Form 0↑ℓ) n
        pfact : Parser P (Form 0↑ℓ) n
        plit  : Parser P (Form 0↑ℓ) n
        pcnj  : Parser P (Form 0↑ℓ) n
        pdsj  : Parser P (Form 0↑ℓ) n
        pimp  : Parser P (Form 0↑ℓ) n
        pfrm  : Parser P (Form 0↑ℓ) n

open PForm

-- TODO move

ch : Parameters 0ℓ
ch = chars {ℓb = 0ℓ} {E = ⊤ℓ} {A = ⊥ℓ} ⦃ bd = Bind-Id ⦄

parseℕ : String → Maybe ℕ
parseℕ = parseM {P = ch} ⦃ ch = choice-agdarsecT ⦄ decimalℕ
  where
   instance _ = Bind-Id


pForm : ∀[ PForm ch ]
pForm = INS.fix (PForm ch) $
        λ rec →
        let factor = parens (INS.map pfrm rec) <|>C cst <|>C atom
            lit    = iterater negop factor
            conj   = chainr1 lit  $ box cnjop
            disj   = chainr1 conj $ box dsjop
            impl   = chainr1 disj $ box impop
            form   = chainr1 impl $ box iffop
        in record { patom = atom
                  ; pcst  = cst
                  ; pfact = factor
                  ; plit  = lit
                  ; pcnj  = conj
                  ; pdsj  = disj
                  ; pimp  = impl
                  ; pfrm  = form
                  }

 module Details where
   instance _ = Bind-Id

   atom : ∀[ Parser ch (Form 0↑ℓ) ]
   atom {x} = (λ where (s , mb) →
                         Atom $ list→string $ List⁺.to-list $
                         s ⁺++ Maybe.rec [] List⁺.to-list mb)
              <$>C (alphas⁺ <&?> box (list⁺ (num <|>C char '\'' <|>C char '_')))

   cst : ∀[ Parser ch (Form 0↑ℓ) ]
   cst {x} = False <$C (text "false" {pr = refl}) <|>C True <$C (text "true" {pr = refl})

   negop : ∀[ Parser ch ((Form 0↑ℓ) →ℓ (Form 0↑ℓ)) ]
   negop {x} = withSpaces (Not <$C char '~')

   cnjop : ∀[ Parser ch ((Form 0↑ℓ) →ℓ ((Form 0↑ℓ) →ℓ (Form 0↑ℓ))) ]
   cnjop {x} = withSpaces (And <$C text "/\\" {pr = refl})

   dsjop : ∀[ Parser ch ((Form 0↑ℓ) →ℓ ((Form 0↑ℓ) →ℓ (Form 0↑ℓ))) ]
   dsjop {x} = withSpaces (Or <$C text "\\/" {pr = refl})

   impop : ∀[ Parser ch ((Form 0↑ℓ) →ℓ ((Form 0↑ℓ) →ℓ (Form 0↑ℓ)))]
   impop {x} = withSpaces (Imp <$C text "=>" {pr = refl})

   iffop : ∀[ Parser ch ((Form 0↑ℓ) →ℓ ((Form 0↑ℓ) →ℓ (Form 0↑ℓ)))]
   iffop {x} = withSpaces (Iff <$C text "<=>" {pr = refl})

FormP : ∀[ Parser ch (Form 0↑ℓ) ]
FormP {x} = pForm .pfrm

parseForm : String → Maybe Form
parseForm = parseM {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄ FormP

_∈F : String → 𝒰
str ∈F = _∈P_ {P = ch} ⦃ ch = choice-agdarsecT ⦃ bd = Bind-Id ⦄ ⦄
              str
              FormP

-- printer

brk : Bool → Doc → Doc
brk b d = if b then parensD d else d

prettyForm : ℕ → Form → Doc
prettyForm p False     = textD "false"
prettyForm p True      = textD "true"
prettyForm p (Atom v)  = textD v
prettyForm p (Not x)   = brk (10 <? p) $ charD '¬' ◆ prettyForm 11 x
prettyForm p (And x y) = brk (8 <? p) $ sep $ (prettyForm 9 x ◈ charD '∧') ∷ prettyForm 8 y ∷ []
prettyForm p (Or x y)  = brk (6 <? p) $ sep $ (prettyForm 7 x ◈ charD '∨') ∷ prettyForm 6 y ∷ []
prettyForm p (Imp x y) = brk (4 <? p) $ sep $ (prettyForm 5 x ◈ charD '⇒') ∷ prettyForm 4 y ∷ []
prettyForm p (Iff x y) = brk (2 <? p) $ sep $ (prettyForm 3 x ◈ charD '⇔') ∷ prettyForm 2 y ∷ []

prettyF : Form → String
prettyF = render ∘ prettyForm 0

ppF : (Form → Form) → String → String
ppF f s = Maybe.rec "parse error" (prettyF ∘ f) (parseForm s)

{-
-- tests

f1 : Form
f1 = Imp (Or (Atom "p") (Atom "q")) (Atom "r")

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
