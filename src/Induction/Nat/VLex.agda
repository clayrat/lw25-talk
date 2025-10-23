{-# OPTIONS --safe #-}
module Induction.Nat.VLex where

open import Meta.Prelude
open Variadics _

open import Data.Empty
open import Data.Sum
open import Data.Reflects
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Nat.Properties
open import Data.Vec.Inductive
open import Order.Constructions.Lex
open import Order.Constructions.Lex.Vec

private variable
  ub : ℕ

_<∷×_ : Vec ℕ ub × ℕ → Vec ℕ ub × ℕ → 𝒰
_<∷×_ = ×-lex (Vec-lex< _<_) _<_

_≤∷×_ : Vec ℕ ub × ℕ → Vec ℕ ub × ℕ → 𝒰
_≤∷×_ = ×-lex (Vec-lex< _<_) _≤_

<-≤-∷×trans : {as bs cs : Vec ℕ ub} {x y z : ℕ}
            → (as , x) <∷× (bs , y)
            → (bs , y) ≤∷× (cs , z)
            → (as , x) <∷× (cs , z)
<-≤-∷×trans {ub = zero}   {as = []}     {bs = []}     {cs = []}     abs bcs =
  map-r (λ where (_ , x<y) →
                     refl
                   , <-≤-trans x<y ([ (λ p → absurd (lower p)) , snd ]ᵤ bcs))
        abs
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inl a<b))         (inl (inl b<c))         =
  inl (inl (<-trans a<b b<c))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inl a<b))         (inl (inr (b=c , _)))   =
  inl (inl (<-≤-trans a<b (=→≤ b=c)))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inr (a=b , _)))   (inl (inl b<c))         =
  inl (inl (≤-<-trans (=→≤ a=b) b<c))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inr (a=b , abs))) (inl (inr (b=c , bcs))) =
  inl (inr (a=b ∙ b=c , Vec-lex<-trans <-trans {xs = as} {ys = bs} {zs = cs} abs bcs))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inl a<b))         (inr (bs=cs , y≤z))     =
  inl (inl (<-≤-trans a<b (=→≤ (∷-head-inj bs=cs))))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inl (inr (a=b , abs))) (inr (bs=cs , y≤z))     =
  inl (inr (a=b ∙ ∷-head-inj bs=cs , subst (Vec-lex< _<_ as) (∷-tail-inj bs=cs) abs))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inr (as=bs , x<y))     (inl (inl b<c))         =
  inl (inl (≤-<-trans (=→≤ (∷-head-inj as=bs)) b<c))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inr (as=bs , x<y))     (inl (inr (b=c , bcs))) =
  inl (inr (∷-head-inj as=bs ∙ b=c , subst (λ q → Vec-lex< _<_ q cs) (∷-tail-inj as=bs ⁻¹) bcs))
<-≤-∷×trans {ub = suc ub} {as = a ∷ as} {bs = b ∷ bs} {cs = c ∷ cs} (inr (as=bs , x<y))     (inr (bs=cs , y≤z))     =
  inr (as=bs ∙ bs=cs , <-≤-trans x<y y≤z)

<∷×-trans : {as bs cs : Vec ℕ ub} {x y z : ℕ}
          → (as , x) <∷× (bs , y)
          → (bs , y) <∷× (cs , z)
          → (as , x) <∷× (cs , z)
<∷×-trans =
  ×-lex-trans {_Q<_ = _<_}
    (λ {px} {py} {pz} → Vec-lex<-trans <-trans {xs = px} {ys = py} {zs = pz})
    <-trans

{-
<-∷ascend : {n : ℕ} {xs ys : List ℕ} → (n ∷ xs) <∷ (suc n ∷ ys)
<-∷ascend = inl <-ascend

-}

infix 9 □∷×_
record □∷×_ {ℓ} (A : Vec ℕ ub × ℕ → 𝒰 ℓ) (xsn : Vec ℕ ub × ℕ) : 𝒰 ℓ where
  constructor mk-lpbox
  field call : ∀ {ys} {m} → (ms<ns : (ys , m) <∷× xsn) → A (ys , m)
open □∷×_ public

module _ {ℓ} {A : Vec ℕ ub × ℕ → 𝒰 ℓ} where

 ≤∷×↓ : {xsm ysn : Vec ℕ ub × ℕ} → (xsm≤ysn : xsm ≤∷× ysn) → (□∷× A) ysn → (□∷× A) xsm
 ≤∷×↓ {xsm} xsm≤ysn a .call {ys = zs} {m = k} zsk<xsm = a .call (<-≤-∷×trans {as = zs} {bs = xsm .fst} zsk<xsm xsm≤ysn)

 <∷×↓ : {xsm ysn : Vec ℕ ub × ℕ} → (xsm<ysn : xsm <∷× ysn) → (□∷× A) ysn → (□∷× A) xsm
 <∷×↓ {xsm} xsm<ysn a .call {ys = zs} {m = k} zsk<xsm = a .call (<∷×-trans {as = zs} {bs = xsm .fst} zsk<xsm xsm<ysn)

module _ {ℓ} {A B : Vec ℕ ub × ℕ → 𝒰 ℓ} where

 map∷× : ∀[ A ⇒ B ] → ∀[ □∷× A ⇒ □∷× B ]
 map∷× f a .call ij<mn = f (a .call ij<mn)

module _ {ℓ} {A : Vec ℕ ub × ℕ → 𝒰 ℓ} where

 pure∷× : ∀[ A ] → ∀[ □∷× A ]
 pure∷× a .call _ = a

 -- TODO these now only hold when 0 < ub
 {-
 extract∷× : ∀[ □∷× A ] → ∀[ A ]
 extract∷× a {x = ([] [< prf >]) , n} = a {x = (([]) [< {!!} >]) , 1} .call {!!}
 extract∷× a {x = ((x ∷ xs) [< prf >]) , n} = {!!}


 extractΠ∷× : Π[ □∷× A ] → Π[ A ]
 extractΠ∷× a []       = a (0 ∷ []) .call (lift tt)
 extractΠ∷× a (x ∷ xs) = a (suc x ∷ xs) .call (<-∷ascend {ys = xs})
 -}

 duplicate∷ : ∀[ □∷× A ⇒ □∷× □∷× A ]
 duplicate∷ {x} a .call {ys} {m} ms<ns .call {ys = ks} {m = k} ks<ms = a .call (<∷×-trans {as = ks} {bs = ys} {cs = x .fst} ks<ms ms<ns)

fix∷× : ∀ {ℓ} (A : Vec ℕ ub × ℕ → 𝒰 ℓ)
      → ∀[ □∷× A ⇒ A ] → ∀[ A ]
fix∷× A f {x} =
  ×-ind (Vec-lex<-ind <-ind) <-ind
    (λ y ih → f (mk-lpbox λ {i} {j} → ih (i , j)))
    x

fix∷×Π : ∀ {ℓ} (A : Vec ℕ ub × ℕ → 𝒰 ℓ)
       → Π[ □∷× A ⇒ A ] → Π[ A ]
fix∷×Π A f =
  ×-ind (Vec-lex<-ind <-ind) <-ind
    λ y ih → f y (mk-lpbox λ {i} {j} → ih (i , j))

module _ {ℓ} {A B : Vec ℕ ub × ℕ → 𝒰 ℓ} where

 map²∷× : {C : Vec ℕ ub × ℕ → 𝒰 ℓ} → ∀[ A ⇒ B ⇒ C ] → ∀[ □∷× A ⇒ □∷× B ⇒ □∷× C ]
 map²∷× f A B .call ij<mn = f (A .call ij<mn) (B .call ij<mn)

 app∷× : ∀[ □∷× (A ⇒ B) ⇒ (□∷× A ⇒ □∷× B) ]
 app∷× F A .call ij<mn = F .call ij<mn (A .call ij<mn)

{-

module _ {ℓ} {A : ℕ → 𝒰 ℓ} where

 <-close : (∀ {m n} → (@0 m<n : m < n) → A n → A m) → ∀[ A ⇒ □ A ]
 <-close d a .call m<n = d m<n a

 ≤-close : (∀ {m n} → (@0 m≤n : m ≤ n) → A n → A m) → ∀[ A ⇒ □ A ]
 ≤-close d = <-close λ m<n → d (<-weaken _ _ m<n)

 loeb : ∀[ □ (□ A ⇒ A) ⇒ □ A ]
 loeb = fix (□ (□ A ⇒ A) ⇒ □ A) $
        λ rec f → mk-nbox λ m<n →
                            f .call m<n (rec .call m<n (duplicate f .call m<n))
-}

