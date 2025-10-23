{-# OPTIONS --safe #-}

module Induction.Nat.Lex where

open import Meta.Prelude
open Variadics _

open import Data.Empty
open import Data.Sum
open import Data.Nat.Base
open import Data.Nat.Order.Base
open import Data.Nat.Properties
open import Order.Constructions.Lex

open import Induction.Nat.Strong

_<×_ : ℕ × ℕ → ℕ × ℕ → 𝒰
_<×_ = ×-lex _<_ _<_

_≤×_ : ℕ × ℕ → ℕ × ℕ → 𝒰
_≤×_ = ×-lex _<_ _≤_

<-≤-×trans : {a b c x y z : ℕ} → (a , x) <× (b , y) → (b , y) ≤× (c , z) → (a , x) <× (c , z)
<-≤-×trans (inl a<b)         (inl b<c)         = inl (<-trans a<b b<c)
<-≤-×trans (inl a<b)         (inr (b=c , y≤z)) = inl (<-≤-trans a<b (=→≤ b=c))
<-≤-×trans (inr (a=b , x<y)) (inl b<c)         = inl (≤-<-trans (=→≤ a=b) b<c)
<-≤-×trans (inr (a=b , x<y)) (inr (b=c , y≤z)) = inr ((a=b ∙ b=c) , (<-≤-trans x<y y≤z))

<-×trans : {a b c x y z : ℕ} → (a , x) <× (b , y) → (b , y) <× (c , z) → (a , x) <× (c , z)
<-×trans {a} {b} {c} {x} {y} {z} = ×-lex-trans <-trans <-trans {pqx = a , x} {pqz = c , z}

<-×ascend : {a x y : ℕ} → (a , x) <× (suc a , y)
<-×ascend = inl <-ascend

infix 9 □×_
record □×_ {ℓ} (A : ℕ × ℕ → 𝒰 ℓ) (mn : ℕ × ℕ) : 𝒰 ℓ where
  constructor mk-lbox
  field call : ∀ {i j} → (ij<mn : (i , j) <× mn) → A (i , j)
open □×_ public

module _ {ℓ} {A : ℕ × ℕ → 𝒰 ℓ} where

 ≤×↓ : {k l m n : ℕ} → (kl≤mn : (k , l) ≤× (m , n)) → (□× A) (m , n) → (□× A) (k , l)
 ≤×↓ kl≤mn a .call ij<kl = a .call (<-≤-×trans ij<kl kl≤mn)

 <×↓ : {k l m n : ℕ} → (kl≤mn : (k , l) <× (m , n)) → (□× A) (m , n) → (□× A) (k , l)
 <×↓ kl<mn a .call ij<kl = a .call (<-×trans ij<kl kl<mn)

module _ {ℓ} {A B : ℕ × ℕ → 𝒰 ℓ} where

 map× : ∀[ A ⇒ B ] → ∀[ □× A ⇒ □× B ]
 map× f a .call ij<mn = f (a .call ij<mn)

module _ {ℓ} {A : ℕ × ℕ → 𝒰 ℓ} where

 pure× : ∀[ A ] → ∀[ □× A ]
 pure× a .call _ = a

 extract× : ∀[ □× A ] → ∀[ A ]
 extract× a {x = x , y} = a .call (<-×ascend {y = y})

 extractΠ× : Π[ □× A ] → Π[ A ]
 extractΠ× a (x , y) = a (suc x , y) .call <-×ascend

 duplicate× : ∀[ □× A ⇒ □× □× A ]
 duplicate× a .call kl<mn .call ij<kl = a .call (<-×trans ij<kl kl<mn)

fix× : ∀ {ℓ} (A : ℕ × ℕ → 𝒰 ℓ) → ∀[ □× A ⇒ A ] → ∀[ A ]
fix× A f {x} =
  ×-ind <-ind <-ind
    (λ y ih → f (mk-lbox λ {i} {j} → ih (i , j)))
    x

fix×Π : ∀ {ℓ} (A : ℕ × ℕ → 𝒰 ℓ) → Π[ □× A ⇒ A ] → Π[ A ]
fix×Π A f =
  ×-ind <-ind <-ind
    λ y ih → f y (mk-lbox λ {i} {j} → ih (i , j))


{-
 fix□× : ∀[ □× A ⇒ A ] → ∀[ □× A ]
 fix□× f {x = k , l} .call {i} {j} =
   [ (λ i<k → go₁ k .call i<k j)
   , (λ where (i=k , j<l) → go₂ i l (go₁ i) .call j<l) ]ᵤ
   where
   go₂ : ∀ u w → (□ (λ p → ∀ q → A (p , q))) u → (□ (λ q → A (u , q))) w
   go₂ u w ih₁ =
     fix□ λ {x} ih₂ → f (mk-lbox λ {i = f} {j = g} →
                           [ (λ f<u → ih₁ .call f<u g)
                           , (λ where (f=u , g<x) →
                                        subst (λ q → A (q , g))
                                              (f=u ⁻¹)
                                              (ih₂ .call g<x))
                           ]ᵤ) 
   go₁ : ∀ u → (□ (λ p → ∀ q → A (p , q))) u
   go₁ u =
     fix□ λ {x} ih₁ y → f (mk-lbox λ {i = f} {j = g} →
                             [ (λ f<x → ih₁ .call f<x g)
                             , (λ where (f=x , g<y) →
                                           go₂ f y
                                               (subst (□ (λ p → (q : ℕ) → A (p , q)))
                                                      (f=x ⁻¹)
                                                      ih₁)
                                               .call g<y)
                             ]ᵤ)
 
 fix□Π× : Π[ □× A ⇒ A ] → Π[ □× A ]
 fix□Π× f (k , l) .call {i} {j} =
   [ (λ i<k → go₁ k .call i<k j)
   , (λ where (i=k , j<l) → go₂ i l (go₁ i) .call j<l) ]ᵤ
   where
   go₂ : ∀ u w → (□ (λ p → ∀ q → A (p , q))) u → (□ (λ q → A (u , q))) w
   go₂ u w ih₁ =
     fix□Π
       (λ x ih₂ → f (u , x) (mk-lbox λ {i = f} {j = g} →
                               [ (λ f<u → ih₁ .call f<u g)
                               , (λ where (f=u , g<x) →
                                            subst (λ q → A (q , g))
                                                  (f=u ⁻¹)
                                                  (ih₂ .call g<x))
                               ]ᵤ))
       w
   go₁ : ∀ u → (□ (λ p → ∀ q → A (p , q))) u
   go₁ =
     fix□Π
       (λ x ih₁ y → f (x , y) (mk-lbox λ {i = f} {j = g} →
                                 [ (λ f<x → ih₁ .call f<x g)
                                 , (λ where (f=x , g<y) →
                                               go₂ f y
                                                   (subst (□ (λ p → (q : ℕ) → A (p , q)))
                                                          (f=x ⁻¹)
                                                          ih₁)
                                                   .call g<y)
                                 ]ᵤ))

fix× : ∀ {ℓ} (A : ℕ × ℕ → 𝒰 ℓ) → ∀[ □× A ⇒ A ] → ∀[ A ]
fix× A = extract× ∘ fix□×

fix×Π : ∀ {ℓ} (A : ℕ × ℕ → 𝒰 ℓ) → Π[ □× A ⇒ A ] → Π[ A ]
fix×Π A = extractΠ× ∘ fix□Π×
-}

module _ {ℓ} {A B : ℕ × ℕ → 𝒰 ℓ} where

 map²× : {C : ℕ × ℕ → 𝒰 ℓ} → ∀[ A ⇒ B ⇒ C ] → ∀[ □× A ⇒ □× B ⇒ □× C ]
 map²× f A B .call ij<mn = f (A .call ij<mn) (B .call ij<mn)

 app× : ∀[ □× (A ⇒ B) ⇒ (□× A ⇒ □× B) ]
 app× F A .call ij<mn = F .call ij<mn (A .call ij<mn)

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
