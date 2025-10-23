{-# OPTIONS --safe #-}
module ListSet where

open import Foundations.Prelude
open import Meta.Effect
open import Logic.Discreteness
open import Functions.Embedding

open import Data.Empty
open import Data.Bool
open import Data.Reflects
open import Data.Dec
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Operations.Properties
open import Data.List.Operations.Rel
open import Data.List.Operations.Discrete
open import Data.List.Correspondences.Binary.OPE

private variable
  A B : 𝒰

union : ⦃ d : is-discrete A ⦄
       → List A → List A → List A
union xs ys = nub _=?_ $ xs ++ ys

union-empty : ⦃ d : is-discrete A ⦄
            → {xs ys : List A}
            → union xs ys ＝ []
            → (xs ＝ []) × (ys ＝ [])
union-empty {xs} {ys} p =
 let (xl , yl) = +=0-2 (length xs) (length ys)
                       (  ++-length xs ys ⁻¹
                        ∙ ap length (nub-[] {xs = xs ++ ys} p))
   in
 length=0→nil xl , length=0→nil yl

insert-s : ⦃ d : is-discrete A ⦄
         → A → List A → List A
insert-s x xs = nub _=?_ $ x ∷ xs

unions : ⦃ d : is-discrete A ⦄
       → List (List A) → List A
unions = nub _=?_ ∘ concat

unions-∈ : ⦃ d : is-discrete A ⦄
         → {xss : List (List A)} {x : A}
         → x ∈ unions xss
         → Σ[ xs ꞉ List A ] (xs ∈ xss × x ∈ xs)
unions-∈ = ∈-concat ∘ ope→subset nub-ope

image : ⦃ d : is-discrete B ⦄
      → (A → B) → List A → List B
image f = nub _=?_ ∘ map f

image-empty : ⦃ d : is-discrete B ⦄
            → {f : A → B} {xs : List A}
            → image f xs ＝ []
            → xs ＝ []
image-empty {f} {xs = []}     _ = refl
image-empty {f} {xs = x ∷ xs}   = false!

∈-image : ⦃ d : is-discrete B ⦄
        → {f : A → B} {xs : List A} {x : A}
        → x ∈ xs → f x ∈ image f xs
∈-image ⦃ d ⦄ x∈ = ⊆-nub {R = λ _ _ → d .proof} (∈-map _ x∈)

image-∈ : ⦃ d : is-discrete B ⦄
        → {f : A → B} {xs : List A} {x : A}
        → Injective f
        → f x ∈ image f xs → x ∈ xs
image-∈ finj = map-∈ _ finj ∘ ope→subset nub-ope

image-∈Σ : ⦃ d : is-discrete B ⦄
         → {f : A → B} {y : B} {xs : List A}
         → y ∈ image f xs → Σ[ x ꞉ A ] ((x ∈ xs) × (y ＝ f x))
image-∈Σ {f} = map-∈Σ f ∘ ope→subset nub-ope

subtract : ⦃ d : is-discrete A ⦄
         → List A → List A → List A
subtract xs ys = nub _=?_ $ diff xs ys

subtract-∈ : ⦃ d : is-discrete A ⦄
           → {xs ys : List A} {y : A}
           → y ∈ subtract xs ys → y ∈ xs × y ∉ ys
subtract-∈ {xs} {ys} y∈s =
  let y∈′ = filter-∈ {p = λ x → not (has x ys)} {xs = xs} $
            ope→subset {ys = diff xs ys} nub-ope y∈s in
  snd y∈′ , λ y∈ → so-not (fst y∈′) (true→so! y∈)
