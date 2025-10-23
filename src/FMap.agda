-- {-# OPTIONS --safe #-}
module FMap where

open import Foundations.Prelude
open import Meta.Effect
open import Logic.Discreteness

open import Data.Bool
open import Data.List as List
open import Data.Maybe as Maybe

private variable
  A B : 𝒰

-- TODO use a listmap from unification?
FMap : 𝒰 → 𝒰 → 𝒰
FMap A B = (A → Maybe B) × List A

emp : FMap A B
emp = (λ _ → nothing) , []

upd : ⦃ d : is-discrete A ⦄
    → A → B → FMap A B → FMap A B
upd k v (mf , md) = (λ x → if x =? k then just v else mf x) , k ∷ md

lup : FMap A B → A → Maybe B
lup (mf , _) = mf

dom : FMap A B → List A
dom (_ , md) = md

codom : FMap A B → List B
codom (mf , md) = md >>= (Maybe.rec [] (_∷ []) ∘ mf)

graph : FMap A B → List (A × B)
graph (mf , md) = map-maybe (λ k → map (k ,_) (mf k)) md

defined : ⦃ d : is-discrete A ⦄
        → FMap A B → A → Bool
defined (_ , md) k = List.has k md

