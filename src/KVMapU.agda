{-# OPTIONS --safe #-}
module KVMapU where

open import Prelude

open import Order.Strict
open import Order.Trichotomous
open import Data.Maybe
open import Data.List
open import Data.List.Correspondences.Unary.Unique

open import KVListU

private variable
  ℓᵏ ℓᵛ ℓ ℓ′ : Level

record KVMap
  (K : 𝒰 ℓᵏ)
  (V : 𝒰 ℓᵛ) : 𝒰 (ℓᵏ ⊔ ℓᵛ) where

  constructor kvmap
  field
    kv  : List (K × V)
    inv : Is-kvlist kv

open KVMap public

unquoteDecl KVMap-iso = declare-record-iso KVMap-iso (quote KVMap)

module KVProp
  {K : 𝒰 ℓᵏ}
  {V : 𝒰 ℓᵛ}
  where

  kv-ext : {kv₁ kv₂ : KVMap K V} → kv₁ .kv ＝ kv₂ .kv → kv₁ ＝ kv₂
  kv-ext {kv₂ = kvmap _ inv₂} e = ap² kvmap e (to-pathᴾ (Uniq-is-prop _ inv₂))

module KVOps
  {K : 𝒰 ℓᵏ}
  ⦃ d : is-discrete K ⦄
  {V : 𝒰 ℓᵛ}
  where

  open KVListU.Ops

  keysm : KVMap K V → List K
  keysm m = keys (m .kv)

  valsm : KVMap K V → List V
  valsm m = values (m .kv)

  emptym : KVMap K V
  emptym .kv  = empty-kv
  emptym .inv = Is-kvlist-empty {V = V}

  lookupm : KVMap K V → K → Maybe V
  lookupm m = lookup-kv (m .kv)

  upsertm : (V → V → V) → K → V → KVMap K V → KVMap K V
  upsertm f k v m .kv  = upsert-kv f k v (m .kv)
  upsertm f k v m .inv = Is-kvlist-upsert (m .inv)

  -- always overwrite
  insertm : K → V → KVMap K V → KVMap K V
  insertm = upsertm λ _ → id

{-
  removem : K → KVMap K< V → KVMap K< V
  removem k m .kv  = remove-kv k (m .kv)
  removem k m .inv = Is-kvlist-remove (m .inv)

  unionm : (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
  unionm f l r .kv  = union-kv f (l .kv) (r .kv)
  unionm f l r .inv = Is-kvlist-union (l .inv) (r .inv)

  interm : (V → V → V) → KVMap K< V → KVMap K< V → KVMap K< V
  interm f l r .kv  = inter-kv f (l .kv) (r .kv)
  interm f l r .inv = Is-kvlist-inter (l .inv) (r .inv)
-}

module KVOps2
  {K K′ : 𝒰 ℓᵏ}
  ⦃ d : is-discrete K ⦄
  ⦃ d′ : is-discrete K′ ⦄
  {V V′ : 𝒰 ℓᵛ}
  where

  open KVListU.OpsBi

  bimapm : (f : K → K′) → Injective f
         → (V → V′) → KVMap K V → KVMap K′ V′
  bimapm f fi g m .kv  = bimap-kv f g (m .kv)
  bimapm f fi g m .inv = Is-kvlist-bimap fi (m .inv)
