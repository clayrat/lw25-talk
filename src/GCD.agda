module GCD where

open import Prelude
open Variadics _

open import Data.Empty
open import Data.Bool
open import Data.Dec

open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Base
open import Data.Sum
open import Data.Dec.Tri

open import Order.Trichotomous
open import Order.Complemented
open import Order.Constructions.Nat

open import Induction.Nat.Strong as Box using (□_)

gcd-ty : ℕ → 𝒰
gcd-ty x = (y : ℕ) → y < x → ℕ

gcd-loop : Π[ □ gcd-ty ⇒ gcd-ty ]
gcd-loop x ih y y<x =
  caseᵈ y ＝ 0 of
    λ where
        (yes y=0) → x
        (no y≠0) →
          Box.call ih
            y<x (x % y)
            (m%n<n x y (≱→< $ contra ≤0→=0 y≠0))
{-
gcd-loop x ih    zero    _   = x
gcd-loop x ih y@(suc y_) y<x =
  Box.call ih {m = y} y<x (x % y) (m%n<n x y z<s)

gcd< : Π[ gcd-ty ]
gcd< = Box.fixΠ gcd-ty gcd-loop

gcd : ℕ → ℕ → ℕ
gcd x y =
  caseᵗ x >=< y of
    λ where
        (LT x<y) → gcd< y x x<y
        (EQ x=y) → x
        (GT y<x) → gcd< x y y<x
  where
  instance
    Tri-nat : is-trichotomous ℕₛ
    Tri-nat = ComplementedPoset.has-tri-order ℕᶜᵖ
-}  

{-
gcd : ℕ → ℕ → ℕ
gcd m n =
  [   (λ m<n → gcd< n m m<n)
  , [ (λ n<m → gcd< m n n<m)
    , (λ m=n → m)
    ]ᵤ
  ]ᵤ (≤-split m n)
-}
