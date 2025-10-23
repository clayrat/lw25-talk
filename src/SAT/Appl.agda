{-# OPTIONS --no-exact-split #-}
module SAT.Appl where

open import Foundations.Prelude
open Variadics _
open import Meta.Show
open import Meta.Effect hiding (_>>_ ; _>>=_)
open import Logic.Decidability
open import Logic.Discreteness

open import Data.Empty
open import Data.Bool
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Nat.Two
open import Data.Nat.Two.Properties
open import Data.List as List
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Operations
open import Data.String
open import Data.Sum

open import Order.Diagram.Meet
open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open decminmax ℕ-dec-total
open import Order.Diagram.Meet.Reasoning ℕₚ min-meets

open import System.Everything hiding (_<$>_)

open import Induction.Nat.Strong as Box using (□_ ; fixΠ ; call)
open import Data.List.NonEmpty as List⁺
open import SAT.Formula0
open import SAT.Sem
open import SAT.NF0

private variable
  A B : 𝒰

{-
-- Ramsey

all-sets : (n : ℕ)  → List A → List (Vec A n)
all-sets    zero      _      = [] ∷ []
all-sets   (suc _)    []     = []
all-sets n@(suc n-1) (h ∷ t) = map (h ∷_) (all-sets n-1 t) List.++ all-sets n t

ramsey : ℕ → ℕ → ℕ → Form
ramsey s t n =
  let vertices = count-from-to 1 (suc n)
      yesgrps = map (all-sets 2 ∘ fst ∘ vec→list) (all-sets s vertices)
      nogrps = map (all-sets 2 ∘ fst ∘ vec→list) (all-sets t vertices)
    in
  Or (list-disj (map (list-conj ∘ map (Atom ∘ mk-atom)) yesgrps))
     (list-disj (map (list-conj ∘ map (Not ∘ Atom ∘ mk-atom)) nogrps))
  where
  mk-atom : Vec ℕ 2 → String
  mk-atom (m ∷ n ∷ []) = "p_" ++ₛ show-ℕ m ++ₛ "_" ++ₛ show-ℕ n
-}
-- Circuits

-- addition

halfsum : Formula A → Formula A → Formula A
halfsum x y = Iff x (Not y)

halfcarry : Formula A → Formula A → Formula A
halfcarry = And

halfadder : Formula A → Formula A → Formula A → Formula A → Formula A
halfadder x y s c = And (Iff s (halfsum x y)) (Iff c (halfcarry x y))

carry : Formula A → Formula A → Formula A → Formula A
carry x y z = Or (And x y) (And (Or x y) z)

sum : Formula A → Formula A → Formula A → Formula A
sum x y z = halfsum (halfsum x y) z

fulladder : Formula A → Formula A → Formula A → Formula A → Formula A → Formula A
fulladder x y z s c = And (Iff s (sum x y z)) (Iff c (carry x y z))

conjoin : (B → Formula A) → List B → Formula A
conjoin f = list-conj ∘ map f

Fgen : 𝒰 → 𝒰
Fgen A = ℕ → Formula A

ripple-carry : Fgen A → Fgen A → Fgen A → Fgen A → Fgen A
ripple-carry x y c out n =
  conjoin (λ i → fulladder (x i) (y i) (c i) (out i) (c (suc i))) $
  count-from-to 0 n

mk-ix : String → ℕ → Form
mk-ix x i = Atom $ x ++ₛ "_" ++ₛ show-ℕ i

mk-ix2 : String → ℕ → ℕ → Form
mk-ix2 x i j = Atom $ x ++ₛ "_" ++ₛ show-ℕ i ++ₛ "_" ++ₛ show-ℕ j

rc : ℕ → Form
rc = ripple-carry (mk-ix "X") (mk-ix "Y") (mk-ix "C") (mk-ix "OUT")

ripple-carry0 : Fgen A → Fgen A → Fgen A → Fgen A → Fgen A
ripple-carry0 x y c out n =
  psimplify $
  ripple-carry x y (λ i → if is-zero? i then False else c i) out n

rc0 : ℕ → Form
rc0 = ripple-carry0 (mk-ix "X") (mk-ix "Y") (mk-ix "C") (mk-ix "OUT")

ripple-carry1 : Fgen A → Fgen A → Fgen A → Fgen A → Fgen A
ripple-carry1 x y c out n =
  psimplify $
  ripple-carry x y (λ i → if is-zero? i then True else c i) out n

mux : Formula A → Formula A → Formula A → Formula A
mux sel in0 in1 = Or (And (Not sel) in0) (And sel in1)

offset : ℕ → Fgen A → Fgen A
offset n x i = x (n + i)

carry-select-ty : 𝒰 → 𝒰
carry-select-ty A = Fgen A → Fgen A → Fgen A → Fgen A
                  → Fgen A → Fgen A → Fgen A → Fgen A
                  → Formula A

carry-select-decr : ∀ {n k} → ¬ (min n k < k) ⊎ (k ＝ 0) → n ∸ k < n
carry-select-decr {n} {k} k′≮k×n≠0 =
  let 0<k = ≱→< (k′≮k×n≠0 ∘ inr ∘ ≤0→=0)
      0<n = <-≤-trans 0<k $ ≤-trans (≯→≤ (k′≮k×n≠0 ∘ inl)) ∩≤l
    in
  <-∸-l-≃ {m = n} {n = k} 0<n ⁻¹ $ <-+-0lr 0<k

-- NB: k is first (it's fixed), n is second
carry-select : ℕ → ℕ → carry-select-ty A
carry-select {A} k =
  fixΠ (λ _ → carry-select-ty A)
    λ n ih
      x y c0 c1
      s0 s1 c s →
      let k′ = min n k
          fm = And (And (ripple-carry0 x y c0 s0 k′)
                        (ripple-carry1 x y c1 s1 k′))
                   (And (Iff (c k′) (mux (c 0) (c0 k′) (c1 k′)))
                        (conjoin (λ i → Iff (s i) (mux (c 0) (s0 i) (s1 i)))
                                 (count-from-to 0 k′)))
        in
       -- stop if k′ < k or k == 0, otherwise it hangs
       --                ^^^^^^^^^
       Dec.rec (λ _ → fm)
               (λ k′≮k×n≠0 →
                   And fm $
                   ih .call {m = n ∸ k} (carry-select-decr k′≮k×n≠0)
                            (offset k x)  (offset k y)  (offset k c0) (offset k c1)
                            (offset k s0) (offset k s1) (offset k c)  (offset k s))
               (Dec-⊎ ⦃ da = <-dec {x = k′} {x = k} ⦄ ⦃ db = k ≟ 0 ⦄)

mk-adder-test : ℕ → ℕ → Form
mk-adder-test n k =
  let x  = mk-ix "X"
      y  = mk-ix "Y"
      c  = mk-ix "C"
      s  = mk-ix "S"
      c0 = mk-ix "C0"
      s0 = mk-ix "S0"
      c1 = mk-ix "C1"
      s1 = mk-ix "S1"
      c2 = mk-ix "C2"
      s2 = mk-ix "S2"
   in
  Imp (And (And (carry-select k n x y c0 c1 s0 s1 c s)
                (Not (c 0)))
           (ripple-carry0 x y c2 s2 n))
      (And (Iff (c n) (c2 n))
           (conjoin (λ i → Iff (s i) (s2 i))
                    (count-from-to 0 n)))

-- multiplication

ripple-shift : Fgen A → Fgen A → Fgen A → Formula A → Fgen A → Fgen A
ripple-shift u v c z w n =
  ripple-carry0 u v
                (λ i → if i == n then w (pred n) else c (suc i))
                (λ i → if is-zero? i then z else w (pred i))
                n

multiplier : (ℕ → Fgen A) → (ℕ → Fgen A) → (ℕ → Fgen A) → Fgen A → Fgen A
multiplier x u v out n =
  if n == 1
    then And (Iff (out 0) (x 0 0)) (Not (out 1))
    else psimplify
           (And (Iff (out 0) (x 0 0))
                (And (ripple-shift (λ i → if i == pred n then False else x 0 (suc i))
                                   (x 1) (v 2) (out 1) (u 2) n)
                     (if n == 2 then And (Iff (out 2) (u 2 0))
                                         (Iff (out 3) (u 2 1))
                                else conjoin (λ k → ripple-shift (u k) (x k) (v (suc k)) (out k)
                                                                 (if k == pred n
                                                                    then offset n out
                                                                    else u (suc k))
                                                                 n)
                                             (count-from-to 2 n))))

-- primality and factorizaton

bitlength-decr : ∀ {n} → n ≠ 0 → (n ÷2) < n
bitlength-decr {n} n≠0 =
  <-÷×2 n n ⁻¹ $
  subst (_< (n ×2)) (·-id-r n) $
  <≃<·l ⁻¹ $ (<≃≱ ⁻¹ $ contra ≤0→=0 n≠0) , s<s z<s

bitlength : ℕ → ℕ
bitlength =
  fixΠ (λ _ → ℕ) λ n ih →
    Dec.rec (λ _ → 0)
            (λ n≠0 → suc $ ih .call {m = n ÷2} (bitlength-decr n≠0))
            (n ≟ 0)

bit-n : ℕ → ℕ → Bool
bit-n  zero   x = odd x
bit-n (suc n) x = bit-n n (x ÷2)

congruent-to : Fgen A → ℕ → ℕ → Formula A
congruent-to x m n =
  conjoin (λ i → if bit-n i m then x i else Not (x i))
          (count-from-to 0 n)

prime : ℕ → Form
prime p =
  let x   = mk-ix  "X"
      y   = mk-ix  "Y"
      out = mk-ix  "OUT"
      u   = mk-ix2 "U"
      v   = mk-ix2 "V"
      m : ℕ → ℕ → Form
      m i j = And (x i) (y j)
      n = bitlength p
    in
  Not (And (multiplier m u v out (pred n))
           (congruent-to out p (max n (2 · n ∸ 2))))

{-
main : Main
main = run $ do
--                put-str-ln $ prettyF $ ramsey 3 3 4
--                put-str-ln $ "tautology(ramsey 3 3 5): "
--                         ++ₛ (show $ tautology $ ramsey 3 3 5)
--                put-str-ln $ "tautology(ramsey 3 3 6): "
--                         ++ₛ (show $ tautology $ ramsey 3 3 6)
                put-str-ln $ prettyF $ rc 2
                put-str-ln $ prettyF $ rc0 2
                put-str-ln $ prettyF $ mk-adder-test 0 1
                put-str-ln $ "tautology(mk-adder-test 1 1): "
                         ++ₛ (show $ tautology $ mk-adder-test 1 1)
                put-str-ln $ "tautology(mk-adder-test 1 2): "
                         ++ₛ (show $ tautology $ mk-adder-test 1 2)
--                put-str-ln $ "tautology(mk-adder-test 2 1): "
--                         ++ₛ (show $ tautology $ mk-adder-test 2 1)
--                put-str-ln $ "tautology(mk-adder-test 2 2): "
--                         ++ₛ (show $ tautology $ mk-adder-test 2 2)
                put-str-ln $ "tautology(prime 7): "
                         ++ₛ (show $ tautology $ prime 7)
                put-str-ln $ "tautology(prime 9): "
                         ++ₛ (show $ tautology $ prime 9)
                put-str-ln $ "tautology(prime 11): "
                         ++ₛ (show $ tautology $ prime 11)
-}
