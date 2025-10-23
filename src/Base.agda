-- open import Level using (Level)

open import Foundations.Prelude
open import Meta.Effect
open import Meta.Effect.Bind.State

module Base (ℓ : Level) where

open import Level.Bounded

open import Data.Bool
open import Data.Nat -- as Nat
open import Data.Nat.Order.Base
open import Data.List
open import Data.Char
open import Data.String
open import Data.Maybe as Maybe
open import Data.Vec.Inductive
open import Data.Vec.Inductive.Operations

open import Data.Sum
{-
open import Data.Nat.Properties
open import Data.Char.Base as Char using (Char)
import Data.Empty as Empty
open import Data.Product as Product using (_,_; proj₁)

open import Data.List.Base as List using ([]; _∷_)
open import Data.List.Categorical as List

open import Data.String as String
open import Data.Vec as Vec using ()
open import Data.Bool
open import Data.Maybe as Maybe using (nothing; just; maybe′)
open import Data.Maybe.Categorical as MaybeCat
open import Data.Sum
open import Function
open import Category.Monad
open import Category.Monad.State
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary using (IUniversal; _⇒_) public
open import Relation.Binary.PropositionalEquality.Decidable public
open import Induction.Nat.Strong hiding (<-lower ; ≤-lower) public


-}
open import Data.Singleton public
open import Data.Subset public
open import Data.List.Sized.Interface
open import Data.Text.Sized

open import Text.Parser.Types.Core          public
open import Text.Parser.Types               public
open import Text.Parser.Position            public
open import Text.Parser.Combinators         public
open import Text.Parser.Combinators.Char    public
open import Text.Parser.Combinators.Numbers public
open import Text.Parser.Monad               public
open import Text.Parser.Monad.Result        public

-- open Agdarsec′ public

record Tokenizer (A : 𝒰≤ ℓ) : 𝒰 (A .lev≤ .level) where
  constructor mk-tokenizer
  field tokenize : List Char → List (A .ty)

  fromText : String → List (A .ty)
  fromText = tokenize ∘ string→list

instance
  tokChar : Tokenizer (Char 0↑ℓ)
  tokChar = mk-tokenizer id

record BindRun (M : Effect) : Typeω where
  private module M = Effect M
  field
    runM : {A : 𝒰 ℓ} → M.₀ A → List A

open BindRun

instance
{-
  Agdarsec′M : RawMonad (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M  = Agdarsec′.monad

  Agdarsec′M0 : RawMonadZero (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M0 = Agdarsec′.monadZero

  Agdarsec′M+ : RawMonadPlus (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M+ = Agdarsec′.monadPlus
-}
  runId : BindRun (eff id)
  runId .runM = _∷ []

  runMaybe : BindRun (eff Maybe)
  runMaybe .runM = Maybe.rec [] (_∷ [])

  runList : BindRun (eff List)
  runList .runM = id

  runResult : {E : 𝒰 ℓ} → BindRun (eff (Result E))
  runResult .runM = result (λ _ → []) (λ _ → []) (_∷ [])

  runResultT : {M : Effect} {E : 𝒰≤ ℓ} (let module M = Effect M)
               ⦃ rn : BindRun M ⦄
             → BindRun (eff (ResultT E M))
  runResultT ⦃ rn ⦄ .runM x =
     concat $ map {M = eff List} (runResult .runM) $ rn .runM (x .run-resultT)

  runStateT : {M : Effect} {A : 𝒰≤ ℓ} (let module M = Effect M)
              ⦃ rn : BindRun M ⦄
            → BindRun (eff (StateT (Liftℓ ((Position 0↑ℓ) ×ℓ Listℓ A)) M))
  runStateT ⦃ rn ⦄ .runM st =
    map snd $
    rn .runM $
    st .run-stateT (liftℓ (start , []))

  runAgdarsecT : {M : Effect} {E A : 𝒰≤ ℓ} (let module M = Effect M)
                 ⦃ rn : BindRun M ⦄
               → BindRun (eff (AgdarsecT E A M))
  runAgdarsecT {M} {E} {A} ⦃ rn ⦄ .runM x =
    runStateT .runM (x .run-agdarsecT)

{-

  monadMaybe : RawMonad {l} Maybe.Maybe
  monadMaybe = MaybeCat.monad

  plusMaybe : RawMonadPlus {l} Maybe.Maybe
  plusMaybe = MaybeCat.monadPlus

  monadList : RawMonad {l} List.List
  monadList = List.monad

  plusList : RawMonadPlus {l} List.List
  plusList = List.monadPlus
-}

module _ {P : Parameters ℓ} (open Parameters P)
         ⦃ t : Tokenizer Tok}}
         ⦃ ch : Choice M ⦄
         ⦃ S : Sized Tok Toks}}
         ⦃ L : ∀ {n} → Subset ((Vecℓ Tok n) .ty) ((Toks n) .ty) ⦄
         ⦃ rn : BindRun M ⦄
        where

  parseM : {A : 𝒰≤ ℓ} → ∀[ Parser P A ] → String → Maybe (A .ty)
  parseM P str =
    let (len , input , eq) =
         the (Σ[ len ꞉ ℕ ] Vec (Tok .ty) len × (length (Tokenizer.fromText t str) ＝ len))
             (list→vec $ Tokenizer.fromText t str)
        parse = P .run-parser ≤-ascend (liftℓ (L .into (input)))
        check = λ s → if Success.ssize s == 0
                          then just (Success.value s) else nothing
     in
    map lowerℓ $
    traverse check (rn .runM parse) >>= headᵐ

  _∈P_ : {A : 𝒰≤ ℓ} → String → ∀[ Parser P A ] → 𝒰 (A .lev≤ .level)
  str ∈P P = fromJust $ parseM P str
