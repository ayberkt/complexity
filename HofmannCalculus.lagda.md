```agda
module HofmannCalculus where

open import Data.Product
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Nat
```

```agda
data ArrowSort : Set where
  «⇒» «⊸» : ArrowSort

Boxed : Set
Boxed = Bool

Aspect : Set
Aspect = ArrowSort × Boxed

_≼_ : Aspect → Aspect → Set
(«⇒» ,  true) ≼ («⊸» , false) = ⊤
(«⇒» , false) ≼ («⇒» , false) = ⊤
(«⇒» ,  true) ≼ («⇒» ,  true) = ⊤
(«⊸» , false) ≼ («⊸» , false) = ⊤
(«⊸» ,  true) ≼ («⊸» ,  true) = ⊤
(_   ,     _) ≼ (_   ,     _) = ⊥

data Typ : Set where
  Nat   : Typ
  Arrow : Aspect → Typ → Typ → Typ

infix  4 _⊢_
infix  4 _∋_
infixl 5 _⌢_

data Context : Set where
  ∅   : Context
  _⌢_ : Context → Typ → Context

data _∋_ : Context → Typ → Set where
  Z  : ∀ {Γ A} → Γ ⌢ A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ ⌢ B ∋ A

⇒-syntax : Typ → Typ → Typ
⇒-syntax A B = Arrow («⇒» , false) A B

syntax ⇒-syntax A B = A ⇒ B

□⇒-syntax : Typ → Typ → Typ
□⇒-syntax A B = Arrow («⇒» , true) A B

syntax □⇒-syntax A B = A =□⇒ B

syntax ⊸-syntax A B = A ⊸ B

⊸-syntax : Typ → Typ → Typ
⊸-syntax A B = Arrow («⊸» , false) A B
```

```agda
data _<∶_ : Typ → Typ → Set where
  s-refl  : (A : Typ) → A <∶ A
  s-trans : (A B C : Typ) → A <∶ B → B <∶ C → A <∶ C
  s-ax₁   : (A : Typ) → (Nat ⇒ A) <∶ (Nat ⊸ A)
  s-ax₂   : (A : Typ) → (Nat ⇒ A) <∶ (Nat ⊸ A)
  s-arr   : (A₁ A₂ B₁ B₂ : Typ) (a a′ : Aspect)
          → B₁ <∶ A₁ → A₂ <∶ B₂ → a ≼ a′ → Arrow a A₁ A₂ <∶ Arrow a′ B₁ B₂
```

```agda
private
  variable
    Γ   : Context
    A B : Typ

data _⊢_ : Context → Typ → Set where
  var : Γ ∋ A → Γ ⊢ A
```