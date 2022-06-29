```agda
module HoffmanCalculus where
```

```agda
data Typ : Set where
  Nat  : Typ
  _⇒_  : Typ → Typ → Typ
  _⊸_  : Typ → Typ → Typ
  □_⇒_ : Typ → Typ → Typ
  □_⊸_ : Typ → Typ → Typ

data ArrowSort : Set where
  arrow loli : ArrowSort

data _<∶_ : Typ → Typ → Set where
  s-refl  : (A : Typ)           → A <∶ A
  s-ax₁   : (A : Typ)           → (Nat ⇒ A) <∶ (Nat ⊸ A)
  s-ax₂   : (A : Typ)           → (Nat ⇒ A) <∶ (Nat ⊸ A)
  s-trans : (A B C : Typ)       → A <∶ B → B <∶ C → A <∶ C
  -- s-arr   : (A₁ A₂ B₁ B₂ : Typ) → B₁ <∶ A₁ → A₂ <∶ B₂ →
```
