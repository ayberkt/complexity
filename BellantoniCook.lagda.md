```agda
module BellantoniCook where

open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.Vec
```

```agda
data BC : ℕ → ℕ → Set where
  zero : BC 0 0
  projₙ : {m n : ℕ} → Fin m                       → BC m n
  projₛ : {m n : ℕ} → Fin n                       → BC m n
  succ  : Bool                                    → BC 0 1
  predd :                                           BC 0 1
  cond  :                                           BC 0 4
  rec   : {m n : ℕ} → BC m n → BC (suc m) (suc n) → BC (suc m) n
```

```agda
_‼_ : {n : ℕ} → Vec ℕ n → Fin n → ℕ
(x ∷ _)  ‼ zero  = x
(x ∷ xs) ‼ suc n = xs ‼ n
```

```agda
mutual
  ⟦_⟧ : {m n : ℕ} → BC m n → Vec ℕ m → Vec ℕ n → ℕ
  ⟦ zero       ⟧ [] []       = 0
  ⟦ projₙ i    ⟧ xs as       = xs ‼ i
  ⟦ projₛ i    ⟧ xs as       = as ‼ i
  ⟦ succ false ⟧ [] (x ∷ []) = 2 * x
  ⟦ succ true  ⟧ [] (x ∷ []) = suc (2 * x)
  ⟦ predd      ⟧ = {!!}
  ⟦ cond ⟧ = {!!}
  ⟦ rec e e₁ ⟧ = {!!}
```

```agda
```
