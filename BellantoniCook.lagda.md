```agda
module BellantoniCook where

open import Data.Nat
open import Data.Fin
open import Data.Bool
```

```agda
data BC : ℕ → ℕ → Set where
  zero : BC 0 0
  projₛ : {m n : ℕ} → Fin m → BC m n
  projₙ : {m n : ℕ} → Fin n → BC m n
  succ  : Bool              → BC 0 1
  predd :                     BC 0 1
  cond  :                     BC 0 4
```
