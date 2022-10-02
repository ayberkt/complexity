```agda
module Peter where

open import Data.Nat

Baire = ℕ → ℕ

𝔽 : Baire → (Baire → ℕ → ℕ → ℕ) → ℕ → Baire
𝔽 g h zero    m = g m
𝔽 g h (suc n) m = h (λ y → 𝔽 g h n y) n m

```
