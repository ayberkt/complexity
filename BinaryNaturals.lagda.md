```agda
module BinaryNaturals where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Data.Vec

open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
```

Based on the Agda standard library

```agda
data ℕᵇ : Set where
  𝟎   : ℕᵇ        -- zero
  _∙𝕝 : ℕᵇ → ℕᵇ   -- 2 * (1 + n) = nonzero even numbers
  _∙𝕣 : ℕᵇ → ℕᵇ   -- 1 + (2 * n) = odd numbers

infixl 5 _∙𝕝
infixl 5 _∙𝕣
```

```agda
to-unary : ℕᵇ → ℕ
to-unary 𝟎      = 0
to-unary (n ∙𝕝) = 2 * (suc (to-unary n))
to-unary (n ∙𝕣) = suc (2 * to-unary n)
```

```agda
sucᵇ : ℕᵇ → ℕᵇ
sucᵇ 𝟎      = 𝟎 ∙𝕣
sucᵇ (n ∙𝕝) = sucᵇ n ∙𝕣  --   1 + (2 * (1 + n))
                         -- = 2n + 3
                         -- = 1 + 2 * (n + 1)
sucᵇ (n ∙𝕣) = n ∙𝕝       --   1 + (1 + (2 * n))
                         -- = 2 + (2 * n)
                         -- = 2 * (1 + n)
```

```agda
doubling-lemma : (n : ℕ) → n + n ≡ 2 * n
lemma : (n : ℕ) → 2 * suc n ≡ suc (suc (2 * n))

doubling-lemma zero = refl
doubling-lemma (suc n) =
 suc n + suc n      ≡⟨ refl ⟩
 suc (n + suc n)    ≡⟨ cong suc (+-comm n (suc n)) ⟩
 suc (suc (n + n))  ≡⟨ cong (λ - → suc (suc -)) (doubling-lemma n) ⟩
 suc (suc (2 * n))  ≡⟨ sym (lemma n) ⟩
 2 * suc n          ∎

lemma zero    = refl
lemma (suc n) =
 2 * suc (suc n)                 ≡⟨ refl ⟩
 suc (suc n) + (1 * suc (suc n)) ≡⟨ cong (suc (suc n) +_) (*-identityˡ (suc (suc n))) ⟩
 suc (suc n) + (suc (suc n))     ≡⟨ refl ⟩
 2 + (n + suc (suc n))           ≡⟨ cong (2 +_) (+-comm n (suc (suc n))) ⟩
 2 + (suc (suc n) + n)           ≡⟨ refl ⟩
 2 + (suc (suc (n + n)))         ≡⟨ cong (λ - → 2 + suc (suc -)) (doubling-lemma n) ⟩
 2 + (suc (suc (2 * n)))         ≡⟨ cong (2 +_) (sym (lemma n)) ⟩
 suc (suc (2 * suc n))           ∎

sucᵇ-correct : (n : ℕᵇ) → to-unary (sucᵇ n) ≡ suc (to-unary n)
sucᵇ-correct 𝟎      = refl
sucᵇ-correct (n ∙𝕝) = to-unary (sucᵇ (n ∙𝕝))      ≡⟨ refl ⟩
                      to-unary (sucᵇ n ∙𝕣)        ≡⟨ refl ⟩
                      suc (2 * to-unary (sucᵇ n)) ≡⟨ i    ⟩
                      suc (2 * suc (to-unary n))  ≡⟨ refl ⟩
                      suc (to-unary (n ∙𝕝))       ∎
                       where
                        i = cong (λ - → suc (2 * -)) (sucᵇ-correct n)
sucᵇ-correct (n ∙𝕣) = to-unary (sucᵇ (n ∙𝕣))      ≡⟨ refl ⟩
                      to-unary (n ∙𝕝)             ≡⟨ refl ⟩
                      2 * suc (to-unary n)        ≡⟨ lemma (to-unary n) ⟩
                      suc (suc (2 * to-unary n))  ≡⟨ refl ⟩
                      suc (to-unary (n ∙𝕣))       ∎
```

```agda
to-binary : ℕ → ℕᵇ
to-binary zero    = 𝟎
to-binary (suc n) = sucᵇ (to-binary n)
```

```agda
section : (n : ℕ) → to-unary (to-binary n) ≡ n
section zero    = refl
section (suc n) = to-unary (to-binary (suc n))  ≡⟨ refl                       ⟩
                  to-unary (sucᵇ (to-binary n)) ≡⟨ sucᵇ-correct (to-binary n) ⟩
                  suc (to-unary (to-binary n))  ≡⟨ cong suc (section n)       ⟩
                  suc n ∎
```
