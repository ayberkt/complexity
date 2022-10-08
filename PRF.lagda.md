---
title: PRF
author: Ayberk Tosun
---

## Preamble and Some Bureaucratic Things

Originally written as an assignment in Nils Anders Danielsson's Models of
Computation course.

```agda
module PRF where

open import Data.Nat
open import Data.Bool hiding (_≤_; _≤?_; _<?_; _<_)
open import Data.Sum
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Fin using (Fin; zero; suc; inject₁)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Function
open import Relation.Nullary

Type₀ = Set₀
```

## Recursion principle of ℕ

```agda
natrec : ∀ {A : Type₀} → A → (ℕ → A → A) → ℕ → A
natrec z s zero     = z
natrec z s (suc n)  = s n (natrec z s n)
```

```agda
data Vec (A : Type₀) : ℕ → Type₀ where
  nil : Vec A 0
  _,_ : ∀ {n} → Vec A n → A → Vec A (suc n)

_⟨$⟩_ : {A B : Type₀} {n : ℕ} → (A → B) → Vec A n → Vec B n
f ⟨$⟩ nil      = nil
f ⟨$⟩ (xs , x) = f ⟨$⟩ xs , f x

tail : {n : ℕ} → (Fin (suc n) → ℕ) → Fin n → ℕ
tail f = f ∘ suc

fin-map-to-vec : {n : ℕ} → (Fin n → ℕ) → Vec ℕ n
fin-map-to-vec {zero}  p = nil
fin-map-to-vec {suc n} p = fin-map-to-vec (tail p) , p zero
```

## Definition of the PRF syntax

```agda
data PRF : ℕ → Type₀ where
  zero : PRF 0
  suc  : PRF 1
  proj : {n   : ℕ} → Fin n → PRF n
  comp : {m n : ℕ} → PRF m → Vec (PRF n) m → PRF n
  rec  : {n   : ℕ} → PRF n → PRF (suc (suc n)) → PRF (suc n)
```

```agda
_[_] : {A : Type₀} {n : ℕ} → Vec A n → Fin n → A
_[_] (_  , x) zero    = x
_[_] (xs , x) (suc i) = xs [ i ]
```

```agda
mutual
  ⟦_⟧ : {n : ℕ} → PRF n → Vec ℕ n → ℕ
  ⟦ zero       ⟧ nil        = 0
  ⟦ suc        ⟧ (nil , n)  = 1 + n
  ⟦ proj i     ⟧ ρ          = ρ [ i ]
  ⟦ comp f gs  ⟧ ρ          = ⟦ f ⟧ (⟦ gs ⟧⋆ ρ)
  ⟦ rec  f g   ⟧ (ρ , n)    = natrec (⟦ f ⟧ ρ) (λ n r → ⟦ g ⟧ ((ρ , r) , n)) n

  ⟦_⟧⋆ : ∀ {m n} → Vec (PRF m) n → Vec ℕ m → Vec ℕ n
  ⟦ nil     ⟧⋆ ρ = nil
  ⟦ fs , f  ⟧⋆ ρ = ⟦ fs ⟧⋆ ρ , ⟦ f ⟧ ρ
```

## Implementation of addition

```agda
prf-add : PRF 2
prf-add = rec (proj zero) (comp suc (nil , proj (suc zero)))
```

```
open ≡-Reasoning hiding (begin_)

PRF-add-correct : ∀ m n → ⟦ prf-add ⟧ ((nil , m) , n) ≡ m + n
PRF-add-correct m zero = sym (+-identityʳ m)
PRF-add-correct m (suc n) =
  ⟦ prf-add ⟧ ((nil , m) , suc n)       ≡⟨ refl                           ⟩
  suc (⟦ prf-add ⟧ ((nil , m) , n))     ≡⟨ cong suc (PRF-add-correct m n) ⟩
  suc (m + n)                           ≡⟨ sym (+-suc m n)                ⟩
  m + suc n ∎
```

```agda
private
  variable
    n : ℕ

isPrimitive : (Vec ℕ n → ℕ) → Type₀
isPrimitive {n = n} f = Σ[ p ∈ PRF n  ] ⟦ p ⟧ ≡ f
```

## Pa

```agda
iter : {A : Set} → ℕ → (A → A) → A → A
iter zero    f x = x
iter (suc n) f x = f (iter n f x)

succ : ℕ → ℕ
succ = suc

pa : ℕ → ℕ → ℕ
pa zero    = λ n → suc n
pa (suc m) = λ n → iter (suc n) (pa m) 1

pa-eq₀ : (n : ℕ) → pa 0 n ≡ 1 + n
pa-eq₀ _ = refl

open ≡-Reasoning

pa-eq₁ : (m : ℕ) → pa (suc m) 0 ≡ pa m 1
pa-eq₁ _ = refl

pa-eq₂ : (m n : ℕ)
       → pa (suc m) (suc n) ≡ pa m (pa (suc m) n)
pa-eq₂ _ _ = refl

pa-addition : (n : ℕ) → pa 1 n ≡ suc (suc n)
pa-addition zero    = refl
pa-addition (suc n) = pa 1 (suc n)       ≡⟨ refl                        ⟩
                      pa 0 (pa 1 n)      ≡⟨ cong (pa 0) (pa-addition n) ⟩
                      pa 0 (suc (suc n)) ≡⟨ refl                        ⟩
                      suc (suc (suc n)) ∎

pa-lemma : (r s y : ℕ) → pa r (pa s y) < pa (r + s + 2) y
pa-lemma r s y = {!r!}
```

```agda
ack : Vec ℕ 2 → ℕ
ack ((nil , m) , n) = pa m n
```

## Majorisation

```agda
_⋎_ : ℕ → ℕ → ℕ
m ⋎ n with m <? n
(m ⋎ n) | false because q = m
(m ⋎ n) | true  because q = n
```

```agda
0-right-unit-for-⋎ : (n : ℕ) → n ⋎ 0 ≡ n
0-right-unit-for-⋎ zero = refl
0-right-unit-for-⋎ (suc n) = refl

⋎-upper-left : (m n : ℕ) → m ≤ (m ⋎ n)
⋎-upper-left m n with m <? n
⋎-upper-left m n | false because p = ≤-reflexive refl
⋎-upper-left m n | yes p           = <⇒≤ p

⋎-upper-right : (m n : ℕ) → n ≤ (m ⋎ n)
⋎-upper-right m n with m <? n
⋎-upper-right m n | no p           = ≮⇒≥ p
⋎-upper-right m n | true because p = ≤-reflexive refl

suc-preserves-⋎-⇒ : (m n : ℕ) → suc m ⋎ suc n ≤ suc (m ⋎ n)
suc-preserves-⋎-⇒ zero    zero    = ≤-reflexive refl
suc-preserves-⋎-⇒ zero    (suc n) = ≤-reflexive refl
suc-preserves-⋎-⇒ (suc m) zero    = ≤-reflexive refl
suc-preserves-⋎-⇒ (suc m) (suc n) with suc (suc m) <? suc (suc n)
suc-preserves-⋎-⇒ (suc m) (suc n) | no  _ = s≤s (⋎-upper-left  (suc m) (suc n))
suc-preserves-⋎-⇒ (suc m) (suc n) | yes _ = s≤s (⋎-upper-right (suc m) (suc n))

suc-preserves-⋎-⇐ : (m n : ℕ) → suc (m ⋎ n) ≤ suc m ⋎ suc n
suc-preserves-⋎-⇐ zero    zero            = ≤-reflexive refl
suc-preserves-⋎-⇐ zero    (suc n)         = ≤-reflexive refl
suc-preserves-⋎-⇐ (suc m) zero            = ≤-reflexive refl
suc-preserves-⋎-⇐ (suc m) (suc n) with suc m <? suc n
suc-preserves-⋎-⇐ (suc m) (suc n) | no  _ = ⋎-upper-left  (suc (suc m)) (suc (suc n))
suc-preserves-⋎-⇐ (suc m) (suc n) | yes p = ⋎-upper-right (suc (suc m)) (suc (suc n))

suc-preserves-⋎ : (m n : ℕ) → suc (m ⋎ n) ≡ suc m ⋎ suc n
suc-preserves-⋎ m n = ≤-antisym (suc-preserves-⋎-⇐ m n) (suc-preserves-⋎-⇒ m n)
```

```agda
max : {n : ℕ} → Vec ℕ n → ℕ
max nil      = 0
max (ns , n) = n ⋎ max ns
```

```agda
max-gives-upper-bound : {n : ℕ} → (ns : Vec ℕ n) → (i : Fin n) → ns [ i ] ≤ max ns
max-gives-upper-bound (ns , n) zero    = ⋎-upper-left n (max ns)
max-gives-upper-bound (ns , n) (suc i) = ≤-trans IH (⋎-upper-right n (max ns))
 where
  IH : (ns [ i ]) ≤ max ns
  IH = max-gives-upper-bound ns i
```

```agda
_≺_ : {n : ℕ} → (Vec ℕ n → ℕ) → (Vec ℕ 2 → ℕ) → Set
_≺_ {n = n} f g = Σ[ m ∈ ℕ ] ((ns : Vec ℕ n) → f ns < g ((nil , m) , max ns))
```

**Lemma**: the Ackermann function majorises every primitive recursive function.

```agda
majorisation-zero : ⟦ zero ⟧ ≺ ack
majorisation-zero = 0 , †
  where
    † : (ns : Vec ℕ 0) → ⟦ zero ⟧ ns < ack ((nil , 0) , max ns)
    † nil = s≤s z≤n

open import Relation.Binary.Reasoning.StrictPartialOrder <-strictPartialOrder
  renaming (_∎ to _■)

majorisation-suc : ⟦ suc ⟧ ≺ ack
majorisation-suc = 1 , †
  where
    † : (ns : Vec ℕ 1) → ⟦ suc ⟧ ns < pa 1 (max ns)
    † (nil , n) =
      begin-strict
        suc n        <⟨ n<1+n (suc n)       ⟩
        suc (suc n)  ≈⟨ sym (pa-addition n) ⟩
        pa 1 n
      ■

majorisation-proj : {n : ℕ} → (i : Fin n) → ⟦ proj i ⟧ ≺ ack
majorisation-proj {n = n} zero    = 0 , †
  where
    † : (ns : Vec ℕ (suc _)) → ⟦ proj zero ⟧ ns < ack ((nil , 0) , max ns)
    † (ns , n) =
      begin-strict
        n                     <⟨ ≤-reflexive refl ⟩
        suc n                 ≤⟨ m≤n⇒m<n∨m≡n (⋎-upper-left (suc n) (suc (max ns))) ⟩
        suc n ⋎ suc (max ns)  ≈⟨ sym (suc-preserves-⋎ n (max ns)) ⟩
        suc (n ⋎ max ns)      ≈⟨ refl ⟩
        pa 0 (n ⋎ max ns)     ■
majorisation-proj (suc i) = 0 , †
  where
    † : (ns : Vec ℕ (suc _)) → ⟦ proj (suc i) ⟧ ns < ack ((nil , 0) , max ns)
    † (ns , n) =
      begin-strict
        ns [ i ]            ≤⟨ m≤n⇒m<n∨m≡n (max-gives-upper-bound ns i) ⟩
        max ns              ≤⟨ m≤n⇒m<n∨m≡n (⋎-upper-right n (max ns))   ⟩
        n ⋎ max ns          <⟨ n<1+n (n ⋎ max ns)                       ⟩
        suc (n ⋎ max ns)    ≈⟨ refl ⟩
        pa 0 (max (ns , n))
      ■

apply⋆ : {A B : Set} {n : ℕ} → Vec (A → B) n → A → Vec B n
apply⋆ nil      x = nil
apply⋆ (fs , f) x = apply⋆ fs x , f x

-- majorisation-comp : {m n : ℕ} (e : PRF n) (es : Vec (PRF m) n)
--                   → ⟦ e ⟧ ≺ ack
--                   → ((i : Fin n) → ⟦ es [ i ] ⟧ ≺ ack)
--                   → ⟦ comp e es ⟧ ≺ ack
-- majorisation-comp {m = m} {n} e es φ ψ = s + max (fin-map-to-vec r) + 2 , †
--   where
--     h : Vec ℕ n → ℕ
--     h = ⟦ e ⟧

--     𝕘 : Fin n → Vec ℕ m → ℕ
--     𝕘 i = ⟦ es [ i ] ⟧

--     r : Fin n → ℕ
--     r i = proj₁ (ψ i)

--     lemma : (i : Fin n) (ns : Vec ℕ m) → 𝕘 i ns < pa (r i) (max ns)
--     lemma i ns =
--       begin-strict
--         𝕘 i ns              <⟨ proj₂ (ψ i) ns ⟩
--         pa (r i) (max ns)
--       ■

--     s : ℕ
--     s = proj₁ φ

--     lemma₀ : (ns : Vec ℕ n) → h ns < pa s (max ns)
--     lemma₀ ns =
--       begin-strict
--         h ns          <⟨ proj₂ φ ns ⟩
--         pa s (max ns)
--       ■

--     ks : Vec ℕ n
--     ks = fin-map-to-vec (proj₁ ∘ ψ)

--     † : (ns : Vec ℕ m)
--       → ⟦ comp e es ⟧ ns < pa (s + max {!!} + 2) (max ns)
--     † ns =
--       begin-strict
--         h (⟦ es ⟧⋆ ns)               <⟨ lemma₀ (⟦ es ⟧⋆ ns) ⟩
--         pa s o                       <⟨ {!!} ⟩
--         pa s (pa o (max ns))         <⟨ pa-lemma s o (max ns) ⟩
--         pa (s + o + 2) (max ns)
--       ■
--         where
--           o = max (⟦ es ⟧⋆ ns)

majorisation-rec : {n : ℕ}
                 → (e₀ : PRF n) (e₁ : PRF (suc (suc n)))
                 → ⟦ e₀ ⟧ ≺ ack
                 → ⟦ e₁ ⟧ ≺ ack
                 → ⟦ rec e₀ e₁ ⟧ ≺ ack
majorisation-rec {n = n} e₀ e₁ (r₀ , μ₀) (r₁ , μ₁) = {!!}
  where
    lemma : Σ[ q ∈ ℕ ] ((ns : Vec ℕ n) (n : ℕ) → ⟦ rec e₀ e₁ ⟧ (ns , n) < pa q (n + max ns))
    lemma = suc (r₀ ⋎ r₁) , †
      where
        † : (ns : Vec ℕ n) (k : ℕ) → ⟦ rec e₀ e₁ ⟧ (ns , k) < pa (suc (r₀ ⋎ r₁)) (k + max ns)
        † ns zero    with r₀ <? r₁
        † ns zero | no ¬p = {!!}
        † ns zero | true because proof₁ = {!!}
        † ns (suc k) = {!!}

-- majorisation-lemma : {n : ℕ} → (e : PRF n) → ⟦ e ⟧ ≺ ack
-- majorisation-lemma zero        = majorisation-zero
-- majorisation-lemma suc         = majorisation-suc
-- majorisation-lemma (proj i)    = majorisation-proj i
-- majorisation-lemma (comp e es) = majorisation-comp e es
-- majorisation-lemma (rec e e₁)  = {!!}
```
