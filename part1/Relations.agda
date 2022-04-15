module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)


-- Defining relations

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)


-- Implicit arguments

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))


+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _


-- Precedence

infix 4 _≤_


-- Inversion

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl


-- Exercise `orderings`

-- example of preorder and not partial order:
-- `b : Bin`
-- `⟨⟩ ≤ ⟨⟩ O` and `⟨⟩ O ≤ ⟨⟩` but `⟨⟩ ≢ ⟨⟩ O`

-- example of partial order but total order:
-- `Maybe ℕ`
-- `Nothing` and `Just 0` does not hold `Nothing ≤ Just 0` nor `Just 0 ≤ Nothing`
-- (assuming `_≤_` is defined only for `Just _`)


-- Reflexivity

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl


-- Transitivity

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)


-- Anti-symmetry

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


-- Exersize `≤-antisym-cases`

-- If arguments are `z≤n` and `s≤s`,
-- the first requires `m = zero` and the second does `m = suc _`,
-- which is impossible.


-- Total

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)



