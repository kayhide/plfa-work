module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise

-- (*) (^)
-- identity: 1 * x ≡ x, x * 1 ≡ x
-- associativity: (x * y) * z ≡ x * (y * z)
-- commutativity: x * y ≡ y * x
-- distributivity: (x * y) ^ a ≡ x ^ a * y ^ a

-- (>=>)
-- identity: pure >=> f ≡ f, f >=> pure ≡ f
-- associativity: (f >=> g) >=> h ≡ f >=> (g >=> h)
-- commutativity: f >=> g /= g >=> f


-- Our first proof: associativity

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
   suc m + (n + p)
  ∎
