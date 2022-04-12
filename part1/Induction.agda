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


-- Our second proof: commutativity

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
 begin
   zero + zero
 ≡⟨⟩
   zero
 ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎


-- Our first corollary: rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎


-- Exercise `finite-|-assoc`

-- On the first day
-- 0 : ℕ

-- On the second day
-- 0 : ℕ
-- 1 : ℕ, 0 + 0 = 0, (0 + 0) + 0 = 0 + (0 + 0)

-- On the third day
-- 0 : ℕ
-- 1 : ℕ, 0 + 0 = 0, (0 + 0) + 0 = 0 + (0 + 0)
-- 2 : ℕ, 0 + 1 = 1, 1 + 0 = 1, (0 + 0) + 1 = 0 + (0 + 1), (0 + 1) + 0 = 0 + (1 + 0), (1 + 0) + 0 = 1 + (0 + 0)

-- On the forth day
-- 0 : ℕ
-- 1 : ℕ, 0 + 0 = 0, (0 + 0) + 0 = 0 + (0 + 0)
-- 2 : ℕ, 0 + 1 = 1, 1 + 0 = 1, (0 + 0) + 1 = 0 + (0 + 1), (0 + 1) + 0 = 0 + (1 + 0), (1 + 0) + 0 = 1 + (0 + 0)
-- 3 : ℕ, 0 + 2 = 2, 1 + 1 = 1, 2 + 0 = 2
--  (0 + 0) + 2 = 0 + (0 + 2), (0 + 1) + 1 = 0 + (1 + 1), (1 + 0) + 1 = 1 + (0 + 1),
--  (0 + 2) + 0 = 0 + (2 + 0), (1 + 1) + 0 = 1 + (1 + 0), (2 + 0) + 0 = 2 + (0 + 0)


-- Asociativity with rewrite

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


-- Commutativity with rewrite

+-identityʳ′ : ∀ (n : ℕ) → n + zero ≡ n
+-identityʳ′ zero = refl
+-identityʳ′ (suc n) rewrite +-identityʳ′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identityʳ′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


-- Exercise `+-swap`

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-comm n (suc (m + p)) | +-comm (m + p) n | +-swap m n p = refl


-- Exercise `*-distrib-+`

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl


-- Exercise `*-assoc`

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl


-- Exercise `*-comm`

*-zero-r : ∀ (n : ℕ) → n * zero ≡ zero
*-zero-r zero = refl
*-zero-r (suc n) rewrite *-zero-r n = refl

*-distrib-+-r : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*-distrib-+-r zero n p = refl
*-distrib-+-r (suc m) n p rewrite *-distrib-+-r m n p | +-assoc n p (m * n + m * p) | +-swap p (m * n) (m * p) | +-assoc n (m * n) (p + m * p) = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero-r n = refl
*-comm (suc m) n rewrite *-distrib-+-r n 1 m | *-comm m n | *-identityʳ n = refl


-- Exercise `0∸n≡0`

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl


-- Exercise `∸-|-assoc`

∸-|-assoc-suc : ∀ (m n : ℕ) → m ∸ suc n ≡ m ∸ 1 ∸ n
∸-|-assoc-suc zero n rewrite 0∸n≡0 n = refl
∸-|-assoc-suc (suc m) n = refl

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m zero p = refl
∸-|-assoc m (suc n) p
  rewrite
    ∸-|-assoc-suc m (n + p)
    | ∸-|-assoc-suc m n
    | ∸-|-assoc (m ∸ 1) n p
    = refl
