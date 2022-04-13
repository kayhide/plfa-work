module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

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


-- Exercise `+*^`

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap zero n p rewrite *-zero-r n = refl
*-swap (suc m) n p rewrite *-distrib-+-r n p (m * p) | *-swap m n p = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite
    ^-distribʳ-* m n p
    | *-assoc m n ((m ^ p) * (n ^ p))
    | *-swap n (m ^ p) (n ^ p)
    | *-assoc m (m ^ p) (n * (n ^ p))
    = refl

^-identityˡ : ∀ (n : ℕ) → 1 ^ n ≡ 1
^-identityˡ zero = refl
^-identityˡ (suc n) rewrite ^-identityˡ n = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p rewrite ^-identityˡ p = refl
^-*-assoc m (suc n) p
  rewrite
    ^-distribˡ-|-* m p (n * p)
    | ^-distribʳ-* m (m ^ n) p
    | ^-*-assoc m n p
    = refl


-- Exercise `Bin-laws`

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b * 2
from (b I) = from b * 2 + 1

bin-inc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-inc-suc ⟨⟩ = refl
bin-inc-suc (b O) rewrite +-comm (from b * 2) 1 = refl
bin-inc-suc (b I) rewrite bin-inc-suc b | +-comm (from b * 2) 1 = refl

-- bin-to-from : ∀ (b : Bin) → to (from b) ≡ b
-- This does not hold.
-- Counter example: `b = ⟨⟩ O`, where `from b = 0`, `to 0 = ⟨⟩` and `to (from (⟨⟩ O)) ‌= ⟨⟩ ≢ ⟨⟩ O‌‌‌`
--
-- If we assume `⟨⟩ O ≡ ⟨⟩` then it holds.
-- A proof of this case is on the blow.

bin-from-to : ∀ (n : ℕ) → from (to n) ≡ n
bin-from-to zero = refl
bin-from-to (suc n) rewrite bin-inc-suc (to n) | bin-from-to n = refl


-- The following goes a proof of `to (from b) ≡ b` with a hypothesis of
-- `⟨⟩ O ≡ ⟨⟩`.

bin-null : ⟨⟩ O ≡ ⟨⟩
bin-null = {!!}

*-2 : ∀ (n : ℕ) → n * 2 ≡ n + n
*-2 zero = refl
*-2 (suc n) rewrite *-2 n | +-comm n (suc n) = refl

_++_ : Bin → Bin → Bin
_++_ ⟨⟩ y = y
_++_ (x O) ⟨⟩ = x O
_++_ (x O) (y O) = (x ++ y) O
_++_ (x O) (y I) = (x ++ y) I
_++_ (x I) ⟨⟩ = x I
_++_ (x I) (y O) = (x ++ y) I
_++_ (x I) (y I) = (inc (x ++ y)) O

infixl 6 _++_

++-identityʳ : ∀ (b : Bin) → b ++ ⟨⟩ ≡ b
++-identityʳ ⟨⟩ = refl
++-identityʳ (b O) = refl
++-identityʳ (b I) = refl

++-inc : ∀ (x y : Bin) → inc x ++ y ≡ inc (x ++ y)
++-inc x ⟨⟩ rewrite ++-identityʳ x | ++-identityʳ (inc x) = refl
++-inc ⟨⟩ (y O) = refl
++-inc (x O) (y O) = refl
++-inc (x I) (y O) rewrite ++-inc x y = refl
++-inc ⟨⟩ (y I) = refl
++-inc (x O) (y I) = refl
++-inc (x I) (y I) rewrite ++-inc x y = refl


++-twice : ∀ (b : Bin) → b ++ b ≡ b O
++-twice ⟨⟩ rewrite bin-null = refl
++-twice (b O) rewrite ++-twice b = refl
++-twice (b I) rewrite ++-twice b = refl

to-distrib : ∀ (m n : ℕ) → to (m + n) ≡ to m ++ to n
to-distrib zero n = refl
to-distrib (suc m) n rewrite to-distrib m n | ++-inc (to m) (to n) = refl

bin-to-from : ∀ (b : Bin) → to (from b) ≡ b
bin-to-from ⟨⟩ = refl
bin-to-from (b O) rewrite *-2 (from b) | to-distrib (from b) (from b) | bin-to-from b | ++-twice b = refl
bin-to-from (b I) rewrite to-distrib (from b * 2) 1 | *-2 (from b) | to-distrib (from b) (from b) | bin-to-from b | ++-twice b | ++-identityʳ b = refl
