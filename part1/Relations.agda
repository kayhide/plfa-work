module part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)


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


-- Monotonicity

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


-- Exercise `*-mono-≤`

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


-- Strict inequality

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n


-- Exercise `<-trans`

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)


-- Exercise `trichotomy`

_>_ : ℕ → ℕ → Set
_>_ m n = n < m

data Trichotomy (m n : ℕ) : Set where
  asc : m < n → Trichotomy m n
  eql : m ≡ n → Trichotomy m n
  desc : m > n → Trichotomy m n

<-tricotomy : ∀ (m n : ℕ) → Trichotomy m n
<-tricotomy zero zero = eql refl
<-tricotomy zero (suc n) = asc z<s
<-tricotomy (suc m) zero = desc z<s
<-tricotomy (suc m) (suc n) with <-tricotomy m n
... | asc m<n = asc (s<s m<n)
... | eql m≡n = eql (cong suc m≡n)
... | desc m>n = desc (s<s m>n)


-- Exercise `+-mono-<`

+-monoˡ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoˡ-< zero p q p<q = p<q
+-monoˡ-< (suc n) p q p<q = s<s (+-monoˡ-< n p q p<q)

+-monoʳ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoʳ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoˡ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoʳ-< m n p m<n) (+-monoˡ-< n p q p<q)


-- Exercise `≤-iff-<`

≤-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-< zero .(suc _) (s≤s sm≤n) = z<s
≤-< (suc m) .(suc _) (s≤s sm≤n) = s<s (≤-< m _ sm≤n)

<-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-≤ zero .(suc _) z<s = s≤s z≤n
<-≤ (suc m) .(suc _) (s<s m<n) = s≤s (<-≤ m _ m<n)


-- Exercise `<-trans-revisited`

≤-suc : ∀ (m n : ℕ) → m ≤ n → m ≤ suc n
≤-suc zero n m≤n = z≤n
≤-suc (suc m) (suc n) (s≤s m≤n) = s≤s (≤-suc m n m≤n)

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n@(suc n⁻) p@(suc p⁻) m<n (s<s n⁻<p⁻)
  = ≤-< m p (≤-trans (<-≤ m n m<n) (≤-suc n p⁻ (<-≤ n⁻ p⁻ n⁻<p⁻)))


-- Even and odd

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)


e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)

o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)


-- Exercise `o+o≡e`

odd-comm : ∀ (m n : ℕ) → odd (m + n) ≡ odd (n + m)
odd-comm m n = cong odd (+-comm m n)

e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
e+o≡o {m} {n} em on rewrite odd-comm m n = o+e≡o on em

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc em) on = suc (e+o≡o em on)


-- Exercise `Bin-predicates`

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



data One : Bin → Set where
  one : One (inc ⟨⟩)
  suc : ∀ {b : Bin} → One b → One (inc b)

data Can : Bin → Set where
  zero : Can ⟨⟩
  one : ∀ {b : Bin} → One b → Can b

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can-inc zero = one one
can-inc (one x) = one (suc x)

can-to : ∀ (n : ℕ) → Can (to n)
can-to zero = zero
can-to (suc n) = can-inc (can-to n)


one-to-from : ∀ {b : Bin} → One b → to (from b) ≡ b
one-to-from one = refl
one-to-from (suc {b} ob) rewrite bin-inc-suc b = cong inc (one-to-from ob)

can-to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b
can-to-from zero = refl
can-to-from (one ob) = one-to-from ob

