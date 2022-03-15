module Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Exercise
seven : ℕ
seven = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Addition

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- Exercise
+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎


-- Multplication

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

-- Exercise
*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    (suc 2) * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + ((suc 1) * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + ((suc 0) * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

-- Exponentiation

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

-- Exercise
^-example : 3 ^ 4 ≡ 81
^-example =
  begin
    3 ^ 4
  ≡⟨⟩
    3 ^ (suc 3)
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 ^ (suc 2))
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 ^ (suc 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ (suc 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

-- Monus

_∸_  : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

-- Exercise

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
   3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Precedence

infixl 6 _+_ _∸_
infixl 7 _*_

-- Writing definitions interactively

_+'_ : ℕ → ℕ → ℕ
zero +' n = n
suc m +' n = suc (m + n)

-- More pragmas

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

inc-eleven : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
inc-eleven =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    inc (⟨⟩ I O I) O
  ≡⟨⟩
    inc (⟨⟩ I O) O O
  ≡⟨⟩
    (⟨⟩ I I) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

to-0 : to 0 ≡ ⟨⟩ O
to-0 =
  begin
    to 0
  ≡⟨⟩
    ⟨⟩ O
  ∎

to-1 : to 1 ≡ ⟨⟩ I
to-1 =
  begin
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ∎

to-2 : to 2 ≡ ⟨⟩ I O
to-2 =
  begin
    to 2
  ≡⟨⟩
    ⟨⟩ I O
  ∎

to-3 : to 3 ≡ ⟨⟩ I I
to-3 =
  begin
    to 3
  ≡⟨⟩
    ⟨⟩ I I
  ∎

to-4 : to 4 ≡ ⟨⟩ I O O
to-4 =
  begin
    to 4
  ≡⟨⟩
    ⟨⟩ I O O
  ∎

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = from b * 2
from (b I) = from b * 2 + 1

from-0 : from ⟨⟩ ≡ 0
from-0 =
  begin
    from ⟨⟩
  ≡⟨⟩
    0
  ∎

from-1 : from (⟨⟩ I) ≡ 1
from-1 =
  begin
    from (⟨⟩ I)
  ≡⟨⟩
    1
  ∎

from-2 : from (⟨⟩ I O) ≡ 2
from-2 =
  begin
    from (⟨⟩ I O)
  ≡⟨⟩
    2
  ∎

from-3 : from (⟨⟩ I I) ≡ 3
from-3 =
  begin
    from (⟨⟩ I I)
  ≡⟨⟩
    3
  ∎

from-4 : from (⟨⟩ I O O) ≡ 4
from-4 =
  begin
    from (⟨⟩ I O O)
  ≡⟨⟩
    4
  ∎

