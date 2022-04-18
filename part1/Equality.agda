module part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


infix 4 _≡_


sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl


cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl _ = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst p refl px = px


module ≡-Reasoning {A : Set} where
  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin xy = xy

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ xy = xy

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ xy ⟩ yz = trans xy yz

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  xx ∎ = refl

open ≡-Reasoning


trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans′ {A} {x} {y} {z} xy yz =
  begin
    x
  ≡⟨ xy ⟩
    y
  ≡⟨ yz ⟩
    z
  ∎

-- Exercise `trans` and `≡-Reasoning`
-- We cannot use `trans′` as the definition of `trans` because
-- `_≡⟨_⟩_` is defined by using `trans`.



data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ∎


-- Exercise `≤-Reasoning`

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

postulate
  ≤-identity : ∀ {x : ℕ} → x ≤ x
  ≤-trans : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≡-≤ : ∀ {x y : ℕ} → x ≡ y → x ≤ y

module ≤-Reasoning where
  infix 1 begin≤_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _∎≤

  begin≤_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin≤ xy = xy

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ xy = xy

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ xy ⟩ yz = ≤-trans xy yz

  _∎≤ : ∀ (x : ℕ)
      -----
    → x ≤ x
  xx ∎≤ = ≤-identity

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q pq =
  begin≤
    zero + p
  ≤⟨ pq ⟩
    zero + q
  ∎≤
+-monoʳ-≤ (suc n) p q pq =
  begin≤
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q pq) ⟩
    suc (n + q)
  ∎≤

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p mn =
  begin≤
    m + p
  ≤⟨ ≡-≤ (+-comm m p) ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n mn ⟩
    p + n
  ≤⟨ ≡-≤ (+-comm p n) ⟩
    n + p
  ∎≤

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q mn pq =
  begin≤
    m + p
  ≤⟨ +-monoˡ-≤ m n p mn ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q pq ⟩
    n + q
  ∎≤

--

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)


{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm m n = ev


+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl


even-comm′ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm′ m n ev with m + n    | +-comm m n
...                  | .(n + m) | refl = ev

even-comm″ : ∀ (m n : ℕ) → even (m + n) → even (n + m)
even-comm″ m n = subst even (+-comm m n)
