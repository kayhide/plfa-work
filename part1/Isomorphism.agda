module part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm)



_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)


postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g


_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)


same : _+′_ ≡ _+_
same = extensionality λ m → extensionality (λ n → same-app m n)

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g


-- Isomorphism

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
  { to = λ x → x
  ; from = λ y → y
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym AB =
  record
  { to = from AB
  ; from = to AB
  ; from∘to = to∘from AB
  ; to∘from = from∘to AB
  }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans AB BC =
  record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  ; from∘to = λ x →
      begin
        (from AB ∘ from BC) ((to BC ∘ to AB) x)
      ≡⟨⟩
        from AB (from BC (to BC (to AB x)))
      ≡⟨ cong (from AB) (from∘to BC (to AB x)) ⟩
        from AB (to AB x)
      ≡⟨ from∘to AB x ⟩
        x
      ∎
  ; to∘from = λ y →
      begin
        (to BC ∘ to AB) ((from AB ∘ from BC) y)
      ≡⟨⟩
        to BC (to AB (from AB (from BC y)))
      ≡⟨ cong (to BC) (to∘from AB (from BC y)) ⟩
        to BC (from BC y)
      ≡⟨ to∘from BC y ⟩
        y
      ∎
  }


module ≃-Reasoning where
  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin AB = AB

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  _ ≃⟨ AB ⟩ BC = ≃-trans AB BC

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning


-- Embedding

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
  { to = λ x → x
  ; from = λ x → x
  ; from∘to = λ x → refl
  }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans AB BC =
  record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  ; from∘to = λ x →
      begin
        (from AB ∘ from BC) ((to BC ∘ to AB) x)
      ≡⟨⟩
        from AB (from BC (to BC (to AB x)))
      ≡⟨ cong (from AB) (from∘to BC (to AB x)) ⟩
        from AB (to AB x)
      ≡⟨ from∘to AB x ⟩
        x
      ∎
  }

≲-antisym : ∀ {A B : Set}
  → (AB : A ≲ B)
  → (BA : B ≲ A)
  → (to AB ≡ from BA)
  → (from AB ≡ to BA)
    -----------------
  → A ≃ B
≲-antisym AB BA to≡from from≡to =
  record
  { to = to AB
  ; from = from AB
  ; from∘to = from∘to AB
  ; to∘from = λ y →
      begin
        to AB (from AB y)
      ≡⟨ cong (to AB) (cong-app from≡to y) ⟩
        to AB (to BA y)
      ≡⟨ cong-app to≡from (to BA y) ⟩
        from BA (to BA y)
      ≡⟨ from∘to BA y ⟩
        y
      ∎
  }


module ≲-Reasoning where
  infix 1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix 3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin AB = AB

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  _ ≲⟨ AB ⟩ BC = ≲-trans AB BC

  _≲-∎ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  _≲-∎ AB = AB

open ≲-Reasoning


-- Exercise `≃-implies-≲`

≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ AB =
  record
  { to = to AB
  ; from = from AB
  ; from∘to = from∘to AB
  }


-- Exercise `_⇔_`

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl {A} =
  record
  { to = λ x → x
  ; from = λ y → y
  }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym AB =
  record
  { to = from AB
  ; from = to AB
  }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans AB BC =
  record
  { to = to BC ∘ to AB
  ; from = from AB ∘ from BC
  }


-- Exercise `Bin-embedding`

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

to-bin : ℕ → Bin
to-bin zero = ⟨⟩
to-bin (suc n) = inc (to-bin n)

from-bin : Bin → ℕ
from-bin ⟨⟩ = 0
from-bin (b O) = from-bin b * 2
from-bin (b I) = from-bin b * 2 + 1

bin-inc-suc : ∀ (b : Bin) → from-bin (inc b) ≡ suc (from-bin b)
bin-inc-suc ⟨⟩ = refl
bin-inc-suc (b O) rewrite +-comm (from-bin b * 2) 1 = refl
bin-inc-suc (b I) rewrite bin-inc-suc b | +-comm (from-bin b * 2) 1 = refl

bin-from-to : ∀ (n : ℕ) → from-bin (to-bin n) ≡ n
bin-from-to zero = refl
bin-from-to (suc n) rewrite bin-inc-suc (to-bin n) | bin-from-to n = refl

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
  { to = to-bin
  ; from = from-bin
  ; from∘to = bin-from-to
  }
