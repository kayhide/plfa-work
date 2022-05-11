module part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import part1.Relations using (_<_; z<s; s<s)
open import part1.Isomorphism using (_⇔_)


infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n


2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))


data Bool : Set where
  true : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎


T : Bool → Set
T true = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n = tt
≤→≤ᵇ (s≤s mn) = ≤→≤ᵇ mn


data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no (¬s≤s ¬m≤n)


_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl


-- Exercise `_<?_`

¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬n<z
zero <? suc n = yes z<s
suc m <? zero = no ¬n<z
suc m <? suc n with m <? n
... | yes m<n = yes (s<s m<n)
... | no ¬m<n = no (¬s<s ¬m<n)


-- Exercise `_≡ℕ?_`

z≡z : zero ≡ zero
z≡z = refl

s≡s : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
s≡s = cong suc

z≢s : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
z≢s ()

s≢z : ∀ {n : ℕ} → ¬ (suc n ≡ zero)
s≢z ()

s≢s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
s≢s m≢n refl = m≢n refl


_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes z≡z
zero ≡ℕ? suc n = no z≢s
suc m ≡ℕ? zero = no s≢z
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes m≡n = yes (s≡s m≡n)
... | no m≢n = no (s≢s m≢n)


----

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p


⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋


toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x


≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness


----

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ _ = false


infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
yes x ×-dec no ¬y = no (λ { ⟨ _ , y ⟩ → ¬y y })
no ¬x ×-dec _ = no λ { ⟨ x , _ ⟩ → ¬x x }


infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ true = true
false ∨ false = false


infixr 6 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _ = yes (inj₁ x)
no ¬x ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no (λ { (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y })


not : Bool → Bool
not true = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x


_⊃_ : Bool → Bool → Bool
true ⊃ true = true
true ⊃ false = false
false ⊃ _ = true

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
yes x →-dec yes y = yes (λ _ → y)
yes x →-dec no ¬y = no λ f → ¬y (f x)
no ¬x →-dec b = yes λ x → ⊥-elim (¬x x)


-- Exercise `erasure`

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no ¬y) = refl
∧-× (no ¬x) _ = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) _ = refl
∨-⊎ (no ¬x) (yes y) = refl
∨-⊎ (no ¬x) (no ¬y) = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no ¬x) = refl


-- Exercise `iff-erasure`

_iff_ : Bool → Bool → Bool
true iff true = true
true iff false = false
false iff true = false
false iff false = true

open _⇔_

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record { to = λ _ → y ; from = λ _ → x })
yes x ⇔-dec no ¬y = no λ AB → ¬y (to AB x)
no ¬x ⇔-dec yes y = no (λ AB → ¬x (from AB y))
no ¬x ⇔-dec no ¬y = yes (record { to = λ x → ⊥-elim (¬x x) ; from = λ y → ⊥-elim (¬y y) })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (yes x) (no ¬y) = refl
iff-⇔ (no ¬x) (yes y) = refl
iff-⇔ (no ¬x) (no ¬y) = refl


----

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m zero _ = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl


_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
(m - n) {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 2 ≡ 3
_ = refl


True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋


-- Exercise `False`

False : ∀ {Q} → Dec Q → Set
False Q = T (not ⌊ Q ⌋)

toWitnessFalse : ∀ {A : Set} {D : Dec A} → T (not ⌊ D ⌋) → ¬ A
toWitnessFalse {A} {yes x} ()
toWitnessFalse {A} {no ¬x} tt = ¬x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → T (not ⌊ D ⌋)
fromWitnessFalse {A} {yes x} ¬x = ¬x x
fromWitnessFalse {A} {no ¬x} _ = tt
