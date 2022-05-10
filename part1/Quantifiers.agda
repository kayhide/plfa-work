module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong-app)
open Eq.≡-Reasoning
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; z≤n; s≤s; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; +-comm; +-suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import part1.Isomorphism using (_≃_; extensionality)


∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    ---------------------
  → B M
∀-elim L M = L M


-- Exercise `∀-distrib-×`

∀-distrib-× : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ f → ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩
    ; from = λ { ⟨ f , g ⟩ → λ x → ⟨ (f x) , (g x) ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ y → refl
    }


-- Exercise `⊎∀-implies-∀⊎`

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
  → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) x = inj₂ (g x)


-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set}
--   → (∀ (x : A) → B x ⊎ C x)
--   → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ f = {!!}
-- The converse does not hold.
-- It is because the "universal of disjunctions" shares the concrete type of `x` while
-- "disjunction of universals" does not share the type of `x`.


-- Exercise `∀-×`

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri


postulate
  extensionality′ : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
    ; from = λ { ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ aa → baa
               ; ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ bb → bbb
               ; ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ cc → bcc
               }
    ; from∘to = λ _ → extensionality′ λ { aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ _ → refl
    }


----

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ

infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-proj₁ : {A : Set} {B : A → Set} → ∃ {A} B → A
∃-proj₁ ⟨ x , _ ⟩ = x

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B


∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y


∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to = λ { f ⟨ x , y ⟩ → f x y }
    ; from = λ { g x y → g ⟨ x , y ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ { g → extensionality λ { ⟨ x , y ⟩ → refl } }
    }


-- Exercise `∃-distrib-⊎`

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ { ⟨ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
             ; ⟨ x , inj₂ y ⟩ → inj₂ ⟨ x , y ⟩
             }
    ; from = λ { (inj₁ ⟨ x , y ⟩) → ⟨ x , inj₁ y ⟩
               ; (inj₂ ⟨ x , y ⟩) → ⟨ x , inj₂ y ⟩
               }
    ; from∘to = λ { ⟨ x , inj₁ y ⟩ → refl
                  ; ⟨ x , inj₂ y ⟩ → refl
                  }
    ; to∘from = λ { (inj₁ ⟨ x , y ⟩) → refl
                  ; (inj₂ ⟨ x , y ⟩) → refl
                  }
    }


-- Exercise `∃×-implies-×∃`

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = λ { ⟨ x , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ x , b ⟩ , ⟨ x , c ⟩ ⟩  }


-- Exercise `∃-⊎`

∃-⊎ : {B : Tri → Set} → (∃[ x ] B x) ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
    { to = λ { ⟨ aa , t ⟩ → inj₁ t
             ; ⟨ bb , t ⟩ → inj₂ (inj₁ t)
             ; ⟨ cc , t ⟩ → inj₂ (inj₂ t)
             }
    ; from = λ { (inj₁ t) → ⟨ aa , t ⟩
               ; (inj₂ (inj₁ t)) → ⟨ bb , t ⟩
               ; (inj₂ (inj₂ t)) → ⟨ cc , t ⟩
               }
    ; from∘to = λ { ⟨ aa , t ⟩ → refl
                  ; ⟨ bb , t ⟩ → refl
                  ; ⟨ cc , t ⟩ → refl
                  }
    ; to∘from = λ { (inj₁ t) → refl
                  ; (inj₂ (inj₁ t)) → refl
                  ; (inj₂ (inj₂ t)) → refl
                  }
    }


----

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)


even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} → odd n  → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ zero = ⟨ zero , refl ⟩
even-∃ (suc x) with odd-∃ x
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (suc x) with even-∃ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd n

∃-even ⟨ zero , refl ⟩ = zero
∃-even ⟨ suc m , refl ⟩ = suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = suc (∃-even ⟨ m , refl ⟩)


-- Exercise `∃-even-odd`

-- It is difficult to construct a proof in a way such that
-- termination checker agrees.
-- I could not find out how to make it work and the following
-- does not pass termination check.

n+1 : ∀ (n : ℕ) → n + 1 ≡ suc n
n+1 zero = refl
n+1 (suc n) = cong suc (n+1 n)

{-# TERMINATING #-}
∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

∃-even′ ⟨ zero , refl ⟩ = zero
∃-even′ ⟨ suc m , refl ⟩ = suc (∃-odd′ ⟨ m , p ⟩)
  where
  p : m + (m + zero) + 1 ≡ m + suc (m + zero)
  p =
    begin
      m + (m + zero) + 1
    ≡⟨ +-assoc m (m + zero) 1 ⟩
      m + ((m + zero) + 1)
    ≡⟨ cong (m +_) (n+1 (m + zero)) ⟩
      m + suc (m + zero)
    ∎

∃-odd′ ⟨ m , refl ⟩ rewrite cong odd (n+1 (2 * m)) = suc (∃-even′ ⟨ m , refl ⟩)


-- Exercise `∃-|-≤`

∃-≤ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
∃-≤ {_} {z} z≤n = ⟨ z , +-identityʳ z ⟩
∃-≤ {suc y} (s≤s yz) with ∃-≤ {y} yz
... | ⟨ x , refl ⟩ = ⟨ x , +-suc x y ⟩

≤-∃ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
≤-∃ {zero} ⟨ x , refl ⟩ = z≤n
≤-∃ {suc y} ⟨ x , refl ⟩ with s≤s (≤-∃ {y} ⟨ x , refl ⟩)
... | yz rewrite sym (+-suc x y) = yz


----

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      = λ { ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    = λ { ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to = λ ¬∃xy → extensionality (λ { ⟨ x , y ⟩ → refl })
    ; to∘from = λ ∀¬xy → refl
    }


-- Exercise `∃¬-implies-¬∀`

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ = λ z → y (z x)


-- The converse does not hold.
-- A counterexample is there is no instance of A.

-- ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
--   → ¬ (∀ x → B x)
--     --------------
--   → ∃[ x ] (¬ B x)
-- ¬∀-implies-∃¬ ¬y = ⟨ {!!} , {!!} ⟩


-- Exercise `Bin-isomorphism`

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
from (b O) = from b + from b
from (b I) = 1 + from b + from b

postulate
  bin-from-to : ∀ (n : ℕ) → from (to n) ≡ n


module OneBin where
  infixl 6 _++_
  _++_ : Bin → Bin → Bin
  _++_ ⟨⟩ y = y
  _++_ (x O) ⟨⟩ = x O
  _++_ (x O) (y O) = (x ++ y) O
  _++_ (x O) (y I) = (x ++ y) I
  _++_ (x I) ⟨⟩ = x I
  _++_ (x I) (y O) = (x ++ y) I
  _++_ (x I) (y I) = (inc (x ++ y)) O

  ++-inc : ∀ (x y : Bin) → inc x ++ y ≡ inc (x ++ y)
  ++-inc ⟨⟩ ⟨⟩ = refl
  ++-inc ⟨⟩ (y O) = refl
  ++-inc ⟨⟩ (y I) = refl
  ++-inc (x O) ⟨⟩ = refl
  ++-inc (x O) (y O) = refl
  ++-inc (x O) (y I) = refl
  ++-inc (x I) ⟨⟩ = refl
  ++-inc (x I) (y O) rewrite ++-inc x y = refl
  ++-inc (x I) (y I) rewrite ++-inc x y = refl

  to-distrib-+ : ∀ (m n : ℕ) → to (m + n) ≡ to m ++ to n
  to-distrib-+ zero n = refl
  to-distrib-+ (suc m) n rewrite to-distrib-+ m n | ++-inc (to m) (to n) = refl


  data One : Bin → Set where
    ⟨I⟩ : One (⟨⟩ I)
    _O : ∀ {b : Bin} → One b → One (b O)
    _I : ∀ {b : Bin} → One b → One (b I)

  one-inc : ∀ {b : Bin} → One b → One (inc b)
  one-inc ⟨I⟩ = ⟨I⟩ O
  one-inc (o O) = o I
  one-inc (o I) = one-inc o O

  ++-twice : ∀ {b : Bin} → One b → b ++ b ≡ b O
  ++-twice ⟨I⟩ = refl
  ++-twice (o O) rewrite ++-twice o = refl
  ++-twice (o I) rewrite ++-twice o = refl

  one-to-from : ∀ {b : Bin} → One b → to (from b) ≡ b
  one-to-from ⟨I⟩ = refl
  one-to-from (_O {b} o) rewrite to-distrib-+ (from b) (from b) | one-to-from o | ++-twice o = refl
  one-to-from (_I {b} o) rewrite to-distrib-+ (from b) (from b) | one-to-from o | ++-twice o = refl


  data Can : Bin → Set where
    zero : Can ⟨⟩
    one : ∀ {b : Bin} → One b → Can b

  can-inc : ∀ {b : Bin} → Can b → Can (inc b)
  can-inc zero = one ⟨I⟩
  can-inc (one x) = one (one-inc x)

  can-to : ∀ (n : ℕ) → Can (to n)
  can-to zero = zero
  can-to (suc n) = can-inc (can-to n)

  can-to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b
  can-to-from zero = refl
  can-to-from (one x) = one-to-from x

  ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
  ≡One ⟨I⟩ ⟨I⟩ = refl
  ≡One (x O) (y O) = cong _O (≡One x y)
  ≡One (x I) (y I) = cong _I (≡One x y)

  ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
  ≡Can zero zero = refl
  ≡Can (one x) (one y) = cong one (≡One x y)

  proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → ∃-proj₁ cb ≡ ∃-proj₁ cb′ → cb ≡ cb′
  proj₁≡→Can≡ {⟨ b , cb ⟩} {⟨ b′ , cb′ ⟩} refl rewrite ≡Can cb cb′ = refl

  Bin-isomorphism : ℕ ≃ ∃[ b ] Can b
  Bin-isomorphism =
    record
      { to = λ n → ⟨ to n , can-to n ⟩
      ; from = λ { ⟨ b , cb ⟩ → from b }
      ; from∘to = λ n → bin-from-to n
      ; to∘from = λ { ⟨ b , cb ⟩ → proj₁≡→Can≡ (can-to-from cb) }
      }


-- This approach uses the definition of `One` and `Can` in terms of `inc` function.
-- With this definision, I have already proved several properties in `Bin-laws` and `Bin-predicates`
-- and I will postulate them in the following.
-- As a result, this approach turned out to be difficult to prove `≡One`
-- because `One` is not defined inductively and thus, is not applicable to consume inductively.
module OneInc where
  data One : Bin → Set where
    one : One ⟨⟩
    suc : ∀ {b : Bin} → One b → One (inc b)

  data Can : Bin → Set where
    zero : Can ⟨⟩
    one : ∀ {b : Bin} → One b → Can (inc b)

  postulate
    can-inc : ∀ {b : Bin} → Can b → Can (inc b)
    can-to : ∀ (n : ℕ) → Can (to n)
    can-to-from : ∀ {b : Bin} → Can b → to (from b) ≡ b

  inc-neq-nil : ∀ {b : Bin} → ¬ (inc b ≡ ⟨⟩)
  inc-neq-nil {⟨⟩} = λ()
  inc-neq-nil {(b O)} = λ()
  inc-neq-nil {(b I)} = λ()

  -- Try heterogeneous equality to prove `≡One`.
  -- Even though it enables us to case-split over both `Bin`,
  -- I could not find out how to recursively prove `≅One`
  data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
    refl : x ≅ x

  ≅-≡ : {A : Set} {x y : A} → x ≅ y → x ≡ y
  ≅-≡ refl = refl

  ≅-cong : {A B : Set} {x y : A} → (f : A → B) → x ≅ y → f x ≅ f y
  ≅-cong f refl = refl


  inc-≡ : {b b′ : Bin} → One b → One b′ → inc b ≡ inc b′ → b ≡ b′
  inc-≡ {.⟨⟩} {.⟨⟩} one one p = refl
  inc-≡ {.⟨⟩} {.(inc _)} one (suc oy) p = {!!}
  inc-≡ {.(inc _)} {y} (suc ox) oy p = {!!}

  ≅One : ∀ {b b′ : Bin} (o : One b) → (o′ : One b′) → b ≡ b′ → o ≅ o′
  ≅One one one refl = refl
  ≅One one (suc y) p = ⊥-elim (inc-neq-nil (sym p))
  ≅One (suc x) one p = ⊥-elim (inc-neq-nil p)
  ≅One {b} {b′} (suc x) (suc y) p with inc-≡ x y p
  ... | refl = ≅-cong suc (≅One x y refl)

  ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
  ≡One {b} o o′ = ≅-≡ (≅One o o′ refl)

  postulate
    ≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′

  proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → ∃-proj₁ cb ≡ ∃-proj₁ cb′ → cb ≡ cb′
  proj₁≡→Can≡ {⟨ b , cb ⟩} {⟨ b′ , cb′ ⟩} refl rewrite ≡Can cb cb′ = refl

  Bin-isomorphism : ℕ ≃ ∃[ b ] Can b
  Bin-isomorphism =
    record
      { to = λ n → ⟨ to n , can-to n ⟩
      ; from = λ { ⟨ b , cb ⟩ → from b }
      ; from∘to = λ n → bin-from-to n
      ; to∘from = λ { ⟨ b , cb ⟩ → proj₁≡→Can≡ (can-to-from cb) }
      }
