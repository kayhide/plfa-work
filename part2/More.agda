module part2.More where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)


infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_


data Type : Set where
  `ℕ : Type
  _⇒_ : Type → Type → Type
  Nat : Type
  _`×_ : Type → Type → Type


data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context


data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B


data _⊢_ : Context → Type → Set where

  -- variables
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions
  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals
  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  -- fixpoint
  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

  -- primitive numbers
  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let
  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ B

  -- products
  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      ----------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ----------
    → Γ ⊢ B

  -- products alternative
  case× : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      -------------
    → Γ ⊢ C


length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {_ , A} {zero} (s≤s z≤n) = A
lookup {Γ , _} {suc n} (s≤s p) = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero} (s≤s z≤n) = Z
count {_ , _} {suc n} (s≤s p) = S count p

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = ` count (toWitness n∈Γ)


ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
ext ρ Z = Z
ext ρ (S x) = S ρ x

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` ρ x
rename ρ (ƛ N) = ƛ rename (ext ρ) N
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ `zero = `zero
rename ρ (`suc M) = `suc rename ρ M
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N) = μ (rename (ext ρ) N)
rename ρ (con n) = con n
rename ρ (M `* N) = rename ρ M `* rename ρ N
rename ρ (`let M N) = `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩ = `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L) = `proj₁ (rename ρ L)
rename ρ (`proj₂ L) = `proj₂ (rename ρ L)
rename ρ (case× L M) = case× (rename ρ L) (rename (ext (ext ρ)) M)
