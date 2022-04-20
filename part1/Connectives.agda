module part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import part1.Isomorphism using (_≃_; _≲_; extensionality)
open part1.Isomorphism.≃-Reasoning


data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B


proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y


η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_



record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B

open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl


data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true , aa ⟩ = 1
×-count ⟨ true , bb ⟩ = 2
×-count ⟨ true , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6


×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to      = λ { ⟨ a , b ⟩ → ⟨ b , a ⟩ }
    ; from    = λ { ⟨ b , a ⟩ → ⟨ a , b ⟩ }
    ; from∘to = λ { ⟨ a , b ⟩ → refl }
    ; to∘from = λ { ⟨ b , a ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ }
    ; from    = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ }
    ; from∘to = λ { ⟨ ⟨ a , b ⟩ , c ⟩ → refl }
    ; to∘from = λ { ⟨ a , ⟨ b , c ⟩ ⟩ → refl }
    }


-- Exercise `⇔≃×`

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A

open _⇔_


⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ x → ⟨ to x , from x ⟩
    ; from = λ { ⟨ A→B , B→A ⟩ →
        record
          { to = A→B
          ; from = B→A
          }
        }
    ; from∘to = λ x → refl
    ; to∘from = λ { ⟨ A→B , B→A ⟩ → refl }
    }


--

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl


record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = tt′

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ { ⟨ _ , A ⟩ → A }
    ; from = λ A → ⟨ tt , A ⟩
    ; from∘to = λ { ⟨ tt , A ⟩ → refl }
    ; to∘from = λ A → refl
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎


--

data _⨄_ (A B : Set) : Set where
  inj₁ : A → A ⨄ B
  inj₂ : B → A ⨄ B

case-⨄ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⨄ B
    -------
  → C
case-⨄ AC BC (inj₁ x) = AC x
case-⨄ AC BC (inj₂ x) = BC x

η-⨄ : ∀ {A B : Set} (w : A ⨄ B) → case-⨄ inj₁ inj₂ w ≡ w
η-⨄ (inj₁ x) = refl
η-⨄ (inj₂ x) = refl

uniq-⨄ : ∀ {A B C : Set} (h : A ⨄ B → C) (w : A ⨄ B) →
  case-⨄ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⨄ h (inj₁ x) = refl
uniq-⨄ h (inj₂ x) = refl

infixr 1 _⨄_


⨄-count : Bool ⨄ Tri → ℕ
⨄-count (inj₁ true) = 1
⨄-count (inj₁ false) = 2
⨄-count (inj₂ aa) = 3
⨄-count (inj₂ bb) = 4
⨄-count (inj₂ cc) = 5


-- Exercise `⨄-comm`

⨄-comm : ∀ {A B : Set} → A ⨄ B ≃ B ⨄ A
⨄-comm =
  record
    { to = λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
    ; from = λ { (inj₁ y) → inj₂ y ; (inj₂ y) → inj₁ y }
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ y) → refl ; (inj₂ y) → refl }
    }


-- Exercise `⨄-assoc`

⨄-assoc : ∀ {A B C : Set} → (A ⨄ B) ⨄ C ≃ A ⨄ (B ⨄ C)
⨄-assoc =
  record
    { to = λ { (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x) ; (inj₂ x) → inj₂ (inj₂ x) }
    ; from = λ { (inj₁ x) → inj₁ (inj₁ x) ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x) ; (inj₂ (inj₂ x)) → inj₂ x }
    ; from∘to = λ { (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ x)) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ x)) → refl }
    }


--

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()


-- Exercise `⊥-identityˡ`

⊥-identityˡ : ∀ {A : Set} → ⊥ ⨄ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ x) → x }
    ; from = λ x → inj₂ x
    ; from∘to = λ { (inj₂ x) → refl }
    ; to∘from = λ y → refl
    }


-- Exercise `⊥-identityʳ`

⊥-identityʳ : ∀ {A : Set} → A ⨄ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⨄ ⊥)
  ≃⟨ ⨄-comm ⟩
    (⊥ ⨄ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎


--

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim f x = f x

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
... | aa | aa = 1
... | aa | bb = 2
... | aa | cc = 3
... | bb | aa = 4
... | bb | bb = 5
... | bb | cc = 6
... | cc | aa = 7
... | cc | bb = 8
... | cc | cc = 9


currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ f →  λ { ⟨ x , y ⟩ → f x y }
    ; from = λ g → λ x y → g ⟨ x , y ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality (λ { ⟨ x , y ⟩ → refl })
    }

→-distrib-⨄ : ∀ {A B C : Set} → (A ⨄ B → C) ≃ ((A → C) × (B → C))
→-distrib-⨄ =
  record
    { to = λ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩
    ; from = λ { ⟨ g , h ⟩ → λ { (inj₁ x) → g x ; (inj₂ x) → h x } }
    ; from∘to = λ f → extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from = λ { ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ f → extensionality λ x → η-× (f x)
    ; to∘from = λ { ⟨ g , h ⟩ → refl }
    }

×-distrib-⨄ : ∀ {A B C : Set} → (A ⨄ B) × C ≃ (A × C) ⨄ (B × C)
×-distrib-⨄ =
  record
    { to = λ { ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩ ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩ }
    ; from = λ { (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩ ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩ }
    ; from∘to = λ { ⟨ inj₁ x , z ⟩ → refl ; ⟨ inj₂ y , z ⟩ → refl }
    ; to∘from = λ { (inj₁ ⟨ x , z ⟩) → refl ; (inj₂ ⟨ y , z ⟩) → refl }
    }

⨄-distrib-× : ∀ {A B C : Set} → (A × B) ⨄ C ≲ (A ⨄ C) × (B ⨄ C)
⨄-distrib-× =
  record
    { to = λ { (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
             ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
             }
    ; from = λ { ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
               ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
               ; ⟨ inj₂ z , _ ⟩ → inj₂ z
               }
    ; from∘to = λ { (inj₁ ⟨ x , y ⟩) → refl
                  ; (inj₂ z) → refl
                  }
    }


-- Exercise `⨄-weak-×`

⨄-weak-× : ∀ {A B C : Set} → (A ⨄ B) × C → A ⨄ (B × C)
⨄-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⨄-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩


-- Exercise `⨄×-implies-×⨄`

⨄×-implies-×⨄ : ∀ {A B C D : Set} → (A × B) ⨄ (C × D) → (A ⨄ C) × (B ⨄ D)
⨄×-implies-×⨄ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⨄×-implies-×⨄ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- The converse does not hold.
-- Counter example: ⟨ inj₁ a , inj₂ d ⟩

