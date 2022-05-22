module part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import part1.Isomorphism
open import part2.Lambda


V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ ()
V¬—→ V-zero ()
V¬—→ (V-suc x) (ξ-suc M→N) = V¬—→ x M→N


—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M→N x = V¬—→ x M→N


infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    ---------------
  → Canonical V ⦂ A
canonical (⊢ƛ ⊢N) V-ƛ = C-ƛ ⊢N
canonical ⊢zero V-zero = C-zero
canonical (⊢suc ⊢V) (V-suc VV) = C-suc (canonical ⊢V VV)

value : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → Value M
value (C-ƛ ⊢N) = V-ƛ
value C-zero = V-zero
value (C-suc CM) = V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N) = ⊢ƛ ⊢N
typed C-zero = ⊢zero
typed (C-suc CM) = ⊢suc (typed CM)


data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ ⊢N) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L→X = step (ξ-·₁ L→X)
... | done VL with progress ⊢M
...   | step M→Y = step (ξ-·₂ VL M→Y)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _ = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M→N = step (ξ-suc M→N)
... | done VM = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L→X = step (ξ-case L→X)
... | done VL with canonical ⊢L VL
...   | C-zero = step β-zero
...   | C-suc CL = step (β-suc (value CL))
progress (⊢μ ⊢M) = step β-μ


-- postulate
--   progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ] M —→ N


-- Exercise `Progress-≃`

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ] M —→ N
Progress-≃ {M} =
  record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : Progress M → Value M ⊎ ∃[ N ] M —→ N
    to (step {N} M→N) = inj₂ ⟨ N , M→N ⟩
    to (done VM) = inj₁ VM

    from : Value M ⊎ ∃[ N ] M —→ N → Progress M
    from (inj₁ VM) = done VM
    from (inj₂ ⟨ _ , M→N ⟩) = step M→N

    from∘to : (p : Progress M) → from (to p) ≡ p
    from∘to (step _) = refl
    from∘to (done _) = refl

    to∘from : (q : Value M ⊎ ∃[ N ] M —→ N) → to (from q) ≡ q
    to∘from (inj₁ _) = refl
    to∘from (inj₂ _) = refl


-- Exercise `progress′`

progress′′ : ∀ M {A} → ∅ ⊢ M ⦂ A → (∃[ N ] M —→ N) ⊎ Value M
progress′′ .(ƛ _ ⇒ _) (⊢ƛ ⊢N) = inj₂ V-ƛ
progress′′ (L · M) (⊢L · ⊢M) with progress′′ L ⊢L
... | inj₁ ⟨ X , L→X ⟩ = inj₁ ⟨ X · M , ξ-·₁ L→X ⟩
... | inj₂ VL with progress′′ M ⊢M
...   | inj₁ ⟨ Y , M→Y ⟩ = inj₁ ⟨ L · Y , ξ-·₂ VL M→Y ⟩
...   | inj₂ VM with canonical ⊢L VL
...     | C-ƛ {x} {N = N} C = inj₁ ⟨ N [ x := M ] , β-ƛ VM ⟩
progress′′ .`zero ⊢zero = inj₂ V-zero
progress′′ (`suc M) (⊢suc ⊢M) with progress′′ M ⊢M
... | inj₁ ⟨ N , M→N ⟩ = inj₁ ⟨ `suc N , ξ-suc M→N ⟩
... | inj₂ VM = inj₂ (V-suc VM)
progress′′ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case ⊢L ⊢M ⊢N) with progress′′ L ⊢L
... | inj₁ ⟨ X , L→X ⟩ = inj₁ ⟨ case X [zero⇒ M |suc x ⇒ N ] , ξ-case L→X ⟩
... | inj₂ VL with canonical ⊢L VL
...   | C-zero = inj₁ ⟨ M , β-zero ⟩
...   | C-suc {V} CL = inj₁ ⟨ N [ x := V ] , (β-suc (value CL)) ⟩
progress′′ (μ x ⇒ M) (⊢μ ⊢M) = inj₁ ⟨ M [ x := μ x ⇒ M ] , β-μ  ⟩


⊎-swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap (inj₁ x) = inj₂ x
⊎-swap (inj₂ y) = inj₁ y

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ (∃[ N ] M —→ N)
progress′ m x = ⊎-swap (progress′′ m x)


-- Exercise `value?`

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? (⊢ƛ _) = yes V-ƛ
value? (⊢L · ⊢M) with progress ⊢L
... | step L→L′ = no (—→¬V (ξ-·₁ L→L′))
... | done VL with progress ⊢M
...   | step M→M′ = no (—→¬V (ξ-·₂ VL M→M′))
...   | done VM with canonical ⊢L VL
...     | C-ƛ _ = no (—→¬V (β-ƛ VM))
value? ⊢zero = yes V-zero
value? (⊢suc ⊢M) with progress ⊢M
... | step M→M′ = no (—→¬V (ξ-suc M→M′))
... | done VM = yes (V-suc VM)
value? (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L→L′ = no (—→¬V (ξ-case L→L′))
... | done VL with canonical ⊢L VL
... | C-zero = no (—→¬V β-zero)
... | C-suc CL = no (—→¬V (β-suc (value CL)))
value? (⊢μ ⊢M) = no (—→¬V β-μ)


----

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z = Z
ext ρ (S x≢y ∋x) = S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ---------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w) = ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N) = ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M) = rename ρ ⊢L · rename ρ ⊢M
rename ρ ⊢zero = ⊢zero
rename ρ (⊢suc ⊢M) = ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N) = ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M) = ⊢μ (rename (ext ρ) ⊢M)


weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ---------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename (λ()) ⊢M

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    -------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
    ρ : ∀ {z C}
      → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
        -------------------------
      → Γ , x ⦂ B ∋ z ⦂ C
    ρ Z = Z
    ρ (S x≢x Z) = ⊥-elim (x≢x refl)
    ρ (S z≢x (S _ ∋z)) = S z≢x ∋z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    -------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
    ρ : ∀ {z C}
      → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
        -------------------------
      → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
    ρ Z = S x≢y Z
    ρ (S z≢x Z) = Z
    ρ (S z≢x (S z≢y ∋z)) = S z≢y (S z≢x ∋z)


----

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _ = weaken ⊢V
... | no x≢y = ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes x≡y = ⊥-elim (x≢y x≡y)
... | no _ = ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop ⊢N)
... | no x≢y = ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M) = subst ⊢V ⊢L · subst ⊢V ⊢M
subst ⊢V ⊢zero = ⊢zero
subst ⊢V (⊢suc ⊢M) = ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no x≢y = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl = ⊢μ (drop ⊢M)
... | no x≢y = ⊢μ (subst ⊢V (swap x≢y ⊢M))


-- Exercise `subst′`

subst′ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ]′ ⦂ B

subst′-go : ∀ {Γ} → ∀ (x y : Id) → ∀ {N V A B C}
  → ∅ ⊢ V ⦂ B
  → Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
    --------------------------
  → Γ , x ⦂ A ⊢ go x y N V ⦂ C
subst′-go x y ⊢V ⊢N with x ≟ y
... | yes refl = drop ⊢N
... | no x≢y  = subst′ ⊢V (swap x≢y ⊢N)


subst′ {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _ = weaken ⊢V
... | no x≢y = ⊥-elim (x≢y refl)
subst′ {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes x≡y = ⊥-elim (x≢y x≡y)
... | no _ = ⊢` ∋x
subst′ {x = y} ⊢V (⊢ƛ {x = x} ⊢N) = ⊢ƛ (subst′-go x y ⊢V ⊢N)
subst′ ⊢V (⊢L · ⊢M) = subst′ ⊢V ⊢L · subst′ ⊢V ⊢M
subst′ ⊢V ⊢zero = ⊢zero
subst′ {x = y} ⊢V (⊢suc ⊢M) = ⊢suc (subst′ ⊢V ⊢M)
subst′ {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N)
  = ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) (subst′-go x y ⊢V ⊢N)
subst′ {x = y} ⊢V (⊢μ {x = x} ⊢M) = ⊢μ (subst′-go x y ⊢V ⊢M)
