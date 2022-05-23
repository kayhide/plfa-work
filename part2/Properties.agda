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


----

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ---------
  → ∅ ⊢ N ⦂ A
preserve (⊢L · ⊢M) (ξ-·₁ L→L′) = preserve ⊢L L→L′ · ⊢M
preserve (⊢L · ⊢M) (ξ-·₂ L M→M′) = ⊢L · preserve ⊢M M→M′
preserve (⊢ƛ ⊢N · ⊢V) (β-ƛ VV) = subst ⊢V ⊢N
preserve (⊢suc ⊢M) (ξ-suc M→M′) = ⊢suc (preserve ⊢M M→M′)
preserve (⊢case ⊢L ⊢M ⊢N) (ξ-case L→L′) = ⊢case (preserve ⊢L L→L′) ⊢M ⊢N
preserve (⊢case ⊢L ⊢M ⊢N) β-zero = ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV) = subst ⊢V ⊢N
preserve (⊢μ ⊢M) β-μ = subst (⊢μ ⊢M) ⊢M


----

record Gas : Set where
  constructor gas
  field
    amount : ℕ


data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N


data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L


eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero) ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL = steps (L ∎) (done VL)
... | step L→M with eval (gas m) (preserve ⊢L L→M)
...   | steps M↠N fin = steps (L —→⟨ L→M ⟩ M↠N) fin


⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` Z))

_ : eval (gas 3) ⊢sucμ ≡
  steps (
    μ "x" ⇒ `suc ` "x"
  —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
  —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
  ∎
  ) out-of-gas
_ = refl


_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
  steps (
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎
  ) (done (V-suc (V-suc V-zero)))
_ = refl


_ : eval (gas 100) ⊢2+2 ≡
  steps
  ((μ "+" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒
    (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
        (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
      · ` "m"
      · ` "n")
    ]))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒
    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · ` "m"
    · ` "n")
    ])
  · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · ` "m"
    · `suc (`suc `zero))
  ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · `suc `zero
    · `suc (`suc `zero))
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  `suc
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
        (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
      · ` "m"
      · ` "n")
      ]))
    · `suc `zero
    · `suc (`suc `zero))
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  `suc
  ((ƛ "n" ⇒
    case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
        (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
      · ` "m"
      · ` "n")
    ])
    · `suc (`suc `zero))
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
  `suc
  case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · ` "m"
    · `suc (`suc `zero))
  ]
  —→⟨ ξ-suc (β-suc V-zero) ⟩
  `suc
  (`suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · `zero
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  `suc
  (`suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
          (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
        · ` "m"
        · ` "n")
      ]))
    · `zero
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
  `suc
  (`suc
    ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
        (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
      · ` "m"
      · ` "n")
      ])
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  `suc
  (`suc
    case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · ` "m"
    · `suc (`suc `zero))
    ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl


_ : eval (gas 100) ⊢2+2ᶜ ≡
  steps
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")))))
  · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
  · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
  · (ƛ "n" ⇒ `suc ` "n")
  · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
  (ƛ "n" ⇒
    (ƛ "s" ⇒
    (ƛ "z" ⇒
      (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
      (` "n" · ` "s" · ` "z"))))
  · (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")))
  · (ƛ "n" ⇒ `suc ` "n")
  · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
  (ƛ "s" ⇒
    (ƛ "z" ⇒
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · ` "s" · ` "z")))
  · (ƛ "n" ⇒ `suc ` "n")
  · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
  (ƛ "z" ⇒
    (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    ·
    ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    · ` "z"))
  · `zero
  —→⟨ β-ƛ V-zero ⟩
  (ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
  ·
  ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
  (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
  ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
    · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
  (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
  ((ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
    `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
  ((ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
  (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
  ((ƛ "n" ⇒ `suc ` "n") · `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
  (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
  `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒ `suc ` "n") · `suc (`suc (`suc `zero)) —→⟨
  β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
  `suc (`suc (`suc (`suc `zero))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl


-- Exercise `mul-eval`

-- By normalizing the lhs, it finishes with the value of four.
-- Because the normalized form is so long, I did not write it down here.
-- To ensure, normalize the lhs with `C-c n`.
-- _ : eval (gas 100) (⊢mul · ⊢two · ⊢two) ≡ steps _ (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- _ = {!!}


-- Exercise `progress-preservation`

-- progress : ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ] M —→ N
-- preservation : ∅ ⊢ M ⦂ A → M —→ N → ∅ ⊢ N ⦂ A


-- Exercise `subject-expansion`


-- Counterexample 1. From β-zero, other term cannot be constructed.
-- β-zero ⊢M => ⊢case ⊢L ⊢M ⊢N?
-- M => case L [zero⇒ M ∣suc x ⇒ N? ]

-- Counterexample 2. When substitution is involeved, it cannot be reversed.
-- (β-ƛ VV) ⊢M => ⊢ƛ ⊢N? · ⊢V
-- N [ x := V ] => (ƛ x ⇒ N?) · V


-- expansion : ∀ {M N A} → M —→ N → ∅ ⊢ N ⦂ A → ∅ ⊢ M ⦂ A
-- expansion (ξ-·₁ L→L′) (⊢L′ · ⊢M) = expansion L→L′ ⊢L′ · ⊢M
-- expansion (ξ-·₂ VL M→M′) (⊢L · ⊢M′) = ⊢L · expansion M→M′ ⊢M′
-- expansion (β-ƛ VV) X = {!!}
-- expansion (ξ-suc M→M′) (⊢suc ⊢M′) = ⊢suc (expansion M→M′ ⊢M′)
-- expansion (ξ-case L→L′) (⊢case ⊢L′ ⊢M ⊢N) = ⊢case (expansion L→L′ ⊢L′) ⊢M ⊢N
-- expansion β-zero ⊢M = {!!}
-- expansion (β-suc ⊢V) X = {!!}
-- expansion β-μ ⊢M = ⊢μ {!!}


