module part2.Bisimulation where

open import Data.Product using (Σ; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import part2.More


infix 4 _~_
infix 5 ~ƛ_
infix 7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
      ---------
    → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ----------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†


-- Exercise `_†`

infix 9 _†?
infix 9 _†


_†? : ∀ {Γ A} → (N : Γ ⊢ A) → Dec (∃[ N† ] N ~ N†)
(` x) †? = yes ⟨ (` x) , ~` ⟩
(ƛ N) †? with N †?
... | yes ⟨ N† , ~N ⟩ = yes ⟨ ƛ N† , ~ƛ ~N ⟩
... | no ∄N† = no λ { ⟨ ƛ N† , ~ƛ ~N ⟩ → ∄N† ⟨ N† , ~N ⟩ }
(L · M) †? with L †? | M †?
... | yes ⟨ L† , ~L ⟩ | yes ⟨ M† , ~M ⟩ = yes ⟨ L† · M† , ~L ~· ~M ⟩
... | yes _ | no ∄M† = no λ { ⟨ _ · M† , _ ~· ~M ⟩ → ∄M† ⟨ M† , ~M ⟩ }
... | no ∄L† | _ = no λ { ⟨ L† · _ , ~L ~· _ ⟩ → ∄L† ⟨ L† , ~L ⟩ }
`zero †? = no (λ ())
(`suc N) †? = no (λ ())
case L M N †? = no (λ ())
(μ N) †? = no (λ ())
con x †? = no (λ ())
(M `* N) †? = no (λ ())
`let M N †? with M †? | N †?
... | yes ⟨ M† , ~M ⟩ | yes ⟨ N† , ~N ⟩ = yes ⟨ (ƛ N†) · M† , ~let ~M ~N ⟩
... | yes _ | no ∄N† = no λ { ⟨ (ƛ N†) · _ , ~let _ ~N ⟩ → ∄N† ⟨ N† , ~N ⟩ }
... | no ∄M† | _ = no λ { ⟨ (ƛ _) · M† , ~let ~M _ ⟩ → ∄M† ⟨ M† , ~M ⟩ }
`⟨ M , N ⟩ †? = no (λ ())
`proj₁ N †? = no (λ ())
`proj₂ N †? = no (λ ())
case× M N †? = no (λ ())
`inj₁ N †? = no (λ ())
`inj₂ N †? = no (λ ())
case⊎ L M N †? = no (λ ())
`tt †? = no (λ ())
case⊤ L M †? = no (λ ())
case⊥ L †? = no (λ ())
`[] †? = no (λ ())
(M `∷ N) †? = no (λ ())
caseL L M N †? = no (λ ())


_† : ∀ {Γ A} → (N : Γ ⊢ A) → {True (N †?)} → Γ ⊢ A
(` x) † = ` x
_† (ƛ N) {N†?} with toWitness N†?
... | ⟨ ƛ N† , ~ƛ ~N ⟩ = ƛ (_† N {fromWitness ⟨ N† , ~N ⟩})
_† (L · M) {L·M†?} with toWitness L·M†?
... | ⟨ L† · M† , ~L ~· ~M ⟩ = (_† L {fromWitness ⟨ L† , ~L ⟩}) · (_† M {fromWitness ⟨ M† , ~M ⟩})
_† (`let M N) {letMN†?} with toWitness letMN†?
... | ⟨ (ƛ N†) · M† , ~let ~M ~N ⟩ = (ƛ (_† N {fromWitness ⟨ N† , ~N ⟩})) · (_† M {fromWitness ⟨ M† , ~M ⟩})


M†≡N→M~N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
    ------------------------
  → (_† M {M†?}) ≡ N → M ~ N
M†≡N→M~N (` M) _ {M†?} refl = ~`
M†≡N→M~N (ƛ M) .((ƛ M) †) {M†?} refl with toWitness M†?
... | ⟨ ƛ _ , ~ƛ _ ⟩ = ~ƛ (M†≡N→M~N M (M †) refl)
M†≡N→M~N (L · M) .((L · M) †) {LM†?} refl with toWitness LM†?
... | ⟨ _ · _ , _ ~· _ ⟩ = M†≡N→M~N L (L †) refl ~· M†≡N→M~N M (M †) refl
M†≡N→M~N (`let M N) .(`let M N †) {MN†?} refl with toWitness MN†?
... | ⟨ (ƛ _) · _ , ~let _ _ ⟩ = ~let (M†≡N→M~N M (M †) refl) (M†≡N→M~N N (N †) refl)


M~N→M†≡N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
    ------------------------
  → M ~ N → (_† M {M†?}) ≡ N
M~N→M†≡N (` x) _ ~` = refl
M~N→M†≡N (ƛ M) (ƛ N†) {M†?} (~ƛ ~N) with toWitness M†?
... | ⟨ ƛ X† , ~ƛ ~X ⟩ with M~N→M†≡N M N† {fromWitness ⟨ X† , ~X ⟩} ~N
... | refl = refl
M~N→M†≡N (L · M) (L† · M†) {LM†?} (~L ~· ~M) with toWitness LM†?
... | ⟨ X† · Y† , ~X ~· ~Y ⟩ with M~N→M†≡N L L† {fromWitness ⟨ X† , ~X ⟩} ~L | M~N→M†≡N M M† {fromWitness ⟨ Y† , ~Y ⟩} ~M
... | refl | refl = refl
M~N→M†≡N (`let M N) ((ƛ N†) · M†) {MN†?} (~let ~M ~N) with toWitness MN†?
... | ⟨ (ƛ Y†) · X† , ~let ~X ~Y ⟩ with M~N→M†≡N M M† {fromWitness ⟨ X† , ~X ⟩} ~M | M~N→M†≡N N N† {fromWitness ⟨ Y† , ~Y ⟩} ~N
... | refl | refl = refl


----

~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val (~ƛ _) V-ƛ = V-ƛ


-- Exercise `~val⁻¹`

~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ (~ƛ _) V-ƛ = V-ƛ


----

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ ~` = ~`
~rename ρ (~ƛ ~N) = ~ƛ ~rename (ext ρ) ~N
~rename ρ (~L ~· ~M) = ~rename ρ ~L ~· ~rename ρ ~M
~rename ρ (~let ~M ~N) = ~let (~rename ρ ~M) (~rename (ext ρ) ~N)


~exts : ∀ {Γ Δ}
  → {σ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A B} (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z = ~`
~exts ~σ (S x) = ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x}) = ~σ x
~subst ~σ (~ƛ ~N) = ~ƛ ~subst (~exts ~σ) ~N
~subst ~σ (~L ~· ~M) = ~subst ~σ ~L ~· ~subst ~σ ~M
~subst ~σ (~let ~M ~N) = ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)


~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst ~σ ~N
  where
    ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
    ~σ Z = ~M
    ~σ (S x) = ~`


----

data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N


sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    --------
  → Leg M† N
sim (~L ~· ~M) (ξ-·₁ L—→) with sim ~L L—→
... | leg ~L′ L†—→ = leg (~L′ ~· ~M) (ξ-·₁ L†—→)
sim (~V ~· ~M) (ξ-·₂ VV M—→) with sim ~M M—→
... | leg ~M′ M†—→ = leg (~V ~· ~M′) (ξ-·₂ (~val ~V  VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV) = leg (~sub ~N ~V) (β-ƛ (~val ~V VV))
sim (~let ~M ~N) (ξ-let M—→) with sim ~M M—→
... | leg ~M′ M†—→ = leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N) (β-let VV) = leg (~sub ~N ~V) (β-ƛ (~val ~V VV))
