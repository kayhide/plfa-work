module part2.Bisimulation where

open import Data.Product using (Σ; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import part2.More


infix 4 _~_
infix 5 ~ƛ_
infixl 7 _~·_

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

  ~⟨_,_⟩ : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ ⊢ B}
    → M ~ M†
    → N ~ N†
      -------------------------
    → (`⟨ M , N ⟩) ~ (`⟨ M† , N† ⟩)

  ~proj₁ : ∀ {Γ A B} {L L† : Γ ⊢ A `× B}
    → L ~ L†
      --------------------
    → `proj₁ L ~ `proj₁ L†

  ~proj₂ : ∀ {Γ A B} {L L† : Γ ⊢ A `× B}
    → L ~ L†
      --------------------
    → `proj₂ L ~ `proj₂ L†

  ~case× : ∀ {Γ A B C} {L L† : Γ ⊢ A `× B} {M M† : Γ , A , B ⊢ C}
    → L ~ L†
    → M ~ M†
      -------------------------------------------
    → case× L M ~ (ƛ ƛ M†) · `proj₁ L† · `proj₂ L†


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
`⟨ M , N ⟩ †? with M †? | N †?
... | yes ⟨ M† , ~M ⟩ | yes ⟨ N† , ~N ⟩ = yes ⟨ `⟨ M† , N† ⟩ , ~⟨ ~M , ~N ⟩ ⟩
... | yes _ | no ∄N = no λ { ⟨ `⟨ _ , N† ⟩ , ~⟨ _ , ~N ⟩ ⟩ → ∄N ⟨ N† , ~N ⟩ }
... | no ∄M | _ = no λ { ⟨ `⟨ M† , _ ⟩ , ~⟨ ~M , _ ⟩ ⟩ → ∄M ⟨ M† , ~M ⟩ }
`proj₁ L †? with L †?
... | yes ⟨ L† , ~L ⟩ = yes ⟨ `proj₁ L† , ~proj₁ ~L ⟩
... | no ∄L† = no λ { ⟨ `proj₁ L† , ~proj₁ ~L ⟩ → ∄L† ⟨ L† , ~L ⟩ }
`proj₂ L †? with L †?
... | yes ⟨ L† , ~L ⟩ = yes ⟨ `proj₂ L† , ~proj₂ ~L ⟩
... | no ∄L† = no λ { ⟨ `proj₂ L† , ~proj₂ ~L ⟩ → ∄L† ⟨ L† , ~L ⟩ }
case× L M †? with L †? | M †?
... | yes ⟨ L† , ~L ⟩ | yes ⟨ M† , ~M ⟩ = yes ⟨ (ƛ ƛ M†) · `proj₁ L† · `proj₂ L† , ~case× ~L ~M ⟩
... | yes _ | no ∄M = no λ { ⟨ (ƛ ƛ M†) · _ · _ , ~case× _ ~M ⟩ → ∄M ⟨ M† , ~M ⟩ }
... | no ∄L | _ = no λ { ⟨ (ƛ ƛ _) · `proj₁ L† · _ , ~case× ~L _ ⟩ → ∄L ⟨ L† , ~L ⟩ }
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
((ƛ N) †) {N†?} with toWitness N†?
... | ⟨ ƛ N† , ~ƛ ~N ⟩ = ƛ (_† N {fromWitness ⟨ N† , ~N ⟩})
((L · M) †) {L·M†?} with toWitness L·M†?
... | ⟨ L† · M† , ~L ~· ~M ⟩ = (_† L {fromWitness ⟨ L† , ~L ⟩}) · (_† M {fromWitness ⟨ M† , ~M ⟩})
(`let M N †) {letMN†?} with toWitness letMN†?
... | ⟨ (ƛ N†) · M† , ~let ~M ~N ⟩ = (ƛ (_† N {fromWitness ⟨ N† , ~N ⟩})) · (_† M {fromWitness ⟨ M† , ~M ⟩})
(`⟨ M , N ⟩ †) {MN†?} with toWitness MN†?
... | ⟨ `⟨ M† , N† ⟩ , ~⟨ ~M , ~N ⟩ ⟩ = `⟨ _† M {fromWitness ⟨ M† , ~M ⟩} , _† N {fromWitness ⟨ N† , ~N ⟩} ⟩
(`proj₁ L †) {L†?} with toWitness L†?
... | ⟨ `proj₁ L† , ~proj₁ ~L ⟩ = `proj₁ ((L †) {fromWitness ⟨ L† , ~L ⟩})
(`proj₂ L †) {L†?} with toWitness L†?
... | ⟨ `proj₂ L† , ~proj₂ ~L ⟩ = `proj₂ ((L †) {fromWitness ⟨ L† , ~L ⟩})
(case× L M †) {LM†?} with toWitness LM†?
... | ⟨ (ƛ ƛ M†) · `proj₁ L† · `proj₂ L† , ~case× ~L ~M ⟩ =
        (ƛ ƛ ((M †) {fromWitness ⟨ M† , ~M ⟩})) · `proj₁ ((L †) {fromWitness ⟨ L† , ~L ⟩}) · `proj₂ ((L †) {fromWitness ⟨ L† , ~L ⟩})


M†≡N→M~N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
    ------------------------
  → (_† M {M†?}) ≡ N → M ~ N
M†≡N→M~N (` M) _ {M†?} refl = ~`
M†≡N→M~N (ƛ M) .((ƛ M) †) {M†?} refl with toWitness M†?
... | ⟨ ƛ _ , ~ƛ _ ⟩ = ~ƛ M†≡N→M~N M (M †) refl
M†≡N→M~N (L · M) .((L · M) †) {LM†?} refl with toWitness LM†?
... | ⟨ _ · _ , _ ~· _ ⟩ = M†≡N→M~N L (L †) refl ~· M†≡N→M~N M (M †) refl
M†≡N→M~N (`let M N) .(`let M N †) {MN†?} refl with toWitness MN†?
... | ⟨ (ƛ _) · _ , ~let _ _ ⟩ = ~let (M†≡N→M~N M (M †) refl) (M†≡N→M~N N (N †) refl)
M†≡N→M~N `⟨ M , N ⟩ .(`⟨ M , N ⟩ †) {MN†?} refl with toWitness MN†?
... | ⟨ `⟨ _ , _ ⟩ , ~⟨ _ , _ ⟩ ⟩ = ~⟨ M†≡N→M~N M (M †) refl , M†≡N→M~N N (N †) refl ⟩
M†≡N→M~N (`proj₁ L) .(`proj₁ L †) {L†?} refl with toWitness L†?
... | ⟨ `proj₁ _ , ~proj₁ _ ⟩ = ~proj₁ (M†≡N→M~N L (L †) refl)
M†≡N→M~N (`proj₂ L) .(`proj₂ L †) {L†?} refl with toWitness L†?
... | ⟨ `proj₂ _ , ~proj₂ _ ⟩ = ~proj₂ (M†≡N→M~N L (L †) refl)
M†≡N→M~N (case× L M) .(case× L M †) {LM†?} refl with toWitness LM†?
... | ⟨ (ƛ ƛ _) · _ · _ , ~case× _ _ ⟩ = ~case× (M†≡N→M~N L (L †) refl) (M†≡N→M~N M (M †) refl)


M~N→M†≡N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
    ------------------------
  → M ~ N → (_† M {M†?}) ≡ N
M~N→M†≡N (` x) .(` x) {M†?} ~` = refl
M~N→M†≡N (ƛ M) (ƛ M†) {M†?} (~ƛ ~M) with toWitness M†?
... | ⟨ ƛ X† , ~ƛ ~X ⟩ with M~N→M†≡N M M† {fromWitness ⟨ X† , ~X ⟩} ~M
... | refl = refl
M~N→M†≡N (L · M) (L† · M†) {LM†?} (~L ~· ~M) with toWitness LM†?
... | ⟨ X† · Y† , ~X ~· ~Y ⟩ with M~N→M†≡N L L† {fromWitness ⟨ X† , ~X ⟩} ~L | M~N→M†≡N M M† {fromWitness ⟨ Y† , ~Y ⟩} ~M
... | refl | refl = refl
M~N→M†≡N (`let M N) ((ƛ N†) · M†) {MN†?} (~let ~M ~N) with toWitness MN†?
... | ⟨ (ƛ Y†) · X† , ~let ~X ~Y ⟩ with M~N→M†≡N M M† {fromWitness ⟨ X† , ~X ⟩} ~M | M~N→M†≡N N N† {fromWitness ⟨ Y† , ~Y ⟩} ~N
... | refl | refl = refl
M~N→M†≡N `⟨ M , N ⟩ `⟨ M† , N† ⟩ {MN†?} ~⟨ ~M , ~N ⟩ with toWitness MN†?
... | ⟨ `⟨ X† , Y† ⟩ , ~⟨ ~X , ~Y ⟩ ⟩ with M~N→M†≡N M M† {fromWitness ⟨ X† , ~X ⟩} ~M | M~N→M†≡N N N† {fromWitness ⟨ Y† , ~Y ⟩} ~N
... | refl | refl = refl
M~N→M†≡N (`proj₁ L) (`proj₁ L†) {L†?} (~proj₁ ~L) with toWitness L†?
... | ⟨ `proj₁ X† , ~proj₁ ~X ⟩ with M~N→M†≡N L L† {fromWitness ⟨ X† , ~X ⟩} ~L
... | refl = refl
M~N→M†≡N (`proj₂ L) (`proj₂ L†) {L†?} (~proj₂ ~L) with toWitness L†?
... | ⟨ `proj₂ X† , ~proj₂ ~X ⟩ with M~N→M†≡N L L† {fromWitness ⟨ X† , ~X ⟩} ~L
... | refl = refl
M~N→M†≡N (case× L M) ((ƛ ƛ M†) · `proj₁ L† · `proj₂ L†) {LM†?} (~case× ~L ~M) with toWitness LM†?
... | ⟨ ((ƛ ƛ Y†) · `proj₁ X†  · _) , ~case× ~X ~Y ⟩
        with M~N→M†≡N L L† {fromWitness ⟨ X† , ~X ⟩} ~L | M~N→M†≡N M M† {fromWitness ⟨ Y† , ~Y ⟩} ~M
... | refl | refl = refl


----

~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val (~ƛ _) V-ƛ = V-ƛ
~val ~⟨ ~M , ~N ⟩ V-⟨ VM , VN ⟩ = V-⟨ ~val ~M VM , ~val ~N VN ⟩

-- Exercise `~val⁻¹`

~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ (~ƛ _) V-ƛ = V-ƛ
~val⁻¹ ~⟨ ~M , ~N ⟩ V-⟨ VM , VN ⟩ = V-⟨ ~val⁻¹ ~M VM , ~val⁻¹ ~N VN ⟩


----

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ ~` = ~`
~rename ρ (~ƛ ~N) = ~ƛ ~rename (ext ρ) ~N
~rename ρ (~L ~· ~M) = ~rename ρ ~L ~· ~rename ρ ~M
~rename ρ (~let ~M ~N) = ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
~rename ρ ~⟨ ~M , ~N ⟩ = ~⟨ ~rename ρ ~M , ~rename ρ ~N ⟩
~rename ρ (~proj₁ ~L) = ~proj₁ (~rename ρ ~L)
~rename ρ (~proj₂ ~L) = ~proj₂ (~rename ρ ~L)
~rename ρ (~case× ~L ~M) = ~case× (~rename ρ ~L) (~rename (ext (ext ρ)) ~M)


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
~subst ~σ ~⟨ ~M , ~N ⟩ = ~⟨ ~subst ~σ ~M , ~subst ~σ ~N ⟩
~subst ~σ (~proj₁ ~L) = ~proj₁ (~subst ~σ ~L)
~subst ~σ (~proj₂ ~L) = ~proj₂ (~subst ~σ ~L)
~subst ~σ (~case× ~L ~M) = ~case× (~subst ~σ ~L) (~subst (~exts (~exts ~σ)) ~M)


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
sim ~⟨ ~M , ~N ⟩ (ξ-⟨,⟩₁ M—→) with sim ~M M—→
... | leg ~M′ M†—→ = leg ~⟨ ~M′ , ~N ⟩ (ξ-⟨,⟩₁ M†—→)
sim ~⟨ ~V , ~N ⟩ (ξ-⟨,⟩₂ VV N—→) with sim ~N N—→
... | leg ~N′ N†—→ = leg ~⟨ ~V , ~N′ ⟩ (ξ-⟨,⟩₂ (~val ~V VV) N†—→)
sim (~proj₁ ~L) (ξ-proj₁ L—→) with sim ~L L—→
... | leg ~L′ L†—→ = leg (~proj₁ ~L′) (ξ-proj₁ L†—→)
sim (~proj₁ ~⟨ ~VV , ~VW ⟩) (β-proj₁ VV VW) = leg ~VV (β-proj₁ (~val ~VV VV) (~val ~VW VW))
sim (~proj₂ ~L) (ξ-proj₂ L—→) with sim ~L L—→
... | leg ~L′ L†—→ = leg (~proj₂ ~L′) (ξ-proj₂ L†—→)
sim (~proj₂ ~⟨ ~VV , ~VW ⟩) (β-proj₂ VV VW) = leg ~VW (β-proj₂ (~val ~VV VV) (~val ~VW VW))
sim (~case× ~L ~M) (ξ-case× L—→) with sim ~L L—→
... | leg ~L′ L†—→ = leg (~case× ~L′ ~M) {!!}
sim (~case× ~⟨ ~VV , ~VW ⟩ ~M) (β-case× VV VW) = leg ? ?


-- -- Exercise `sim⁻¹`

-- data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where

--   leg⁻¹ : ∀ {N : Γ ⊢ A}
--     → N ~ N†
--     → M —→ N
--       --------
--     → Leg⁻¹ M N†

-- sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
--   → M ~ M†
--   → M† —→ N†
--     --------
--   → Leg⁻¹ M N†
-- sim⁻¹ (~L ~· ~M) (ξ-·₁ L†—→) with sim⁻¹ ~L L†—→
-- ... | leg⁻¹ ~L′ L—→ = leg⁻¹ (~L′ ~· ~M) (ξ-·₁ L—→)
-- sim⁻¹ (~V ~· ~M) (ξ-·₂ VV† M†—→) with sim⁻¹ ~M M†—→
-- ... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~V ~· ~M′) (ξ-·₂ (~val⁻¹ ~V VV†) M—→)
-- sim⁻¹ ((~ƛ ~N) ~· ~V) (β-ƛ VV†) = leg⁻¹ (~sub ~N ~V) (β-ƛ (~val⁻¹ ~V VV†))
-- sim⁻¹ (~let ~M ~N) (ξ-·₂ V-ƛ M†—→) with sim⁻¹ ~M M†—→
-- ... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~let ~M′ ~N) (ξ-let M—→)
-- sim⁻¹ (~let ~V ~N) (β-ƛ VV†) = leg⁻¹ (~sub ~N ~V) (β-let (~val⁻¹ ~V VV†))
