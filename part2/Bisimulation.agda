module part2.Bisimulation where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)

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

data †-able : ∀ {Γ A} → (N : Γ ⊢ A) → Set where

  †-` : ∀ {Γ A} {x : Γ ∋ A}
      ---------
    → †-able (` x)

  †-ƛ_ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → †-able N
      ----------
    → †-able (ƛ N)

  _†-·_ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → †-able L
    → †-able M
      ----------
    → †-able (L · M)

  †-let : ∀ {Γ A B} {M : Γ ⊢ A} {N : Γ , A ⊢ B}
    → †-able M
    → †-able N
      -----------------
    → †-able (`let M N)


_†? : ∀ {Γ A} → (N : Γ ⊢ A) → Dec (†-able N)
(` x) †? = yes †-`
(ƛ N) †? with N †?
... | yes †-N = yes (†-ƛ †-N)
... | no ¬†-N = no λ { (†-ƛ †-N) → ¬†-N †-N }
(L · M) †? with L †? | M †?
... | yes †-L | yes †-M = yes (†-L †-· †-M)
... | yes _ | no ¬†-M = no λ { (_ †-· †-M) → ¬†-M †-M }
... | no ¬†-L | _ = no λ { (†-L †-· _) → ¬†-L †-L }
`zero †? = no (λ ())
(`suc N) †? = no (λ ())
case L M N †? = no (λ ())
(μ N) †? = no (λ ())
con x †? = no (λ ())
(M `* N) †? = no (λ ())
`let M N †? with M †? | N †?
... | yes †-M | yes †-N = yes (†-let †-M †-N)
... | yes _ | no ¬†-N = no λ { (†-let _ †-N) → ¬†-N †-N }
... | no ¬†-M | _ = no λ { (†-let †-M _) → ¬†-M †-M }
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
... | †-ƛ †-N = ƛ (_† N {fromWitness †-N})
_† (L · M) {L·M†?} with toWitness L·M†?
... | †-L †-· †-M = (_† L {fromWitness †-L}) · (_† M {fromWitness †-M})
_† (`let M N) {letMN†?} with toWitness letMN†?
... | †-let †-M †-N = (ƛ (_† N {fromWitness †-N})) · (_† M {fromWitness †-M})


M†≡N→M~N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
  → (_† M {M†?}) ≡ N
  → M ~ N
M†≡N→M~N (` x) _ {M†?} refl = ~`
M†≡N→M~N (ƛ M) _ {M†?} refl with toWitness M†?
... | †-ƛ _ = ~ƛ M†≡N→M~N M (M †) refl
M†≡N→M~N (L · M) _ {M†?} refl with toWitness M†?
... | _ †-· _ = M†≡N→M~N L (L †) refl ~· M†≡N→M~N M (M †) refl
M†≡N→M~N (`let M N) _ {M†?} refl with toWitness M†?
... | †-let _ _ = ~let (M†≡N→M~N M (M †) refl) (M†≡N→M~N N (N †) refl)

M~N→M†≡N : ∀ {Γ A}
  → (M : Γ ⊢ A)
  → (N : Γ ⊢ A)
  → {M†? : True (M †?)}
  → M ~ N
  → (_† M {M†?}) ≡ N
M~N→M†≡N (` x) _ {M†?} ~` = refl
M~N→M†≡N (ƛ M) (ƛ N†) {M†?} (~ƛ M~M†) with toWitness M†?
... | †-ƛ †-M with M~N→M†≡N M N† {fromWitness †-M} M~M†
... | refl = refl
M~N→M†≡N (L · M) (L† · M†) {M†?} (L~L† ~· M~M†) with toWitness M†?
... | †-L †-· †-M with M~N→M†≡N L L† {fromWitness †-L} L~L† | M~N→M†≡N M M† {fromWitness †-M} M~M†
... | refl | refl = refl
M~N→M†≡N (`let M N) ((ƛ N†) · M†) {M†?} (~let M~M† N~N†) with toWitness M†?
... | †-let †-M †-N with M~N→M†≡N M M† {fromWitness †-M} M~M† | M~N→M†≡N N N† {fromWitness †-N} N~N†
... | refl | refl = refl
