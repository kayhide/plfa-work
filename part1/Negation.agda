module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _≤_; _<_; _>_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import part1.Isomorphism using (_≃_; extensionality; _≲_)
open import part1.Connectives using (⊥-identityˡ)
open _≃_


¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x


¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)


_ : 1 ≢ 2
_ = λ ()

peano : ∀ {n : ℕ} → zero ≢ suc n
peano = λ ()


id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ x → ⊥-elim (¬x′ x)


-- Exercise `<-irreflexive`

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero = λ()
<-irreflexive (suc n) = λ { (s≤s n<n) → <-irreflexive n n<n }


-- Exercise `trichotomy`

≡-suc : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
≡-suc refl = refl

<-suc : ∀ {m n : ℕ} → suc m < suc n → m < n
<-suc (s≤s smsn) = smsn

>-suc : ∀ {m n : ℕ} → suc m > suc n → m > n
>-suc (s≤s smsn) = smsn

trichotomy : ∀ (m n : ℕ)
  → ((m < n) × (¬ m ≡ n) × (¬ m > n)) ⊎ (¬ m < n × m ≡ n × ¬ m > n) ⊎ (¬ m < n × ¬ m ≡ n × m > n)
trichotomy zero zero = inj₂ (inj₁ ((λ ()) , refl , (λ ())))
trichotomy zero (suc n) = inj₁ ((s≤s z≤n) , (λ ()) , (λ ()))
trichotomy (suc m) zero = inj₂ (inj₂ ((λ ()) , (λ ()) , s≤s z≤n))
trichotomy (suc m) (suc n) with trichotomy m n
... | inj₁ (m<n , m≢n , m≯n) = inj₁ (s≤s m<n , (λ sm≡sn → m≢n (≡-suc sm≡sn)) , (λ sm>sn → m≯n (>-suc sm>sn)))
... | inj₂ (inj₁ (m≮n , refl , m≯n)) = inj₂ (inj₁ ((λ sm<sn → m≮n (<-suc sm<sn)) , refl , (λ sm>sn → m≯n (>-suc sm>sn))))
... | inj₂ (inj₂ (m≮n , m≢n , m>n)) = inj₂ (inj₂ ((λ sm<sn → m≮n (<-suc sm<sn)) , (λ sm≡sn → m≢n (≡-suc sm≡sn)) , s≤s m>n))


-- Exercise `⊎-dual-×`


→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ f → f ∘ inj₁ , f ∘ inj₂
    ; from = λ { (g , h) → λ { (inj₁ x) → g x ; (inj₂ x) → h x } }
    ; from∘to = λ f → extensionality λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { (g , h) → refl }
    }

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ ¬ A × ¬ B
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

-- As for the following, it does not hold.
-- ¬ (A × B) ≃ ¬ A ⊎ ¬ B
-- This is because there is no construction of both `A` and `B`,
-- lhs ⇒ rhs is not possible.
-- On the other hand lhs ⇐ rhs holds and the following is the proof.

→-antidistrib-x : ∀ {A B C : Set} → (A → C) ⊎ (B → C) → ((A × B) → C)
→-antidistrib-x (inj₁ A→C) (A , _) = A→C A
→-antidistrib-x (inj₂ B→C) (_ , B) = B→C B

¬A⊎¬B⇒¬A×B : ∀ {A B : Set} → ¬ A ⊎ ¬ B → ¬ (A × B)
¬A⊎¬B⇒¬A×B {A} {B} = →-antidistrib-x {A} {B} {⊥}


--

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ x → k (inj₁ x))


-- Exercise `Classical`

-- em → others
em-dne : ∀ {A : Set} → ¬ ¬ A → A
em-dne {A} ¬¬A with em {A}
... | inj₁ A = A
... | inj₂ ¬A = ⊥-elim (¬¬A ¬A)

em-peirce : ∀ {A B : Set} → ((A → B) → A) → A
em-peirce {A} f with em {A}
... | inj₁ A = A
... | inj₂ ¬A = f (⊥-elim ∘ ¬A)

em-iad : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
em-iad {A} f with em {A}
... | inj₁ A = inj₂ (f A)
... | inj₂ ¬A = inj₁ ¬A

em-demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
em-demorgan {A} {B} with em {A}
...                 | inj₁ A = λ _ → inj₁ A
...                 | inj₂ ¬A with em {B}
...                              | inj₁ B = λ _ → inj₂ B
...                              | inj₂ ¬B = λ f → ⊥-elim (f (¬A , ¬B))

-- dne → em
postulate
  dne : ∀ {A : Set} → ¬ ¬ A → A

dne-em : ∀ {A : Set} → A ⊎ ¬ A
dne-em {A} = dne em-irrefutable

-- peirce → dne
postulate
  peirce : ∀ {A B : Set} → ((A → B) → A) → A

peirce-dne : ∀ {A : Set} → ¬ ¬ A → A
peirce-dne {A} ¬¬A = peirce {A} (⊥-elim ∘ ¬¬A)

-- iad → em
postulate
  iad : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B

iad-em : ∀ {A : Set} → A ⊎ ¬ A
iad-em {A} = swap (iad (λ z → z))

-- demorgan
postulate
  demorgan : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

demorgan-em : ∀ {A : Set} → A ⊎ ¬ A
demorgan-em {A} = demorgan (λ { (¬A , ¬¬A) → ⊥-elim (¬¬A ¬A) })


-- Exercise `Stable`

Stable : Set → Set
Stable A = ¬ ¬ A → A

stable-neg : ∀ {A : Set} → Stable (¬ A)
stable-neg = ¬¬¬-elim


¬¬-distrib-× : ∀ {A B : Set}
  → ¬ ¬ (A × B)
  → ¬ ¬ A × ¬ ¬ B
¬¬-distrib-× k = (λ x → k (λ z → x (proj₁ z))) , λ x → k (λ z → x (proj₂ z))

stable-conj : ∀ {A B : Set}
  → Stable A       -- ¬ ¬ A → A
  → Stable B       -- ¬ ¬ B → B
    --------------
  → Stable (A × B) -- ¬ ¬ (A × B) → (A × B)
stable-conj f g ¬¬AB with ¬¬-distrib-× ¬¬AB
... | ¬¬A , ¬¬B = (f ¬¬A) , (g ¬¬B)

