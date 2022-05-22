module part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Function using (_∘_; id)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import part1.Isomorphism using (_≲_; _≃_)


Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term


two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ]


twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")


-- Exercise `mul`

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m"
    [zero⇒ `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
    ]


-- Exercise `mulᶜ`

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · (` "n" · ` "s") · ` "z"


-- Exercise `primed`

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ] = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥


plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ n
    |suc m ⇒ `suc (+ · m · n)
    ]
  where
    + = ` "+"
    m = ` "m"
    n = ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ `zero
    |suc m ⇒ plus′ · m · (* · m · n)
    ]
  where
    * = ` "*"
    m = ` "m"
    n = ` "n"


----

data Value : Term → Set where

  V-ƛ : ∀ {x N}
    → Value (ƛ x ⇒ N)

  V-zero :
      Value `zero

  V-suc : ∀ {V}
    → Value V
    → Value (`suc V)


infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no _          = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no _          = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
`zero [ y := V ]    = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no _          = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no _          = μ x ⇒ N [ y := V ]


_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl


-- Exercise `_[_:=_]′`

_[_:=_]′ : Term → Id → Term → Term
go : Id → Id → Term → Term → Term

(` x) [ y := V ]′ with x ≟ y
... | yes _           = V
... | no _            = ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ go x y N V
(L · M) [ y := V ]′   = L [ y := V ]′ · M [ y := V ]′
`zero [ y := V ]′     = `zero
(`suc M) [ y := V ]′  = `suc M [ y := V ]′
case L [zero⇒ M |suc x ⇒ N ] [ y := V ]′
                      = case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ go x y N V ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ go x y N V

go x y N V with x ≟ y
... | yes _ = N
... | no _  = N [ y := V ]′


_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ ƛ "y" ⇒ ` "y"
_ = refl


----

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      -----------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      -----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      -------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ---------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

----

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

_ : twoᶜ · sucᶜ · `zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)


----

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
     ------
   → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin_ M—↠N = M—↠N


data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N


-- Exercise `—↠≲—↠′`

—↠≲—↠′ : ∀ M N → M —↠ N ≲ M —↠′ N
—↠≲—↠′ M N =
  record
    { to = to M N
    ; from = from M N
    ; from∘to = from∘to M N
    }
  where
    to : ∀ (M N : Term) → M —↠ N → M —↠′ N
    to M N (M ∎) = refl′
    to M N (_—→⟨_⟩_ M {X} M→X X↠N) = trans′ (step′ M→X) (to X N X↠N)

    from′ : ∀ {L M N : Term} → L —↠′ M → M —↠ N → L —↠ N
    from′ {L} (step′ L→M) = L —→⟨ L→M ⟩_
    from′ refl′ = id
    from′ (trans′ L↠′M M↠′N) = from′ L↠′M ∘ from′ M↠′N

    from : ∀ (M N : Term) → M —↠′ N → M —↠ N
    from M N MN = from′ MN (N ∎)

    from∘to : ∀ (M N : Term) → (M↠N : M —↠ N) → from M N (to M N M↠N) ≡ M↠N
    from∘to M .M (.M ∎) = refl
    from∘to M N (_—→⟨_⟩_ .M {X} M→X X↠N) rewrite from∘to X N X↠N = refl


-- These are not isomorphic because lhs → rhs is not surjective.

_ : ∀ {M N : Term} {M→N : M —→ N} → _≲_.to (—↠≲—↠′ M N) (M —→⟨ M→N ⟩ N ∎) ≡ (trans′ (step′ M→N) refl′)
_ = refl

_ : ∀ {M N : Term} {M→N : M —→ N} → (M —→⟨ M→N ⟩ N ∎) ≡ _≲_.from (—↠≲—↠′ M N) (trans′ (step′ M→N) refl′)
_ = refl

_ : ∀ {M N : Term} {M→N : M —→ N} → (M —→⟨ M→N ⟩ N ∎) ≡ _≲_.from (—↠≲—↠′ M N) (trans′ refl′ (step′ M→N))
_ = refl


----

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      ----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      ----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N


_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
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

_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus ·  two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒ case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")]) · `suc `zero · two
    )
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc (
      (ƛ "n" ⇒ case (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two
    )
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (
      case (`suc `zero) [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
    )
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · `zero · two
    )
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc (
      (ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]) · two
    )
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (
      case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
    )
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc `suc `suc `suc `zero
  ∎


_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    ( ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")
    ) · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z")
    ) · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")
    ) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")
    ) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    ) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    ) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    ) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    ) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
    ) · `suc `suc `zero
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc `suc `suc `suc `zero
  ∎


-- Exercise `plus-example`

one : Term
one = `suc `zero

_ : plus · one · one —↠ two
_ =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
    ) · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒ case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
    ) · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒ case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
      ) · `zero · one
    )
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc (
      (ƛ "n" ⇒ case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ]
      ) · one
    )
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (
      case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one) ]
    )
  —→⟨ ξ-suc β-zero ⟩
    `suc one
  ∎


----

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type


infixl 5 _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context


-- Exercise `Context-≃`

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (x , id ⦂ ty) = ⟨ id , ty ⟩ ∷ to x

    from : List (Id × Type) → Context
    from [] = ∅
    from (⟨ id , ty ⟩ ∷ ys) = (from ys) , id ⦂ ty

    from∘to : ∀ (x : Context) → from (to x) ≡ x
    from∘to ∅ = refl
    from∘to (c , id ⦂ ty) rewrite from∘to c = refl

    to∘from : ∀ (ys : List (Id × Type)) → to (from ys) ≡ ys
    to∘from [] = refl
    to∘from (⟨ id , ty ⟩ ∷ ys) rewrite to∘from ys = refl


----

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A


_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)

S′ : ∀ {Γ x y A B}
  → {x≢y : False (x ≟ y)}
  → Γ ∋ x ⦂ A
    -----------------
  → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x


infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      ------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A


Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A


⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n) (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+ = S′ (S′ (S′ Z))
  ∋m = S′ Z
  ∋n = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two


⊢plusᶜ : ∀ {Γ A} → Γ ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero


∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z Z = refl
∋-injective Z (S x≢ _) = ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z = ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋y) = ∋-injective ∋x ∋y


nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′)) = contradiction (∋-injective ∋x ∋x′)
  where
    contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
    contradiction ()


----

_ : ∃[ A ] ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A
_ = ⟨ `ℕ , ⊢` ∋y · ⊢` ∋x ⟩
  where
    ∋y = S′ Z
    ∋x = Z

_ : ¬ (∃[ A ] ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A)
_ = λ { ⟨ A , ⊢` ∋x · ⊢` _ ⟩ → contradiction ∋x }
  where
    contradiction : ∀ {Γ A B} → ¬ (Γ , "x" ⦂ `ℕ ∋ "x" ⦂ A ⇒ B)
    contradiction (S x≢ _) = x≢ refl

_ : ∃[ A ] ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A
_ = ⟨ `ℕ ⇒ `ℕ , ⊢ƛ (⊢` ∋y · ⊢` ∋x) ⟩
  where
    ∋y = S′ Z
    ∋x = Z


_ : ∀ {A B} → ¬ (∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B)
_ = λ { (⊢` ∋x · ⊢` ∋x′) → contradiction (∋-injective ∋x ∋x′) }
  where
    contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
    contradiction ()

_ : ∀ (T U V : Type) → ∃[ A ] ∃[ B ] ∃[ C ] ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C
_ = λ T U V → ⟨ U ⇒ V , ⟨ T ⇒ U , ⟨ T ⇒ V , ⊢ƛ (⊢` (S′ (S′ Z)) · (⊢` (S′ Z) · ⊢` Z)) ⟩ ⟩ ⟩


-- Exercise `⊢mul`

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul =
  ⊢μ (⊢ƛ (⊢ƛ (
    ⊢case (⊢` ∋m) ⊢zero (⊢μ (⊢ƛ (⊢ƛ (
      ⊢case (⊢` ∋m′) (⊢` ∋n′) (⊢suc (⊢` ∋+ · ⊢` ∋m′′ · ⊢` ∋n′′))
    ))) · ⊢` ∋n′′′ · (⊢` ∋* · ⊢` ∋m′′′ · ⊢` ∋n′′′′))
  )))
  where
    ∋m = S′ Z
    ∋m′ = S′ Z
    ∋n′ = Z
    ∋+ = S′ (S′ (S′ Z))
    ∋m′′ = Z
    ∋n′′ = S′ Z
    ∋* = S′ (S′ (S′ Z))
    ∋n′′′ = S′ Z
    ∋m′′′ = Z
    ∋n′′′′ = S′ Z


-- Exercise `⊢mulᶜ`

⊢mulᶜ : ∀ {Γ A} → Γ ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · (⊢` ∋n · ⊢` ∋s) · ⊢` ∋z))))
  where
    ∋m = S′ (S′ (S′ Z))
    ∋n = S′ (S′ Z)
    ∋s = S′ Z
    ∋z = Z


----

_ : mulᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
    mulᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ ·  (` "n" · ` "s") · ` "z") · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ ·  (twoᶜ · ` "s") · ` "z") · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ ·  (twoᶜ · sucᶜ) · ` "z") · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · (twoᶜ · sucᶜ) · `zero
  —→⟨ ξ-·₁ (ξ-·₂ V-ƛ (β-ƛ V-ƛ)) ⟩
    twoᶜ · (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · (`suc `suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc `suc `suc `suc `zero
  ∎

-- mulᶜ : Term
-- mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · (` "n" · ` "s") · ` "z"

-- twoᶜ : Term
-- twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")
