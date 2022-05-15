module part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; +-∸-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import part1.Isomorphism using (_≃_; _⇔_; extensionality)
open import part1.Induction using (*-distrib-+; *-comm)


data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_


_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []


infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ (3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎


++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)


length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)


reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]


-- Exercise `reverse-++-distrib`

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite reverse-++-distrib xs ys | ++-assoc (reverse ys) (reverse xs) [ x ] = refl


-- Exercise `reverse-involutive`

reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] = cong (x ∷_) (reverse-involutive xs)


----

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys rewrite shunt-reverse xs (x ∷ ys) | ++-assoc (reverse xs) [ x ] ys = refl

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []


reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎


----

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl


sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ = refl


-- Exercise `map-compose`

map-compose′ : ∀ {A B C : Set}
  → (f : A → B)
  → (g : B → C)
  → (xs : List A)
    ---------------------------
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose′ f g [] = refl
map-compose′ f g (x ∷ xs) rewrite map-compose′ f g xs = refl


map-compose : ∀ {A B C : Set}
  → (f : A → B)
  → (g : B → C)
    ---------------------------
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (map-compose′ f g)


-- Exercise `map-++-distribute`

map-++-distrib : ∀ {A B : Set}
  → (f : A → B)
  → (xs : List A)
  → (ys : List A)
    ---------------------------------------
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distrib f [] ys = refl
map-++-distrib f (x ∷ xs) ys rewrite map-++-distrib f xs ys = refl


-- Exercise `map-Tree`

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node ls x rs) = node (map-Tree f g ls) (g x) (map-Tree f g rs)


----

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl


sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ = refl


-- Exercise `product`

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl


-- Exercise `foldr-++`

foldr-++ : ∀ {A B : Set}
  → (_⊗_ : A → B → B)
  → (e : B)
  → (xs : List A)
  → (ys : List A)
    ------------------------------------------------------
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl


-- Exercise `foldr-∷`

foldr-∷-[] : ∀ {A : Set}
  → (xs : List A)
    --------------------
  → foldr _∷_ [] xs ≡ xs
foldr-∷-[] [] = refl
foldr-∷-[] (x ∷ xs) rewrite foldr-∷-[] xs = refl


foldr-∷ : ∀ {A : Set}
  → (xs : List A)
  → (ys : List A)
    --------------------
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷ xs ys with foldr-++ _∷_ [] xs ys
... | p rewrite foldr-∷-[] (xs ++ ys) | foldr-∷-[] ys = p


-- Exercise `map-is-foldr`

map-is-foldr′ : ∀ {A B : Set}
  → (f : A → B)
  → (xs : List A)
  → map f xs ≡ foldr (λ y ys → f y ∷ ys) [] xs
map-is-foldr′ f [] = refl
map-is-foldr′ f (x ∷ xs) rewrite map-is-foldr′ f xs = refl

map-is-foldr : ∀ {A B : Set}
  → (f : A → B)
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr′ f)


-- Exercise `fold-Tree`

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node ls y rs) = g (fold-Tree f g ls) y (fold-Tree f g rs)


-- Exercise `map-is-fold-Tree`

map-is-fold-Tree′ : ∀ {A B C D : Set}
  → (f : A → C)
  → (g : B → D)
  → (xs : Tree A B)
    --------------------------------------------------------------
  → map-Tree f g xs ≡ fold-Tree (leaf ∘ f) (λ l y r → node l (g y) r) xs
map-is-fold-Tree′ f g (leaf x) = refl
map-is-fold-Tree′ f g (node ls y rs)
  rewrite map-is-fold-Tree′ f g ls
        | map-is-fold-Tree′ f g rs = refl

map-is-fold-Tree : ∀ {A B C D : Set}
  → (f : A → C)
  → (g : B → D)
    --------------------------------------------------------------
  → map-Tree f g ≡ fold-Tree (leaf ∘ f) (λ ls y rs → node ls (g y) rs)
map-is-fold-Tree f g = extensionality (map-is-fold-Tree′ f g)


-- Exercise `sum-downFrom`

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl


*-distribˡ-+ : ∀ (n p q : ℕ) → n * (p + q) ≡ n * p + n * q
*-distribˡ-+ n p q rewrite *-comm n (p + q) | *-comm n p | *-comm n q = *-distrib-+ p q n

*2-+ : ∀ (n : ℕ) → n * 2 ≡ n + n
*2-+ n rewrite *-comm n 2 | +-identityʳ n = refl

n+n*n∸1 : ∀ (n : ℕ) → n + n * (n ∸ 1) ≡ n * n
n+n*n∸1 zero = refl
n+n*n∸1 (suc n) rewrite *-distribˡ-+ n 1 n | *-identityʳ n = refl

sum-downFrom : (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) =
  begin
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong ((n * 2) +_) (sum-downFrom n) ⟩
    n * 2 + n * (n ∸ 1)
  ≡⟨ cong (_+ (n * (n ∸ 1))) (*2-+ n) ⟩
    n + n + n * (n ∸ 1)
  ≡⟨ +-assoc n n (n * (n ∸ 1)) ⟩
    n + (n + n * (n ∸ 1))
  ≡⟨ cong (n +_) (n+n*n∸1 n) ⟩
    n + n * n
  ∎


----

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }


foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A)
  → (y : A)
  → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    e ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ y xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e ⊗-monoid xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎


-- Exercise `foldl`

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs


-- Exercise `foldr-monoid-foldl`

foldl-monoid-e : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → (x : A)
  → (xs : List A)
  → foldl _⊗_ x xs ≡ x ⊗ foldl _⊗_ e xs
foldl-monoid-e _⊗_ e ⊗-monoid x [] rewrite identityʳ ⊗-monoid x = refl
foldl-monoid-e _⊗_ e ⊗-monoid x (y ∷ ys)
  rewrite foldl-monoid-e _⊗_ e ⊗-monoid (x ⊗ y) ys
        | identityˡ ⊗-monoid y
        | foldl-monoid-e _⊗_ e ⊗-monoid y ys
        | assoc ⊗-monoid x y (foldl _⊗_ e ys)
        = refl

foldr-monoid-foldl′ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → (xs : List A)
  → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl′ _⊗_ e ⊗-monoid [] = refl
foldr-monoid-foldl′ _⊗_ e ⊗-monoid (x ∷ xs)
  rewrite foldr-monoid-foldl′ _⊗_ e ⊗-monoid xs
        | identityˡ ⊗-monoid x
        | foldl-monoid-e _⊗_ e ⊗-monoid x xs
        = refl

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (foldr-monoid-foldl′ _⊗_ e ⊗-monoid)


----
