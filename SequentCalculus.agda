{-# OPTIONS --rewriting #-}

module SequentCalculus where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utilities

-- We postulate the existence of a type of atomic formulae
postulate At : Set

-- Formulae of Lambek calculus
data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⊸r_ : Fma → Fma → Fma
  _⊸l_ : Fma → Fma → Fma

-- Contexts are lists of formulae
Cxt : Set
Cxt = List Fma

-- Inference rules of Lambek calculus
data _⊢_ : Cxt → Fma → Set where
  ax : ∀ {A} → [ A ] ⊢ A
  ⊸rR : ∀ {Γ A B} → Γ ∷ʳ A ⊢ B → Γ ⊢ A ⊸r B
  ⊸lR : ∀ {Γ A B} → A ∷ Γ ⊢ B → Γ ⊢ A ⊸l B
  IR : [] ⊢ I
  ⊗R : ∀ {Γ Δ A B} → Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A ⊗ B
  ⊸rL : ∀ {Δ₀ Γ Δ₁ A B C} → Γ ⊢ A → Δ₀ ++ B ∷ Δ₁ ⊢ C
    → Δ₀ ++ A ⊸r B ∷ Γ ++ Δ₁ ⊢ C
  ⊸lL : ∀ {Δ₀ Γ Δ₁ A B C} → Γ ⊢ A → Δ₀ ++ B ∷ Δ₁ ⊢ C
    → Δ₀ ++ Γ ++ A ⊸l B ∷ Δ₁ ⊢ C
  IL : ∀ {Δ₀ Δ₁ C} → Δ₀ ++ Δ₁ ⊢ C → Δ₀ ++ I ∷ Δ₁ ⊢ C
  ⊗L : ∀ {Δ₀ Δ₁ A B C} → Δ₀ ++ A ∷ B ∷ Δ₁ ⊢ C → Δ₀ ++ A ⊗ B ∷ Δ₁ ⊢ C

infix 2 _⊢_

-- The inverses of implication-right rules are admissible
⊸rR-inv : ∀ {Γ A B} → Γ ⊢ A ⊸r B → Γ ∷ʳ A ⊢ B
⊸rR-inv ax = ⊸rL {Δ₀ = []} ax ax
⊸rR-inv (⊸rR f) = f
⊸rR-inv (⊸rL {Δ₀} {_} {Δ₁} f g) = ⊸rL f (⊸rR-inv {Δ₀ ++ _ ∷ Δ₁} g)
⊸rR-inv (⊸lL {Δ₀} {_} {Δ₁} f g) = ⊸lL f (⊸rR-inv g)
⊸rR-inv (IL {Δ₀ = Δ₀} {Δ₁} f) = IL (⊸rR-inv {Δ₀ ++ Δ₁} f)
⊸rR-inv (⊗L {Δ₀ = Δ₀} {Δ₁} f) = ⊗L (⊸rR-inv {Δ₀ ++ _ ∷ _ ∷ Δ₁} f)

⊸lR-inv : ∀ {Γ A B} → Γ ⊢ A ⊸l B → A ∷ Γ ⊢ B
⊸lR-inv ax = ⊸lL {[]} ax ax
⊸lR-inv (⊸lR f) = f
⊸lR-inv (⊸rL {Δ₀} f g) = ⊸rL {Δ₀ = _ ∷ Δ₀} f (⊸lR-inv g)
⊸lR-inv (⊸lL {Δ₀} f g) = ⊸lL {Δ₀ = _ ∷ Δ₀} f (⊸lR-inv g)
⊸lR-inv (IL {Δ₀} f) = IL {_ ∷ Δ₀} (⊸lR-inv f)
⊸lR-inv (⊗L {Δ₀} f) = ⊗L {_ ∷ Δ₀} (⊸lR-inv f)

-- Iterated implications:
-- e.g. (A, B, C) ⊸r* D = A ⊸r (B ⊸r (C ⊸r D))
_⊸r*_ : Cxt → Fma → Fma
[] ⊸r* B = B
(A ∷ Γ) ⊸r* B = A ⊸r (Γ ⊸r* B)

_⊸l*_ : Cxt → Fma → Fma
[] ⊸l* B = B
(A ∷ Γ) ⊸l* B = Γ ⊸l* (A ⊸l B)

-- Iterated implication-right rules and their inverses
⊸rR* : ∀ {Γ} Δ {B} → Γ ++ Δ ⊢ B → Γ ⊢ Δ ⊸r* B
⊸rR* [] f = f
⊸rR* (A ∷ Δ) f = ⊸rR (⊸rR* Δ f)

⊸lR* : ∀ Γ {Δ B} → Γ ++ Δ ⊢ B → Δ ⊢ Γ ⊸l* B
⊸lR* [] f = f
⊸lR* (A ∷ Γ) f = ⊸lR* Γ (⊸lR f)

⊸rR-inv* : ∀ {Γ} Δ {B} → Γ ⊢ Δ ⊸r* B → Γ ++ Δ ⊢ B
⊸rR-inv* [] f = f
⊸rR-inv* {Γ} (A ∷ Δ) f = ⊸rR-inv* {Γ ∷ʳ A} Δ (⊸rR-inv f)
⊸lR-inv* : ∀ Γ {Δ B} → Δ ⊢ Γ ⊸l* B → Γ ++ Δ ⊢ B
⊸lR-inv* [] f = f
⊸lR-inv* (A ∷ Γ) f = ⊸lR-inv (⊸lR-inv* Γ f) 

⊸rR-inv*⊸rR* : ∀ {Γ} Δ {B} (f : Γ ++ Δ ⊢ B)
  → ⊸rR-inv* Δ (⊸rR* Δ f) ≡ f
⊸rR-inv*⊸rR* [] f = refl
⊸rR-inv*⊸rR* {Γ} (A ∷ Δ) f = ⊸rR-inv*⊸rR* {Γ ∷ʳ A} Δ f

⊸lR-inv*⊸lR* : ∀ Γ {Δ B} (f : Γ ++ Δ ⊢ B)
  → ⊸lR-inv* Γ {Δ} (⊸lR* Γ f) ≡ f
⊸lR-inv*⊸lR* [] f = refl
⊸lR-inv*⊸lR* (A ∷ Γ) f = cong ⊸lR-inv (⊸lR-inv*⊸lR* Γ (⊸lR f))



