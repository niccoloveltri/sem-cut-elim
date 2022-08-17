{-# OPTIONS --rewriting #-}

module CutAdmissibility where

open import Function
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utilities
open import SequentCalculus 
open import Model 
open import Interpretation

-- The admissibility of cut follows from the Okada property, which is
-- NbE is called also reflection/reification.
reflect : ∀ A → (⟦ A ⟧ ¹) [ A ]
reify : ∀ {Γ} A → (⟦ A ⟧ ¹) Γ → ⟨ A ⟩ Γ

reflect (` X) = ax
reflect I k = IL {[]} (k refl)
reflect (A ⊗ B) k = ⊗L {[]} (k ([ A ] , [ B ] , refl , reflect A , reflect B))
reflect (A ⊸r B) Δ x = run ⟦ B ⟧ _ (λ k → ⊸rL {[]}{Δ} (reify A x) (k (reflect B)))
reflect (A ⊸l B) Δ x = run ⟦ B ⟧  _ (λ k → ⊸lL {[]}{Δ} (reify A x) (k (reflect B)))

reify (` X) f = f
reify I k = k (λ { refl → IR })
reify (A ⊗ B) k = k λ { (_ , _ , refl , x , y) → ⊗R (reify A x) (reify B y) }
reify (A ⊸r B) k = ⊸rR (reify B (k [ A ] (reflect A)))
reify (A ⊸l B) k = ⊸lR (reify B (k [ A ] (reflect A)))

reflect-cxt : ∀ Γ → ⟦ Γ ⟧-cxt Γ
reflect-cxt [] = refl
reflect-cxt (A ∷ Γ) = [ A ] , Γ , refl , reflect A , reflect-cxt Γ

cmplt : ∀ {Γ A} → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹ → ⟨ A ⟩ Γ
cmplt {Γ}{A} f = reify _ (f Γ (reflect-cxt Γ))

cut : ∀{Δ₀ Γ Δ₁ A C} → Γ ⊢ A → Δ₀ ++ A ∷ Δ₁ ⊢ C
  → Δ₀ ++ Γ ++ Δ₁ ⊢ C
cut {Δ₀}{Γ}{Δ₁}{A}{C} f g =
  cmplt (⟦cut⟧ {Δ₀}{Γ}{Δ₁}{A}{C} (sound f) (sound g))

