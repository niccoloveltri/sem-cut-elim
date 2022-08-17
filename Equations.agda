{-# OPTIONS --rewriting #-}

module Equations where

open import Function
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utilities
open import SequentCalculus 
open import Model 
open import Interpretation 

-- I started proving some equations satisfied by the semantic cut
-- operation, which I called ⟦cut⟧

-- Multicategory laws


--   ------- ax          
--    A ⊢ A          Δ₀, A, Δ₁ ⊢ C    
--   ---------------------------------- cut
--           Δ₀, A, Δ₁ ⊢ C
--
-- is equal to    Δ₀, A, Δ₁ ⊢ C

cut-lu : ∀ {Δ₀ Δ₁ A C}
  → (f : ⟦ Δ₀ ++ A ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {[ A ]} {Δ₁} {A} {C} (⟦ax⟧ {A}) f ≡ f
cut-lu {Δ₀} {Δ₁} {A} {C} f = funext (λ Λ → funext (lem Λ))
  where
    lem : ∀ Λ (γ : ⟦ Δ₀ ++ A ∷ Δ₁ ⟧-cxt Λ)
      → ⟦cut⟧ {Δ₀} {[ A ]} {Δ₁} {A} {C} (⟦ax⟧ {A}) f Λ γ ≡ f Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (A ∷ Δ₁) γ
    ... | (Λ₀ , Λ , refl , γ₀ , (Ω , Λ₁ , refl , x , γ₁) , refl) = refl

--                ------- ax
--    Γ ⊢ A        A ⊢ A    
--   ------------------------- cut
--            Γ ⊢ A
--
-- is equal to    Γ ⊢ A

cut-ru : ∀ {Γ A}
  → (f : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → ⟦cut⟧ {[]} {Γ} {[]} {A} {A} f (⟦ax⟧ {A}) ≡ f
cut-ru {Γ} {A} f = funext (λ Λ → funext (lem Λ))
  where
    lem : ∀ Λ γ
      → ⟦cut⟧ {[]} {Γ} {[]} {A} {A} f (⟦ax⟧ {A}) Λ γ ≡ f Λ γ
    lem Λ γ
      rewrite sym (⟦++⟧ru Γ γ) | ⟦++⟧-is-⟦++⟧ Γ [] γ refl | ⟦++⟧ru Γ γ = refl

--                    Ξ₀, A, Ξ₁ ⊢ B      Δ₀, B, Δ₁ ⊢ C
--                   ---------------------------------- cut
--      Γ ⊢ A             Δ₀, Ξ₀, A, Ξ₁, Δ₁ ⊢ C
--   ------------------------------------------------- cut
--              Δ₀, Ξ₀, Γ, Ξ₁, Δ₁ ⊢ C
--
-- is equal to
--
--    Γ ⊢ A       Ξ₀, A, Ξ₁ ⊢ B      
--  ------------------------------ cut
--        Ξ₀, Γ, Ξ₁ ⊢ B                      Δ₀, B, Δ₁ ⊢ C
--   ----------------------------------------------------- cut
--              Δ₀, Ξ₀, Γ, Ξ₁, Δ₁ ⊢ C

cut-ass : ∀ {Δ₀ Ξ₀ Γ Ξ₁ Δ₁ A B C}
  → (f : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (g : ⟦ Ξ₀ ++ A ∷ Ξ₁ ⟧-cxt ⇒ ⟦ B ⟧ ¹)
  → (h : ⟦ Δ₀ ++ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Ξ₀ ++ Γ ++ Ξ₁} {Δ₁} {B} {C} (⟦cut⟧ {Ξ₀} {Γ} {Ξ₁} {A} {B} f g) h
      ≡ ⟦cut⟧ {Δ₀ ++ Ξ₀} {Γ} {Ξ₁ ++ Δ₁} {A} {C} f (⟦cut⟧ {Δ₀} {Ξ₀ ++ A ∷ Ξ₁} {Δ₁} {B} {C} g h)
cut-ass {Δ₀}{Ξ₀}{Γ}{Ξ₁}{Δ₁}{A}{B}{C} f g h = funext (λ Λ → funext (lem Λ))
  where
    lem : ∀ Λ γ
      → ⟦cut⟧ {Δ₀} {Ξ₀ ++ Γ ++ Ξ₁} {Δ₁} {B} {C} (⟦cut⟧ {Ξ₀} {Γ} {Ξ₁} {A} {B} f g) h Λ γ
              ≡ ⟦cut⟧ {Δ₀ ++ Ξ₀} {Γ} {Ξ₁ ++ Δ₁} {A} {C} f (⟦cut⟧ {Δ₀} {Ξ₀ ++ A ∷ Ξ₁} {Δ₁} {B} {C} g h) Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (Ξ₀ ++ Γ ++ Ξ₁ ++ Δ₁) γ
    ... | (Λ₀ , Λ , refl , δ₀ , γ , refl) with is-⟦++⟧ Ξ₀ (Γ ++ Ξ₁ ++ Δ₁) γ
    ... | (Ω₀ , Λ , refl , ω₀ , γ , refl) with is-⟦++⟧ Γ (Ξ₁ ++ Δ₁) γ
    ... | (Λ' , Λ , refl , γ' , γ , refl) with is-⟦++⟧ Ξ₁ Δ₁ γ
    ... | (Ω₁ , Λ₁ , refl , ω₁ , δ₁ , refl)
      rewrite
        sym (⟦++⟧ass Γ Ξ₁ Δ₁ γ' ω₁ δ₁) |
        sym (⟦++⟧ass  Ξ₀ (Γ ++ Ξ₁) Δ₁ ω₀ (⟦++⟧ Γ Ξ₁ γ' ω₁) δ₁) |
        ⟦++⟧-is-⟦++⟧ (Ξ₀ ++ Γ ++ Ξ₁) Δ₁ (⟦++⟧ Ξ₀ (Γ ++ Ξ₁) ω₀ (⟦++⟧ Γ Ξ₁ γ' ω₁)) δ₁ |
        ⟦++⟧-is-⟦++⟧ Ξ₀ (Γ ++ Ξ₁) ω₀ (⟦++⟧ Γ Ξ₁ γ' ω₁) |
        ⟦++⟧-is-⟦++⟧ Γ Ξ₁ γ' ω₁ |
        ⟦++⟧ass Ξ₀ (Γ ++ Ξ₁) Δ₁ ω₀  (⟦++⟧ Γ Ξ₁ γ' ω₁) δ₁ |
        sym (⟦++⟧ass Δ₀ Ξ₀ (Γ ++ Ξ₁ ++ Δ₁) δ₀ ω₀ (⟦++⟧ (Γ ++ Ξ₁) Δ₁ (⟦++⟧ Γ Ξ₁ γ' ω₁) δ₁)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ Ξ₀) (Γ ++ Ξ₁ ++ Δ₁) (⟦++⟧ Δ₀ Ξ₀ δ₀ ω₀) (⟦++⟧ (Γ ++ Ξ₁) Δ₁ (⟦++⟧ Γ Ξ₁ γ' ω₁) δ₁) |
        ⟦++⟧ass Γ Ξ₁ Δ₁ γ' ω₁ δ₁ |
        ⟦++⟧-is-⟦++⟧ Γ (Ξ₁ ++ Δ₁) γ' (⟦++⟧ Ξ₁ Δ₁ ω₁ δ₁) |
        ⟦++⟧ass Δ₀ Ξ₀ (A ∷ Ξ₁ ++ Δ₁) δ₀ ω₀ (Λ' , Ω₁ ++ Λ₁ , refl , f Λ' γ' , ⟦++⟧ Ξ₁ Δ₁ ω₁ δ₁) |
        ⟦++⟧-is-⟦++⟧ Δ₀ (Ξ₀ ++ A ∷ Ξ₁ ++ Δ₁) δ₀ (⟦++⟧ Ξ₀ (A ∷ Ξ₁ ++ Δ₁) ω₀ (Λ' , Ω₁ ++ Λ₁ , refl , f Λ' γ' , ⟦++⟧ Ξ₁ Δ₁ ω₁ δ₁)) |
        sym (⟦++⟧ass Ξ₀ (A ∷ Ξ₁) Δ₁ ω₀ (Λ' , Ω₁ , refl , f Λ' γ' , ω₁) δ₁) |
        ⟦++⟧-is-⟦++⟧ (Ξ₀ ++ A ∷ Ξ₁) Δ₁ (⟦++⟧ Ξ₀ (A ∷ Ξ₁) ω₀ (Λ' , Ω₁ , refl , f Λ' γ' , ω₁)) δ₁ = refl 

--                     Γ₁ ⊢ A₁          Δ₀, A₀, Δ₁, A₁, Δ₂ ⊢ C
--                   ------------------------------------------- cut
--      Γ₀ ⊢ A₀             Δ₀, A₀, Δ₁, Γ₁, Δ₂ ⊢ C
--   ------------------------------------------------- cut
--              Δ₀, Γ₀, Δ₁, Γ₁, Δ₂ ⊢ C
--
-- is equal to
--
--                     Γ₀ ⊢ A₀          Δ₀, A₀, Δ₁, A₁, Δ₂ ⊢ C
--                   ------------------------------------------- cut
--      Γ₁ ⊢ A₁             Δ₀, Γ₀, Δ₁, A₁, Δ₂ ⊢ C
--   ------------------------------------------------- cut
--              Δ₀, Γ₀, Δ₁, Γ₁, Δ₂ ⊢ C


cut-par : ∀ {Δ₀ Γ₀ Δ₁ Γ₁ Δ₂ A₀ A₁ C}
  → (f₀ : ⟦ Γ₀ ⟧-cxt ⇒ ⟦ A₀ ⟧ ¹)
  → (f₁ : ⟦ Γ₁ ⟧-cxt ⇒ ⟦ A₁ ⟧ ¹)
  → (h : ⟦ Δ₀ ++ A₀ ∷ Δ₁ ++ A₁ ∷ Δ₂ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Γ₀} {Δ₁ ++ Γ₁ ++ Δ₂} {A₀} {C} f₀ (⟦cut⟧ {Δ₀ ++ A₀ ∷ Δ₁} {Γ₁} {Δ₂} {A₁} {C} f₁ h)
       ≡ ⟦cut⟧ {Δ₀ ++ Γ₀ ++ Δ₁} {Γ₁} {Δ₂} {A₁} {C} f₁ (⟦cut⟧ {Δ₀} {Γ₀} {Δ₁ ++ A₁ ∷ Δ₂} {A₀} {C} f₀ h)
cut-par {Δ₀}{Γ₀}{Δ₁}{Γ₁}{Δ₂}{A₀}{A₁}{C} f₀ f₁ h = funext (λ Λ → funext (lem Λ))
  where
    lem : ∀ Λ γ
      → ⟦cut⟧ {Δ₀} {Γ₀} {Δ₁ ++ Γ₁ ++ Δ₂} {A₀} {C} f₀ (⟦cut⟧ {Δ₀ ++ A₀ ∷ Δ₁} {Γ₁} {Δ₂} {A₁} {C} f₁ h) Λ γ
              ≡ ⟦cut⟧ {Δ₀ ++ Γ₀ ++ Δ₁} {Γ₁} {Δ₂} {A₁} {C} f₁ (⟦cut⟧ {Δ₀} {Γ₀} {Δ₁ ++ A₁ ∷ Δ₂} {A₀} {C} f₀ h) Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (Γ₀ ++ Δ₁ ++ Γ₁ ++ Δ₂) γ
    ... | (Λ₀ , Λ , refl , δ₀ , γ , refl) with is-⟦++⟧ Γ₀ (Δ₁ ++ Γ₁ ++ Δ₂) γ
    ... | (Ω₀ , Λ , refl , ω₀ , γ , refl) with is-⟦++⟧ Δ₁ (Γ₁ ++ Δ₂) γ
    ... | (Λ₁ , Λ , refl , δ₁ , γ , refl) with is-⟦++⟧ Γ₁ Δ₂ γ
    ... | (Ω₁ , Λ₂ , refl , ω₁ , δ₂ , refl)
      rewrite
        sym (⟦++⟧ass Δ₀ (A₀ ∷ Δ₁) (Γ₁ ++ Δ₂) δ₀ (Ω₀ , Λ₁ , refl , f₀ Ω₀ ω₀ , δ₁) (⟦++⟧ Γ₁ Δ₂ ω₁ δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ A₀ ∷ Δ₁) (Γ₁ ++ Δ₂) (⟦++⟧ Δ₀ (A₀ ∷ Δ₁) δ₀ (Ω₀ , Λ₁ , refl , f₀ Ω₀ ω₀ , δ₁)) (⟦++⟧ Γ₁ Δ₂ ω₁ δ₂) |
        ⟦++⟧-is-⟦++⟧ Γ₁ Δ₂ ω₁ δ₂ |
        sym (⟦++⟧ass Γ₀ Δ₁ (Γ₁ ++ Δ₂) ω₀ δ₁ (⟦++⟧ Γ₁ Δ₂ ω₁ δ₂)) |
        sym (⟦++⟧ass Δ₀ (Γ₀ ++ Δ₁) (Γ₁ ++ Δ₂) δ₀ (⟦++⟧ Γ₀ Δ₁ ω₀ δ₁) (⟦++⟧ Γ₁ Δ₂ ω₁ δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ Γ₀ ++ Δ₁) (Γ₁ ++ Δ₂) (⟦++⟧ Δ₀ (Γ₀ ++ Δ₁) δ₀ (⟦++⟧ Γ₀ Δ₁ ω₀ δ₁)) (⟦++⟧ Γ₁ Δ₂ ω₁ δ₂) |
        ⟦++⟧-is-⟦++⟧ Γ₁ Δ₂ ω₁ δ₂ |
        ⟦++⟧ass Δ₀ (Γ₀ ++ Δ₁) (A₁ ∷ Δ₂) δ₀ (⟦++⟧ Γ₀ Δ₁ ω₀ δ₁) (Ω₁ , Λ₂ , refl , f₁ Ω₁ ω₁ , δ₂) |
        ⟦++⟧-is-⟦++⟧ Δ₀ (Γ₀ ++ Δ₁ ++ A₁ ∷ Δ₂) δ₀ (⟦++⟧ (Γ₀ ++ Δ₁) (A₁ ∷ Δ₂) (⟦++⟧ Γ₀ Δ₁ ω₀ δ₁) (Ω₁ , Λ₂ , refl , f₁ Ω₁ ω₁ , δ₂)) |
        ⟦++⟧ass Γ₀ Δ₁ (A₁ ∷ Δ₂) ω₀ δ₁ (Ω₁ , Λ₂ , refl , f₁ Ω₁ ω₁ , δ₂) |
        ⟦++⟧-is-⟦++⟧ Γ₀ (Δ₁ ++ A₁ ∷ Δ₂) ω₀ (⟦++⟧ Δ₁ (A₁ ∷ Δ₂) δ₁ (Ω₁ , Λ₂ , refl , f₁ Ω₁ ω₁ , δ₂)) =
          cong (h (Λ₀ ++ Ω₀ ++ Λ₁ ++ Ω₁ ++ Λ₂)) (⟦++⟧ass Δ₀ (A₀ ∷ Δ₁) (A₁ ∷ Δ₂) δ₀ (Ω₀ , Λ₁ , refl , f₀ Ω₀ ω₀ , δ₁) (Ω₁ , Λ₂ , refl , f₁ Ω₁ ω₁ , δ₂))

-- ==========================================================

--              Δ₀, A, Δ₁, Δ₂ ⊢ C
--             --------------------- IL
--    Γ ⊢ A     Δ₀, A, Δ₁, I , Δ₂ ⊢ C    
--   ---------------------------------- cut
--          Δ₀, Γ, Δ₁, I, Δ₂ ⊢ C
--
-- is equal to
--
--    Γ ⊢ A     Δ₀, A, Δ₁, Δ₂ ⊢ C    
--   ------------------------------- cut 
--          Δ₀, Γ, Δ₁, Δ₂ ⊢ C
--       ------------------------- IL
--         Δ₀, Γ, Δ₁, I, Δ₂ ⊢ C

comm-cutIL1 : ∀{Δ₀ Γ Δ₁ Δ₂ A C}
  → (f : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (g : ⟦ Δ₀ ++ A ∷ Δ₁ ++ Δ₂ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ I ∷ Δ₂} {A} {C} f (⟦IL⟧ {Δ₀ ++ A ∷ Δ₁} {Δ₂} {C} g) ≡
          ⟦IL⟧ {Δ₀ ++ Γ ++ Δ₁} {Δ₂} {C} (⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ Δ₂} {A} {C} f g)
comm-cutIL1 {Δ₀}{Γ}{Δ₁}{Δ₂}{A}{C} f g = funext (λ Λ → funext (lem Λ))
  where
    lem' : ∀ Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ 
      → (δ₀ : ⟦ Δ₀ ⟧-cxt Λ₀) (ω : ⟦ Γ ⟧-cxt Ω) (δ₁ : ⟦ Δ₁ ⟧-cxt Λ₁) (δ₂ : ⟦ Δ₂ ⟧-cxt Λ₂)
      → ⟦++⟧ (Δ₀ ++ A ∷ Δ₁) Δ₂ (⟦++⟧ Δ₀ (A ∷ Δ₁) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁)) δ₂
             ≡ map++R {Δ₀} {Γ ++ Δ₁ ++ Δ₂}{A ∷ Δ₁ ++ Δ₂}
                 (map++L {Γ}{[ A ]}{Δ₁ ++ Δ₂} (λ Γ' x → Γ' , [] , refl , f Γ' x , refl))
                                              (Λ₀ ++ Ω ++ Λ₁ ++ Λ₂)
                                              (⟦++⟧ (Δ₀ ++ Γ ++ Δ₁) Δ₂ (⟦++⟧ Δ₀ (Γ ++ Δ₁) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁))  δ₂)
    lem' Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ δ₀ ω δ₁ δ₂
      rewrite
        ⟦++⟧ass Δ₀ (Γ ++ Δ₁) Δ₂ δ₀ (⟦++⟧ Γ Δ₁ ω δ₁) δ₂ |
        ⟦++⟧-is-⟦++⟧ Δ₀ (Γ ++ Δ₁ ++ Δ₂) δ₀ (⟦++⟧ (Γ ++ Δ₁) Δ₂ (⟦++⟧ Γ Δ₁ ω δ₁) δ₂) |
        ⟦++⟧ass Γ Δ₁ Δ₂ ω δ₁ δ₂ |
        ⟦++⟧-is-⟦++⟧ Γ (Δ₁ ++ Δ₂) ω (⟦++⟧ Δ₁ Δ₂ δ₁ δ₂) = ⟦++⟧ass Δ₀ (A ∷ Δ₁) Δ₂ δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁) δ₂

    lem : ∀ Λ γ → 
      ⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ I ∷ Δ₂} {A} {C} f (⟦IL⟧ {Δ₀ ++ A ∷ Δ₁} {Δ₂} {C} g) Λ γ ≡
          ⟦IL⟧ {Δ₀ ++ Γ ++ Δ₁} {Δ₂} {C} (⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ Δ₂} {A} {C} f g) Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (Γ ++ Δ₁ ++ I ∷ Δ₂) γ
    ... | (Λ₀ , Λ , refl , δ₀ , γ , refl) with is-⟦++⟧ Γ (Δ₁ ++ I ∷ Δ₂) γ
    ... | (Ω , Λ , refl , ω , γ , refl) with is-⟦++⟧ Δ₁ (I ∷ Δ₂) γ
    ... | (Λ₁ , _ , refl , δ₁ , (Ξ , Λ₂ , refl , k , δ₂) , refl)
      rewrite
        sym (⟦++⟧ass Δ₀ (A ∷ Δ₁) (I ∷ Δ₂) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁) (Ξ , Λ₂ , refl , k , δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ A ∷ Δ₁) (I ∷ Δ₂) (⟦++⟧ Δ₀ (A ∷ Δ₁) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁)) (Ξ , Λ₂ , refl , k , δ₂) |
        sym (⟦++⟧ass Γ Δ₁ (I ∷ Δ₂) ω δ₁ (Ξ , Λ₂ , refl , k , δ₂)) |
        sym (⟦++⟧ass Δ₀ (Γ ++ Δ₁) (I ∷ Δ₂) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁) (Ξ , Λ₂ , refl , k , δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ Γ ++ Δ₁) (I ∷ Δ₂) (⟦++⟧ Δ₀ (Γ ++ Δ₁) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁)) (Ξ , Λ₂ , refl , k , δ₂) =
          cong (proj₂ ⟦ C ⟧ (Λ₀ ++ Ω ++ Λ₁ ++ Ξ ++ Λ₂)) (ifunext (λ B → funext (λ h →
            cong (⊸lR-inv* (Λ₀ ++ Ω ++ Λ₁)) (cong (⊸rR-inv* Λ₂) (cong k (ifunext (λ Φ → funext (λ { refl →
              cong (⊸rR* Λ₂) (cong (⊸lR* (Λ₀ ++ Ω ++ Λ₁)) (cong h (cong (g (Λ₀ ++ Ω ++ Λ₁ ++ Λ₂))
                (lem' Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ δ₀ ω δ₁ δ₂)))) }))))))))


--              Δ₀, A, Δ₁, A', B' Δ₂ ⊢ C
--             -------------------------- ⊗L
--    Γ ⊢ A     Δ₀, A, Δ₁, A' ⊗ B', Δ₂ ⊢ C    
--   ---------------------------------------- cut
--          Δ₀, Γ, Δ₁, A' ⊗ B', Δ₂ ⊢ C
--
-- is equal to
--
--    Γ ⊢ A     Δ₀, A, Δ₁, A', B', Δ₂ ⊢ C    
--   ------------------------------- cut 
--          Δ₀, Γ, Δ₁, A', B', Δ₂ ⊢ C
--       ------------------------- IL
--         Δ₀, Γ, Δ₁, A' ⊗ B', Δ₂ ⊢ C

comm-cut⊗L1 : ∀{Δ₀ Γ Δ₁ Δ₂ A A' B' C}
  → (f : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (g : ⟦ Δ₀ ++ A ∷ Δ₁ ++ A' ∷ B' ∷ Δ₂ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ A' ⊗ B' ∷ Δ₂} {A} {C} f (⟦⊗L⟧ {Δ₀ ++ A ∷ Δ₁} {Δ₂} {A'}{B'} {C} g) ≡
          ⟦⊗L⟧ {Δ₀ ++ Γ ++ Δ₁} {Δ₂} {A'}{B'} {C} (⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ A' ∷ B' ∷ Δ₂} {A} {C} f g)
comm-cut⊗L1 {Δ₀}{Γ}{Δ₁}{Δ₂}{A}{A'}{B'}{C} f g = funext (λ Λ → funext (lem Λ))
  where
    lem' : ∀ Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ Φ₀ Φ₁
      → (δ₀ : ⟦ Δ₀ ⟧-cxt Λ₀) (ω : ⟦ Γ ⟧-cxt Ω) (δ₁ : ⟦ Δ₁ ⟧-cxt Λ₁) (δ₂ : ⟦ Δ₂ ⟧-cxt Λ₂)
      → (x : (⟦ A' ⟧ ¹) Φ₀) (y : (⟦ B' ⟧ ¹) Φ₁)
      → ⟦++⟧ (Δ₀ ++ A ∷ Δ₁) (A' ∷ B' ∷ Δ₂) (⟦++⟧ Δ₀ (A ∷ Δ₁) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁)) (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂)
             ≡ map++R {Δ₀} {Γ ++ Δ₁ ++ A' ∷ B' ∷ Δ₂}{A ∷ Δ₁ ++ A' ∷ B' ∷ Δ₂}
                 (map++L {Γ}{[ A ]}{Δ₁ ++ A' ∷ B' ∷ Δ₂} (λ Γ' z → Γ' , [] , refl , f Γ' z , refl))
                                              (Λ₀ ++ Ω ++ Λ₁ ++ Φ₀ ++ Φ₁ ++ Λ₂)
                                              (⟦++⟧ (Δ₀ ++ Γ ++ Δ₁) (A' ∷ B' ∷ Δ₂) (⟦++⟧ Δ₀ (Γ ++ Δ₁) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁)) (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂))
    lem' Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ Φ₀ Φ₁ δ₀ ω δ₁ δ₂ x y 
      rewrite
        ⟦++⟧ass Δ₀ (Γ ++ Δ₁) (A' ∷ B' ∷ Δ₂) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁) (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂) |
        ⟦++⟧-is-⟦++⟧ Δ₀ (Γ ++ Δ₁ ++ A' ∷ B' ∷ Δ₂) δ₀ (⟦++⟧ (Γ ++ Δ₁) (A' ∷ B' ∷ Δ₂) (⟦++⟧ Γ Δ₁ ω δ₁) (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂)) |
        ⟦++⟧ass Γ Δ₁ (A' ∷ B' ∷ Δ₂) ω δ₁ (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂) |
        ⟦++⟧-is-⟦++⟧ Γ (Δ₁ ++ A' ∷ B' ∷ Δ₂) ω (⟦++⟧ Δ₁ (A' ∷ B' ∷ Δ₂) δ₁ (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂)) =
          ⟦++⟧ass Δ₀ (A ∷ Δ₁) (A' ∷ B' ∷ Δ₂) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁) (Φ₀ , Φ₁ ++ Λ₂ , refl , x , Φ₁ , Λ₂ , refl , y , δ₂)
        
    lem : ∀ Λ γ → 
      ⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ A' ⊗ B' ∷ Δ₂} {A} {C} f (⟦⊗L⟧ {Δ₀ ++ A ∷ Δ₁} {Δ₂} {A'}{B'} {C} g) Λ γ ≡
          ⟦⊗L⟧ {Δ₀ ++ Γ ++ Δ₁} {Δ₂} {A'}{B'} {C} (⟦cut⟧ {Δ₀} {Γ} {Δ₁ ++ A' ∷ B' ∷ Δ₂} {A} {C} f g) Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (Γ ++ Δ₁ ++ A' ⊗ B' ∷ Δ₂) γ
    ... | (Λ₀ , Λ , refl , δ₀ , γ , refl) with is-⟦++⟧ Γ (Δ₁ ++ A' ⊗ B' ∷ Δ₂) γ
    ... | (Ω , Λ , refl , ω , γ , refl) with is-⟦++⟧ Δ₁ (A' ⊗ B' ∷ Δ₂) γ
    ... | (Λ₁ , _ , refl , δ₁ , (Ξ , Λ₂ , refl , k , δ₂) , refl) 
      rewrite
        sym (⟦++⟧ass Δ₀ (A ∷ Δ₁) (A' ⊗ B' ∷ Δ₂) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁) (Ξ , Λ₂ , refl , k , δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ A ∷ Δ₁) (A' ⊗ B' ∷ Δ₂) (⟦++⟧ Δ₀ (A ∷ Δ₁) δ₀ (Ω , Λ₁ , refl , f Ω ω , δ₁)) (Ξ , Λ₂ , refl , k , δ₂) |
        sym (⟦++⟧ass Γ Δ₁ (A' ⊗ B' ∷ Δ₂) ω δ₁ (Ξ , Λ₂ , refl , k , δ₂)) |
        sym (⟦++⟧ass Δ₀ (Γ ++ Δ₁) (A' ⊗ B' ∷ Δ₂) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁) (Ξ , Λ₂ , refl , k , δ₂)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ Γ ++ Δ₁) (A' ⊗ B' ∷ Δ₂) (⟦++⟧ Δ₀ (Γ ++ Δ₁) δ₀ (⟦++⟧ Γ Δ₁ ω δ₁)) (Ξ , Λ₂ , refl , k , δ₂) =
          cong (proj₂ ⟦ C ⟧ (Λ₀ ++ Ω ++ Λ₁ ++ Ξ ++ Λ₂)) (ifunext (λ B → funext (λ h →
            cong (⊸lR-inv* (Λ₀ ++ Ω ++ Λ₁)) (cong (⊸rR-inv* Λ₂) (cong k (ifunext (λ Φ → funext (λ { (Φ₀ , Φ₁ , refl , x , y) →
              cong (⊸rR* Λ₂) (cong (⊸lR* (Λ₀ ++ Ω ++ Λ₁)) (cong h (cong (g (Λ₀ ++ Ω ++ Λ₁ ++ Φ₀ ++ Φ₁ ++ Λ₂))
                (lem' Δ₀ Δ₁ Δ₂ Λ₀ Ω Λ₁ Λ₂ Φ₀ Φ₁ δ₀ ω δ₁ δ₂ x y)))) }))))))))




--                       Δ₀, Δ₁ ⊢ C
--   ------ IR    --------------------- IL
--     ⊢ I           Δ₀, I , Δ₁ ⊢ C    
--   ---------------------------------- cut
--          Δ₀, Δ₁ ⊢ C
--
-- is equal to
--
--    Δ₀, Δ₁ ⊢ C

princ-cutI : ∀{Δ₀ Δ₁ C}
  → (f : ⟦ Δ₀ ++ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {[]} {Δ₁} {I} {C} ⟦IR⟧ (⟦IL⟧ {Δ₀} {Δ₁} {C} f) ≡ f
princ-cutI {Δ₀} {Δ₁} {C} f =
  funext (λ Λ → funext (lem Λ))
  where
    lem : ∀ Λ (γ :  ⟦ Δ₀ ++ Δ₁ ⟧-cxt Λ)
      → ⟦cut⟧ {Δ₀} {[]} {Δ₁} {I} {C} ⟦IR⟧ (⟦IL⟧ {Δ₀} {Δ₁} {C} f) Λ γ ≡ f Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ Δ₁ γ
    ... | (Λ₀ , Λ₁ , refl , γ₀ , γ₁ , refl)
      rewrite ⟦++⟧-is-⟦++⟧ Δ₀ (I ∷ Δ₁) γ₀ ([] , Λ₁ , refl , (λ h → h refl) , γ₁) =
      trans (cong (proj₂ ⟦ C ⟧ (Λ₀ ++ Λ₁)) (ifunext (λ A → funext (λ g →
                trans (cong (⊸lR-inv* Λ₀) (⊸rR-inv*⊸rR* Λ₁ _))
                      (⊸lR-inv*⊸lR* Λ₀ _)))))
            (run-η' C (Λ₀ ++ Λ₁) _)


--    Γ₀ ⊢ A   Γ₁ ⊢ B           Δ₀, A, B, Δ₁ ⊢ C
--   ------------------ ⊗R    --------------------- ⊗L
--     Γ₀, Γ₁ ⊢ A ⊗ B           Δ₀, A ⊗ B, Δ₁ ⊢ C    
--   ------------------------------------------------ cut
--                Δ₀, Γ₀, Γ₁, Δ₁ ⊢ C
--
-- is equal to
--
--                       Γ₁ ⊢ B            Δ₀, A, B, Δ₁ ⊢ C
--                     -------------------------------- cut
--        Γ₀ ⊢ A             Δ₀, Γ₀, B, Δ₁ ⊢ C    
--   ------------------------------------------------ cut
--                Δ₀, Γ₀, Γ₁, Δ₁ ⊢ C

princ-cut⊗ : ∀{Δ₀ Γ₀ Γ₁ Δ₁ A B C}
  → (f : ⟦ Γ₀ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (g : ⟦ Γ₁ ⟧-cxt ⇒ ⟦ B ⟧ ¹)
  → (h : ⟦ Δ₀ ++ A ∷ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Γ₀ ++ Γ₁} {Δ₁} {A ⊗ B} {C} (⟦⊗R⟧ {Γ₀}{Γ₁}{A}{B} f g) (⟦⊗L⟧ {Δ₀} {Δ₁} {C = C} h)
          ≡ ⟦cut⟧ {Δ₀} {Γ₀} {Γ₁ ++ Δ₁} {A} {C} f (⟦cut⟧ {Δ₀ ∷ʳ A} {Γ₁} {Δ₁} {B} {C} g h)
princ-cut⊗ {Δ₀}{Γ₀}{Γ₁}{Δ₁}{A}{B}{C} f g h = funext (λ Λ → funext (λ γ → lem Λ γ))
  where
    lem : ∀ Λ (γ :  ⟦ Δ₀ ++ Γ₀ ++ Γ₁ ++ Δ₁ ⟧-cxt Λ)
      → ⟦cut⟧ {Δ₀} {Γ₀ ++ Γ₁} {Δ₁} {A ⊗ B} {C} (⟦⊗R⟧ {Γ₀}{Γ₁}{A}{B} f g) (⟦⊗L⟧ {Δ₀} {Δ₁} {C = C} h) Λ γ
          ≡ ⟦cut⟧ {Δ₀} {Γ₀} {Γ₁ ++ Δ₁} {A} {C} f (⟦cut⟧ {Δ₀ ∷ʳ A} {Γ₁} {Δ₁} {B} {C} g h) Λ γ
    lem Λ γ with is-⟦++⟧ Δ₀ (Γ₀ ++ Γ₁ ++ Δ₁) γ
    ... | (Λ₀ , Λ , refl , γ₀ , γ , refl) with is-⟦++⟧ Γ₀ (Γ₁ ++ Δ₁) γ
    ... | (Ω₀ , Λ , refl , ω₀ , γ , refl) with is-⟦++⟧ Γ₁ Δ₁ γ
    ... | (Ω₁ , Λ₁ , refl , ω₁ , γ₁ , refl)
      rewrite
        sym (⟦++⟧ass Δ₀ [ A ] (Γ₁ ++ Δ₁) γ₀ (Ω₀ , [] , refl , f Ω₀ ω₀ , refl) (⟦++⟧ Γ₁ Δ₁ ω₁ γ₁)) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ A ∷ []) (Γ₁ ++ Δ₁) (⟦++⟧ Δ₀ (A ∷ []) γ₀ (Ω₀ , [] , refl , f Ω₀ ω₀ , refl)) (⟦++⟧ Γ₁ Δ₁ ω₁ γ₁) |
        ⟦++⟧-is-⟦++⟧ Γ₁ Δ₁ ω₁ γ₁ |
        sym (⟦++⟧ass Γ₀ Γ₁ Δ₁ ω₀ ω₁ γ₁) |
        ⟦++⟧-is-⟦++⟧ (Γ₀ ++ Γ₁) Δ₁ (⟦++⟧ Γ₀ Γ₁ ω₀ ω₁) γ₁ |
        ⟦++⟧-is-⟦++⟧ Γ₀ Γ₁ ω₀ ω₁ |
        ⟦++⟧-is-⟦++⟧ Δ₀ ((A ⊗ B) ∷ Δ₁) γ₀ (Ω₀ ++ Ω₁ , Λ₁ , refl , η-cl (Ω₀ ++ Ω₁) (Ω₀ , Ω₁ , refl , f Ω₀ ω₀ , g Ω₁ ω₁) , γ₁) =
          trans (cong (proj₂ ⟦ C ⟧ (Λ₀ ++ Ω₀ ++ Ω₁ ++ Λ₁)) (ifunext (λ D → funext (λ k →
                   trans (cong (⊸lR-inv* Λ₀) (⊸rR-inv*⊸rR* {Ω₀ ++ Ω₁} Λ₁ _))
                         (⊸lR-inv*⊸lR* Λ₀ _)))))
                (trans (run-η' C (Λ₀ ++ Ω₀ ++ Ω₁ ++ Λ₁) _)
                       (cong (h (Λ₀ ++ Ω₀ ++ Ω₁ ++ Λ₁))
                             (sym (⟦++⟧ass Δ₀ [ A ] (B ∷ Δ₁) γ₀ (Ω₀ , [] , refl , f Ω₀ ω₀ , refl) (Ω₁ , Λ₁ , refl , g Ω₁ ω₁ , γ₁)))))


--      Λ, A ⊢ B             Γ ⊢ A     Δ₀, B, Δ₁ ⊢ C
--   -------------- ⊸rR    ---------------------------- ⊸rL
--     Λ ⊢ A ⊸r B             Δ₀, A ⊸r B, Γ, Δ₁ ⊢ C    
--   ------------------------------------------------ cut
--                Δ₀, Λ, Γ, Δ₁ ⊢ C
--
-- is equal to
--
--     Γ ⊢ A      Λ, A ⊢ B                 
--    ---------------------- cut              
--           Λ, Γ ⊢ B                Δ₀, B, Δ₁ ⊢ C    
--   ------------------------------------------------ cut
--                Δ₀, Λ, Γ, Δ₁ ⊢ C

princ-cut⊸r : ∀{Δ₀ Γ Δ₁ Λ A B C}
  → (f : ⟦ Λ ∷ʳ A ⟧-cxt ⇒ ⟦ B ⟧ ¹)
  → (g : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (h : ⟦ Δ₀ ++ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹)
  → ⟦cut⟧ {Δ₀} {Λ} {Γ ++ Δ₁} {A ⊸r B} {C} (⟦⊸rR⟧ {Λ} {A} {B} f) (⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{C} g h)
          ≡ ⟦cut⟧ {Δ₀} {Λ ++ Γ} {Δ₁} {B} {C} (⟦cut⟧ {Λ} {Γ} {[]} {A} {B} g f) h
princ-cut⊸r {Δ₀}{Γ}{Δ₁}{Λ}{A}{B}{C} f g h = funext (λ Ω → funext (lem Ω))
  where
    lem : ∀ Ω (ω : ⟦ Δ₀ ++ Λ ++ Γ ++ Δ₁ ⟧-cxt Ω)
      → ⟦cut⟧ {Δ₀} {Λ} {Γ ++ Δ₁} {A ⊸r B} {C} (⟦⊸rR⟧ {Λ} {A} {B} f) (⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{C} g h) Ω ω
          ≡ ⟦cut⟧ {Δ₀} {Λ ++ Γ} {Δ₁} {B} {C} (⟦cut⟧ {Λ} {Γ} {[]} {A} {B} g f) h Ω ω
    lem Ω ω with is-⟦++⟧ Δ₀ (Λ ++ Γ ++ Δ₁) ω
    ... | (Ω₀ , Ω , refl , ω₀ , ω , refl) with is-⟦++⟧ Λ (Γ ++ Δ₁) ω
    ... | (Λ' , Ω , refl , λ' , ω , refl) with is-⟦++⟧ Γ Δ₁ ω
    ... | (Γ' , Ω₁ , refl , γ' , ω₁ , refl)
      rewrite
        ⟦++⟧-is-⟦++⟧ Δ₀ ((A ⊸r B) ∷ Γ ++ Δ₁) ω₀ (Λ' , Γ' ++ Ω₁ , refl , (λ Δ x → f (Λ' ++ Δ) (⟦++⟧ Λ (A ∷ []) λ' (Δ , [] , refl , x , refl))) , ⟦++⟧ Γ Δ₁ γ' ω₁) |
        ⟦++⟧-is-⟦++⟧ Γ Δ₁ γ' ω₁ |
        sym (⟦++⟧ass Λ Γ Δ₁ λ' γ' ω₁) |
        ⟦++⟧-is-⟦++⟧ (Λ ++ Γ) Δ₁ (⟦++⟧ Λ Γ λ' γ') ω₁ |
        ⟦++⟧-is-⟦++⟧ Λ Γ λ' γ' |
        sym (⟦++⟧ru Γ γ') |
        ⟦++⟧-is-⟦++⟧ Γ [] γ' refl |
        ⟦++⟧ru Γ γ' = refl

-- ====================================

-- The model satisfies additional equations, e.g. ⊗R commutes with ⊸rL

--        Γ ⊢ A      Δ₀, B, Δ₁ ⊢ A'      
--  --------------------------------- ⊸rL
--        Δ₀, A ⊸r B, Γ, Δ₁ ⊢ A'              Δ₂ ⊢ B'
--   ------------------------------------------------------- ⊗R
--              Δ₀, A ⊸r B, Γ, Δ₁, Δ₂ ⊢ A' ⊗ B'
--
-- is equal to
--
--                        Δ₀, B, Δ₁ ⊢ A'       Δ₂ ⊢ B'  
--                       --------------------------------- ⊗R
--        Γ ⊢ A              Δ₀, B, Δ₁, Δ₂ ⊢ A' ⊗ B'              
--   ------------------------------------------------------- ⊸rL
--              Δ₀, A ⊸r B, Γ, Δ₁, Δ₂ ⊢ A' ⊗ B'

⟦⊗R⊸rL⟧ : ∀ {Δ₀ Γ Δ₁ Δ₂ A B A' B'}
  → (f : ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹)
  → (g : ⟦ Δ₀ ++ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ A' ⟧ ¹)
  → (h : ⟦ Δ₂ ⟧-cxt ⇒ ⟦ B' ⟧ ¹)
  → ⟦⊗R⟧ {Δ₀ ++ A ⊸r B ∷ Γ ++ Δ₁}{Δ₂}{A'}{B'} (⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{A'} f g) h
         ≡ ⟦⊸rL⟧ {Δ₀} {Γ} {Δ₁ ++ Δ₂} {A} {B} {A' ⊗ B'} f (⟦⊗R⟧ {Δ₀ ++ B ∷ Δ₁}{Δ₂}{A'}{B'} g h)
⟦⊗R⊸rL⟧ {Δ₀}{Γ}{Δ₁}{Δ₂}{A}{B}{A'}{B'} f g h =
  funext λ Λ → funext (λ γ → ifunext (λ C → funext (lem Λ γ)))
  where
    lem : ∀ Λ (γ : ⟦ Δ₀ ++ A ⊸r B ∷ Γ ++ Δ₁ ++ Δ₂ ⟧-cxt Λ )
      → ∀ {C} (k : ∀ {Δ} → ((⟦ A' ⟧ ¹) ⊗-psh (⟦ B' ⟧ ¹)) Δ → ⟨ C ⟩ Δ)
      → ⟦⊗R⟧ {Δ₀ ++ A ⊸r B ∷ Γ ++ Δ₁}{Δ₂}{A'}{B'} (⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{A'} f g) h Λ γ k
             ≡ ⟦⊸rL⟧ {Δ₀} {Γ} {Δ₁ ++ Δ₂} {A} {B} {A' ⊗ B'} f (⟦⊗R⟧ {Δ₀ ++ B ∷ Δ₁}{Δ₂}{A'}{B'} g h) Λ γ k
    lem Λ γ k with is-⟦++⟧ Δ₀ (A ⊸r B ∷ Γ ++ Δ₁ ++ Δ₂) γ
    ... | (Λ₀ , _ , refl , δ₀ , (Ω , _ , refl , l , γ)  , refl) with is-⟦++⟧ Γ (Δ₁ ++ Δ₂) γ
    ... | (Λ' , _ , refl , γ' , γ , refl) with is-⟦++⟧ Δ₁ Δ₂ γ
    ... | (Λ₁ , Λ₂ , refl , δ₁ , δ₂ , refl)
      rewrite
        sym (⟦++⟧ass Δ₀ ((A ⊸r B) ∷ Γ) (Δ₁ ++ Δ₂) δ₀ (Ω , Λ' , refl , l , γ') (⟦++⟧ Δ₁ Δ₂ δ₁ δ₂)) |
        sym (⟦++⟧ass (Δ₀ ++ (A ⊸r B) ∷ Γ) Δ₁ Δ₂ (⟦++⟧ Δ₀ ((A ⊸r B) ∷ Γ) δ₀ (Ω , Λ' , refl , l , γ')) δ₁ δ₂) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ (A ⊸r B) ∷ Γ ++ Δ₁) Δ₂ (⟦++⟧ (Δ₀ ++ (A ⊸r B) ∷ Γ) Δ₁  (⟦++⟧ Δ₀ ((A ⊸r B) ∷ Γ) δ₀ (Ω , Λ' , refl , l , γ')) δ₁) δ₂ |
        ⟦++⟧ass Δ₀ (A ⊸r B ∷ Γ) Δ₁ δ₀ (Ω , Λ' , refl , l , γ') δ₁ |
        ⟦++⟧-is-⟦++⟧ Δ₀ ((A ⊸r B) ∷ Γ ++ Δ₁) δ₀ (Ω , Λ' ++ Λ₁ , refl , l , ⟦++⟧ Γ Δ₁ γ' δ₁) |
        ⟦++⟧-is-⟦++⟧ Γ Δ₁ γ' δ₁ |
        sym (⟦++⟧ass Δ₀ (B ∷ Δ₁) Δ₂ δ₀ (Ω ++ Λ' , Λ₁ , refl , l Λ' (f Λ' γ') , δ₁) δ₂) |
        ⟦++⟧-is-⟦++⟧ (Δ₀ ++ B ∷ Δ₁) Δ₂ (⟦++⟧ Δ₀ (B ∷ Δ₁) δ₀ (Ω ++ Λ' , Λ₁ , refl , l Λ' (f Λ' γ') , δ₁)) δ₂ = refl


