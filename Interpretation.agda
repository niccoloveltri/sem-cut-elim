{-# OPTIONS --rewriting #-}

module Interpretation where

open import Function
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Utilities
open import SequentCalculus
open import Model 

-- Interpretation of formulae
⟦_⟧ : Fma → ∁
⟦ ` X ⟧ = ⟪ ` X ⟫
⟦ I ⟧ = ⟦I⟧
⟦ A ⊗ B ⟧ = ⟦ A ⟧ ⟦⊗⟧ ⟦ B ⟧
⟦ A ⊸r B ⟧ = ⟦ A ⟧ ⟦⊸r⟧ ⟦ B ⟧
⟦ A ⊸l B ⟧ = ⟦ A ⟧ ⟦⊸l⟧ ⟦ B ⟧

-- Interpretation of contexts (as presheaves, not necessarily closed)
⟦_⟧-cxt : Cxt → ℙCxt
⟦ [] ⟧-cxt = I-psh
⟦ A ∷ Γ ⟧-cxt = ⟦ A ⟧ ¹ ⊗-psh ⟦ Γ ⟧-cxt

-- A concatenation operation on the interpretation of contexts, which
-- is unital and associative
⟦++⟧ : ∀ Γ Γ' {Λ Λ'} → ⟦ Γ ⟧-cxt Λ → ⟦ Γ' ⟧-cxt Λ'
  → ⟦ Γ ++ Γ' ⟧-cxt (Λ ++ Λ')
⟦++⟧ [] _ refl γ' = γ'
⟦++⟧ (A ∷ Γ) Γ' {Λ' = Λ'} (Λ₁ , Λ₂ , refl , x , γ) γ' =
  Λ₁ , Λ₂ ++ Λ' , refl , x , (⟦++⟧ Γ Γ' γ γ')

⟦++⟧ru : ∀ Γ {Δ} (γ : ⟦ Γ ⟧-cxt Δ) → ⟦++⟧ Γ [] γ refl ≡ γ
⟦++⟧ru [] refl = refl
⟦++⟧ru (A ∷ Γ) (Δ₁ , Δ₂ , refl , a , γ) rewrite ⟦++⟧ru Γ γ = refl

⟦++⟧ass : ∀ Γ₁ Γ₂ Γ₃ {Δ₁ Δ₂ Δ₃}
  → (γ₁ : ⟦ Γ₁ ⟧-cxt Δ₁) (γ₂ : ⟦ Γ₂ ⟧-cxt Δ₂) (γ₃ : ⟦ Γ₃ ⟧-cxt Δ₃)
  → ⟦++⟧ (Γ₁ ++ Γ₂) Γ₃ (⟦++⟧ Γ₁ Γ₂ γ₁ γ₂) γ₃
       ≡ ⟦++⟧ Γ₁ (Γ₂ ++ Γ₃) γ₁ (⟦++⟧ Γ₂ Γ₃ γ₂ γ₃)
⟦++⟧ass [] _ _ refl γ₂ γ₃ = refl
⟦++⟧ass (A ∷ Γ₁) Γ₂ Γ₃ (_ , _ , refl , a , γ₁) γ₂ γ₃
  rewrite ⟦++⟧ass Γ₁ Γ₂ Γ₃ γ₁ γ₂ γ₃ = refl

-- Some lemmata about semantic concatenation ⟦++⟧
is-⟦++⟧ : ∀ Γ₁ Γ₂ {Λ} (γ : ⟦ Γ₁ ++ Γ₂ ⟧-cxt Λ)
  → Σ Cxt λ Λ₁ → Σ Cxt λ Λ₂ → Σ (Λ ≡ Λ₁ ++ Λ₂) λ eq 
      → Σ (⟦ Γ₁ ⟧-cxt Λ₁) λ γ₁ → Σ (⟦ Γ₂ ⟧-cxt Λ₂) λ γ₂
          → subst ⟦ Γ₁ ++ Γ₂ ⟧-cxt eq γ ≡ ⟦++⟧ Γ₁ Γ₂  γ₁ γ₂ 
is-⟦++⟧ [] Γ₂ {Λ} γ = [] , Λ , refl , refl , γ , refl
is-⟦++⟧ (A ∷ Γ₁) Γ₂ (Ω , Λ' , refl , x , γ) with is-⟦++⟧ Γ₁ Γ₂ γ
... | Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl =
  Ω ++ Λ₁ , Λ₂ , refl , (Ω , Λ₁ , refl , x , γ₁) , γ₂ , refl

⟦++⟧-is-⟦++⟧ : ∀ Γ₁ Γ₂ {Λ₁ Λ₂} (γ₁ : ⟦ Γ₁ ⟧-cxt Λ₁) (γ₂ : ⟦ Γ₂ ⟧-cxt Λ₂)
  → is-⟦++⟧ Γ₁ Γ₂ (⟦++⟧ Γ₁ Γ₂ γ₁ γ₂) ≡ (Λ₁ , Λ₂ , refl , γ₁ , γ₂ , refl)
⟦++⟧-is-⟦++⟧ [] _ refl γ₂ = refl
⟦++⟧-is-⟦++⟧ (A ∷ Γ₁) Γ₂ (_ , _ , refl , γ₁ , γ₁') γ₂
  rewrite ⟦++⟧-is-⟦++⟧ Γ₁ Γ₂ γ₁' γ₂ = refl

-- The cut rule is admissible in the model
map++R : ∀ {Γ Δ Δ'} → ⟦ Δ ⟧-cxt ⇒ ⟦ Δ' ⟧-cxt → ⟦ Γ ++ Δ ⟧-cxt ⇒ ⟦ Γ ++ Δ' ⟧-cxt
map++R {Γ} {Δ} {Δ'} f Λ γ with is-⟦++⟧ Γ Δ γ
... | (Λ₁ , Λ₂ , refl , γ , δ , refl) = ⟦++⟧ Γ Δ' γ (f _ δ)

map++L : ∀ {Γ Γ' Δ} → ⟦ Γ ⟧-cxt ⇒ ⟦ Γ' ⟧-cxt → ⟦ Γ ++ Δ ⟧-cxt ⇒ ⟦ Γ' ++ Δ ⟧-cxt
map++L {Γ} {Γ'} {Δ} f Λ γ with is-⟦++⟧ Γ Δ γ
... | (Λ₁ , Λ₂ , refl , γ , δ , refl) = ⟦++⟧ Γ' Δ (f _ γ) δ

⟦cut⟧ : ∀{Δ₀ Γ Δ₁ A C}
  → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹
  → ⟦ Δ₀ ++ A ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
  → ⟦ Δ₀ ++ Γ ++ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
⟦cut⟧ {Δ₀}{Γ}{Δ₁}{A} f g Λ x =
  g Λ (map++R {Δ₀} {Γ ++ Δ₁} {_ ∷ Δ₁} (map++L {Γ} {[ A ]} {Δ₁} (ρ-psh ∘-psh f)) Λ x)

-- Interpretation of Lambek calculus inference rules.
-- For each rule Rl, we write ⟦Rl⟧ for its counterpart in the model. 
⟦ax⟧ : ∀ {A} → ⟦ [ A ] ⟧-cxt ⇒ ⟦ A ⟧ ¹
⟦ax⟧ _ (Γ₁ , [] , refl , x , refl) = x 

⟦⊸rR⟧ : ∀ {Γ A B} → ⟦ Γ ∷ʳ A ⟧-cxt ⇒ ⟦ B ⟧ ¹
  → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹ ⊸r-psh ⟦ B ⟧ ¹
⟦⊸rR⟧ {Γ} f Λ γ Δ x =
  f _ (⟦++⟧ Γ (_ ∷ []) {Λ' = Δ} γ (_ , _ , refl , x , refl))

⟦⊸lR⟧ : ∀ {Γ A B} → ⟦ A ∷ Γ ⟧-cxt ⇒ ⟦ B ⟧ ¹
  → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹ ⊸l-psh ⟦ B ⟧ ¹
⟦⊸lR⟧ {Γ} {A} f Λ γ Δ x =
  f _ (⟦++⟧ (A ∷ []) Γ {Δ} {Λ} (_ , _ , refl , x , refl) γ)

⟦IR⟧ : ⟦ [] ⟧-cxt ⇒ ⟦I⟧ ¹
⟦IR⟧ Λ γ h = h γ

⟦⊗R⟧ : ∀ {Γ Δ A B} → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹ → ⟦ Δ ⟧-cxt ⇒ ⟦ B ⟧ ¹
  → ⟦ Γ ++ Δ ⟧-cxt ⇒ (⟦ A ⟧ ⟦⊗⟧ ⟦ B ⟧) ¹
⟦⊗R⟧ {Γ}{Δ} f g Λ γ with is-⟦++⟧ Γ Δ γ
... | Λ₁ , Λ₂ , refl , γ , δ , refl =
  η-cl _ (Λ₁ , Λ₂ , refl , f _ γ , g _ δ) 

⟦⊸rL⟧ : ∀ {Δ₀ Γ Δ₁ A B C} → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹
  → ⟦ Δ₀ ++ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
  →  ⟦ Δ₀ ++ (A ⊸r B) ∷ Γ ++ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁} f g _ γ with is-⟦++⟧ Δ₀ (_ ∷ Γ ++ Δ₁) γ
... | (Λ₁ , _ , refl , δ₀ , (Ω , _ , refl , h , γ) , refl) with is-⟦++⟧ Γ Δ₁ γ
... | (Λ , Λ₂ , refl , γ , δ₁ , refl) =
  g _ (⟦++⟧ Δ₀ (_ ∷ Δ₁) {Λ₁}{Ω ++ Λ ++ Λ₂}
            δ₀
            (Ω ++ Λ , Λ₂ , refl , h Λ (f _ γ) , δ₁))

⟦⊸lL⟧ : ∀ {Δ₀ Γ Δ₁ A B C} → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹
  → ⟦ Δ₀ ++ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
  →  ⟦ Δ₀ ++ Γ ++ (A ⊸l B) ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
⟦⊸lL⟧ {Δ₀}{Γ}{Δ₁} f g _ γ with is-⟦++⟧ Δ₀ (Γ ++ _ ∷ Δ₁) γ
... | (Λ₁ , _ , refl , δ₀ , γ , refl) with is-⟦++⟧ Γ (_ ∷ Δ₁) γ
... | (Λ , _ , refl , γ , (Ω , Λ₂ , refl , h , δ₁) , refl) =
  g _ (⟦++⟧ Δ₀ (_ ∷ Δ₁) {Λ₁} {Λ ++ Ω ++ Λ₂}
            δ₀
            (Λ ++ Ω , Λ₂ , refl , h Λ (f _ γ) , δ₁))

⟦IL⟧ : ∀ {Δ₀ Δ₁ C} → ⟦ Δ₀ ++ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
  →  ⟦ Δ₀ ++ I ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
⟦IL⟧ {Δ₀}{Δ₁}{C} f Λ γ with is-⟦++⟧ Δ₀ (I ∷ Δ₁) γ
... | (Λ₁ , _ , refl , δ₀ , (Ω , Λ₂ , refl , h , δ₁) , refl) =
  up-cl ⟦ C ⟧ g _ l3
  where
    l1 : cl (I-psh ⊗-psh ⟦ Δ₁ ⟧-cxt) (Ω ++ Λ₂)
    l1 = mstrR-cl (Ω ++ Λ₂) (_ , _ , refl , h , δ₁)

    l2 : cl ⟦ Δ₁ ⟧-cxt (Ω ++ Λ₂)
    l2 = map-cl λ-psh _ l1

    l3 : cl (⟦ Δ₀ ⟧-cxt ⊗-psh ⟦ Δ₁ ⟧-cxt) (Λ₁ ++ Ω ++ Λ₂)
    l3 = mstrL-cl _ (_ , _ , refl , δ₀ , l2)

    g : ⟦ Δ₀ ⟧-cxt ⊗-psh ⟦ Δ₁ ⟧-cxt  ⇒ ⟦ C ⟧ ¹
    g _ (Λ₁ , Λ₂ , refl , δ₀ , δ₁) = f _ (⟦++⟧ Δ₀ Δ₁ δ₀ δ₁)


⟦⊗L⟧ : ∀ {Δ₀ Δ₁ A B C} → ⟦ Δ₀ ++ A ∷ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
  →  ⟦ Δ₀ ++ A ⊗ B ∷ Δ₁ ⟧-cxt ⇒ ⟦ C ⟧ ¹
⟦⊗L⟧ {Δ₀}{Δ₁}{A}{B}{C} f Λ γ with is-⟦++⟧ Δ₀ (_ ∷ Δ₁) γ
... | (Λ₁ , _ , refl , δ₀ , (Ω , Λ₂ , refl , h , δ₁) , refl) =
  up-cl ⟦ C ⟧ g _ l3
  where
    l1 : cl ((⟦ A ⟧ ¹ ⊗-psh ⟦ B ⟧ ¹) ⊗-psh ⟦ Δ₁ ⟧-cxt) (Ω ++ Λ₂)
    l1 = mstrR-cl (Ω ++ Λ₂) (_ , _ , refl , h , δ₁) 

    l2 : cl (⟦ A ⟧ ¹ ⊗-psh (⟦ B ⟧ ¹ ⊗-psh ⟦ Δ₁ ⟧-cxt)) (Ω ++ Λ₂)
    l2 = map-cl α-psh _ l1

    l3 : cl (⟦ Δ₀ ⟧-cxt ⊗-psh (⟦ A ⟧ ¹ ⊗-psh (⟦ B ⟧ ¹ ⊗-psh ⟦ Δ₁ ⟧-cxt))) (Λ₁ ++ Ω ++ Λ₂)
    l3 = mstrL-cl _ (_ , _ , refl , δ₀ , l2)

    g : ⟦ Δ₀ ⟧-cxt ⊗-psh (⟦ A ⟧ ¹ ⊗-psh (⟦ B ⟧ ¹ ⊗-psh ⟦ Δ₁ ⟧-cxt)) ⇒ ⟦ C ⟧ ¹
    g _ (Λ₁ , _ , refl , δ₀ , (Ω₁ , _ , refl , x , (Ω₂ , Λ₂ , refl , y , δ₁))) =
      f _ (⟦++⟧ Δ₀ (A ∷ B ∷ Δ₁) {Λ₁} {Ω₁ ++ Ω₂ ++ Λ₂}
                δ₀
                (Ω₁ , Ω₂ ++ Λ₂ , refl , x , Ω₂ , Λ₂ , refl , y , δ₁))


-- The soundness function
sound : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧-cxt ⇒ ⟦ A ⟧ ¹
sound (ax {A}) = ⟦ax⟧ {A}
sound (⊸rR {Γ}{A}{B} f) = ⟦⊸rR⟧ {Γ}{A}{B} (sound f)
sound (⊸lR {Γ}{A}{B} f) = ⟦⊸lR⟧ {Γ}{A}{B} (sound f)
sound IR = ⟦IR⟧ 
sound (⊗R {Γ}{Δ}{A}{B} f g) = ⟦⊗R⟧ {Γ}{Δ}{A}{B} (sound f) (sound g)
sound (⊸rL {Δ₀}{Γ}{Δ₁}{A}{B}{C} f g) =
  ⟦⊸rL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{C} (sound f) (sound g)
sound (⊸lL {Δ₀}{Γ}{Δ₁}{A}{B}{C} f g) =
  ⟦⊸lL⟧ {Δ₀}{Γ}{Δ₁}{A}{B}{C} (sound f) (sound g)
sound (IL {Δ₀}{Δ₁}{C} f) = ⟦IL⟧ {Δ₀}{Δ₁}{C} (sound f)
sound (⊗L {Δ₀}{Δ₁}{A}{B}{C} f) = ⟦⊗L⟧ {Δ₀}{Δ₁}{A}{B}{C} (sound f)




-- The equation
-- -- run P ∘-psh η-cl ≡ id-psh
-- does not generally hold for closed presheaves (we are not requiring
-- it yet), but it is true when -- the closed presheaf P is of the
-- form ⟦ C ⟧ for some formula C
run-η' : ∀ C Γ (x : (⟦ C ⟧ ¹) Γ) → (run ⟦ C ⟧ ∘-psh η-cl) Γ x ≡ x
run-η' (` X) Γ x = refl
run-η' I Γ x = refl
run-η' (A ⊗ B) Γ x = refl
run-η' (A ⊸r B) Γ x = funext (λ Δ → funext (λ y →
  trans (cong (proj₂ ⟦ B ⟧ (Γ ++ Δ)) (ifunext (λ C → funext (λ g → ⊸rR-inv*⊸rR* Δ _))))
  -- cstrR-cl ⟦ B ⟧ Γ (η-cl Γ x) Δ y g ≡ η-cl (Γ ++ Δ) (x Δ y) g
        (run-η' B (Γ ++ Δ) (x Δ y))))
run-η' (A ⊸l B) Γ x = funext (λ Δ → funext (λ y →
  trans (cong (proj₂ ⟦ B ⟧ (Δ ++ Γ)) (ifunext (λ C → funext (λ g → ⊸lR-inv*⊸lR* Δ _))))
  --cstrL-cl ⟦ B ⟧ Γ (η-cl Γ x) Δ y g ≡ η-cl (Δ ++ Γ) (x Δ y) g
        (run-η' B (Δ ++ Γ) (x Δ y))))

run-η : ∀ C → run ⟦ C ⟧ ∘-psh η-cl ≡ id-psh
run-η C = funext (λ Γ → funext (run-η' C Γ))
