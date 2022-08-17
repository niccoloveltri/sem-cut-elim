{-# OPTIONS --rewriting #-}

module Model where

open import Function
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Utilities
open import SequentCalculus

-- The type of presheaves over the monoid Cxt
ℙCxt : Set₁
ℙCxt = Cxt → Set

-- Maps between presheaves are natural transformations
_⇒_ : (P Q : ℙCxt) → Set
P ⇒ Q = ∀ Γ → P Γ → Q Γ

infix 19 _⇒_

-- Identity and sequential composition of maps between presheaves
id-psh : ∀ {P} → P ⇒ P
id-psh Γ = id

_∘-psh_ : ∀ {P Q R} → Q ⇒ R → P ⇒ Q → P ⇒ R
(f ∘-psh g) Γ x = f Γ (g Γ x)

-- Each formula specifies a presheaf of derivations
⟨_⟩ : Fma → ℙCxt
⟨ A ⟩ Γ = Γ ⊢ A

-- The closure operator
-- In the usual proof-irrelevant formulation, this reads:
-- Δ ∈ cl P   iff   Δ ∈ ⟨ A ⟩ for all formula A such that P ⊆ ⟨ A ⟩ 
cl : (Cxt → Set) → Cxt → Set
cl P Δ = ∀ {A} → (∀ {Γ} → P Γ → ⟨ A ⟩ Γ) → ⟨ A ⟩ Δ

-- The operator cl is a functor
map-cl : ∀ {P Q} (f : P ⇒ Q) → cl P ⇒ cl Q
map-cl f Δ h g = h (λ x → g (f _ x)) 

map-id-cl : ∀ {P} → map-cl id-psh ≡ id-psh {cl P}
map-id-cl = refl

map-∘-cl : ∀ {P Q R} (f : Q ⇒ R) (g : P ⇒ Q)
  → map-cl (f ∘-psh g) ≡ map-cl f ∘-psh map-cl g
map-∘-cl f g = refl

-- The operator cl is a monad
η-cl : ∀ {P} → P ⇒ cl P
η-cl Δ x g = g x

μ-cl : ∀ {P} → cl (cl P) ⇒ cl P
μ-cl Δ h g = h (λ k → k g)

μ-η-cl1 : ∀ {P} → μ-cl ∘-psh η-cl ≡ id-psh {cl P}
μ-η-cl1 = refl

μ-η-cl2 : ∀ {P} → μ-cl ∘-psh map-cl η-cl ≡ id-psh {cl P}
μ-η-cl2 = refl

μ-μ-cl : ∀ {P} → μ-cl ∘-psh μ-cl {cl P} ≡ μ-cl ∘-psh map-cl μ-cl
μ-μ-cl = refl

-- The type of cl-algebras, with names for its two projections.
∁ : Set₁
∁ = Σ ℙCxt λ P → cl P ⇒ P

_¹ : ∁ → ℙCxt
_¹ = proj₁

infixr 21 _¹

run : (P : ∁) → cl (P ¹) ⇒ P ¹
run = proj₂

-- -- Remarks:
-- 1) Probably one should also require some relationship between the
-- algebra and the monad unit. A natural one would be:
-- run P ∘-psh η-cl ≡ id-psh

-- 2) I am not super sure what is the right notion of morphisms
-- between such objects. For the moment a map between elements of ∁ is
-- just a map between the carriers. But probably one should ask for
-- cl-algebra morphisms.

-- Universal property of cl: 
up-cl : ∀ {P} (Q : ∁) → P ⇒ Q ¹ → cl P ⇒ Q ¹
up-cl (Q , runQ) f = runQ ∘-psh map-cl f

up-inv-cl : ∀ {P} (Q : ∁) → cl P ⇒ Q ¹ → P ⇒ Q ¹
up-inv-cl _ f = f ∘-psh η-cl

-- -- Remark:
-- Notice that in order to prove that up-cl is an isomorphism of
-- categories (with up-inv-cl as its inverse) one needs the
-- modification proposed in 1) and 2) above

-- Embedding of presheaves into closed presheaves
Cl : ℙCxt → ∁
Cl P = cl P , μ-cl

-- The closed presheavs of formulae
⟪_⟫ : Fma → ∁
⟪ A ⟫ = ⟨ A ⟩ , (λ _ h → h id) 

-- The monoidal biclosed structure of ℙCxt
I-psh : ℙCxt
I-psh Γ = Γ ≡ []

_⊗-psh_ : (P Q : ℙCxt) → ℙCxt
(P ⊗-psh Q) Γ = Σ Cxt λ Γ₁ → Σ Cxt λ Γ₂ → Γ ≡ Γ₁ ++ Γ₂ × P Γ₁ × Q Γ₂

_⊸r-psh_ : (P Q : Cxt → Set) → Cxt → Set
(P ⊸r-psh Q) Γ = ∀ Δ → P Δ → Q (Γ ++ Δ)

_⊸l-psh_ : (P Q : Cxt → Set) → Cxt → Set
(P ⊸l-psh Q) Γ = ∀ Δ → P Δ → Q (Δ ++ Γ)

λ-psh : ∀ {P} → I-psh ⊗-psh P ⇒ P
λ-psh _ ([] , Γ , refl , refl , x) = x

ρ-psh : ∀ {P} → P ⇒ P ⊗-psh I-psh
ρ-psh Γ x = Γ , [] , refl , x , refl

α-psh : ∀ {P Q R} → (P ⊗-psh Q) ⊗-psh R ⇒ P ⊗-psh (Q ⊗-psh R)
α-psh _ (_ , Λ , refl , (Γ , Δ , refl , x , y) , z) =
  Γ , Δ ++ Λ , refl , x , Δ , Λ , refl , y , z

curry⊸r : ∀ {P Q R} → (∀ Γ → (P ⊗-psh Q) Γ → R Γ)
  → ∀ Γ → P Γ → (Q ⊸r-psh R) Γ
curry⊸r f Γ x Δ y = f _ (_ , _ , refl , x , y)  

uncurry⊸r : ∀ {P Q R} → (∀ Γ → P Γ → (Q ⊸r-psh R) Γ)
  → ∀ Γ → (P ⊗-psh Q) Γ → R Γ
uncurry⊸r f _ (Γ , Δ , refl , x , y) = f Γ x Δ y  

curry⊸l : ∀ {P Q R} → (∀ Γ → (P ⊗-psh Q) Γ → R Γ)
  → ∀ Γ → Q Γ → (P ⊸l-psh R) Γ
curry⊸l f Γ x Δ y = f _ (_ , _ , refl , y , x)  

uncurry⊸l : ∀ {P Q R} → (∀ Γ → Q Γ → (P ⊸l-psh R) Γ)
  → ∀ Γ → (P ⊗-psh Q) Γ → R Γ
uncurry⊸l f _ (Γ , Δ , refl , x , y) = f Δ y Γ x

-- TODO: prove equations of monoidal biclosed categories

-- cl is a left- and right-strong monad wrt. ⊗-psh (even a commutative
-- monad, perhaps?).
-- Here I also give the equivalent formulation of strength wrt. the
-- internal homs.
mstrR-cl : ∀ {P Q} → cl P ⊗-psh Q ⇒ cl (P ⊗-psh Q)
mstrR-cl _ (Δ , Δ' , refl , k , y) g =
  ⊸rR-inv* Δ' (k (λ {Γ} x → ⊸rR* Δ' (g (Γ , Δ' , refl , x , y))))

mstrL-cl : ∀ {P Q} → P ⊗-psh cl Q ⇒ cl (P ⊗-psh Q)
mstrL-cl _ (Γ , Δ , refl , x , k) g =
  ⊸lR-inv* Γ {Δ} (k (λ y → ⊸lR* Γ (g (_ , _ , refl , x , y))))

cstrR-cl : ∀ {P} (Q : ∁) → cl (P ⊸r-psh Q ¹) ⇒ P ⊸r-psh cl (Q ¹)
cstrR-cl Q Γ h Δ x g = ⊸rR-inv* Δ (h (λ f → ⊸rR* Δ (g (f Δ x))))

cstrL-cl : ∀ {P} (Q : ∁) → cl (P ⊸l-psh Q ¹) ⇒ P ⊸l-psh cl (Q ¹)
cstrL-cl Q Γ h Δ x g = ⊸lR-inv* Δ (h (λ f → ⊸lR* Δ (g (f Δ x))))

-- TODO: prove equations of strength

-- The monoidal biclosed structure of ∁
-- The internal homs lift thanks to strength
⟦I⟧ : ∁
⟦I⟧ = Cl I-psh

_⟦⊗⟧_ : ∁ → ∁ → ∁
P ⟦⊗⟧ Q = Cl (P ¹ ⊗-psh Q ¹)

run⊸r : ∀ {P} (Q : ∁) → cl (P ⊸r-psh Q ¹) ⇒ P ⊸r-psh Q ¹
run⊸r Q Γ h Δ x = run Q _ (cstrR-cl Q Γ h Δ x)

run⊸l : ∀ {P} (Q : ∁) Γ → cl (P ⊸l-psh Q ¹) Γ → (P ⊸l-psh Q ¹) Γ
run⊸l Q Γ h Δ x = run Q _ (cstrL-cl Q Γ h Δ x)

_⟦⊸r⟧'_ : ℙCxt → ∁ → ∁
P ⟦⊸r⟧' Q = P ⊸r-psh Q ¹ , run⊸r Q

_⟦⊸r⟧_ : ∁ → ∁ → ∁
P ⟦⊸r⟧ Q = P ¹ ⟦⊸r⟧' Q

_⟦⊸l⟧'_ : (Cxt → Set) → ∁ → ∁
P ⟦⊸l⟧' Q = P ⊸l-psh Q ¹ , run⊸l Q

_⟦⊸l⟧_ : ∁ → ∁ → ∁
P ⟦⊸l⟧ Q = P ¹ ⟦⊸l⟧' Q
