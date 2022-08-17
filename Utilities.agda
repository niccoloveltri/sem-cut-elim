{-# OPTIONS --rewriting #-}

module Utilities where

open import Data.List
open import Relation.Binary.PropositionalEquality

{-# BUILTIN REWRITE _≡_ #-}

-- Unitality and associativity of list concatenation

++ru : {X : Set} → (xs : List X) → xs ++ [] ≡ xs
++ru [] = refl
++ru (x ∷ xs) = cong (_∷_ x) (++ru xs) 

++ass : {X : Set} → (xs : List X) → {ys zs : List X} → 
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++ass [] = refl
++ass (x ∷ xs) = cong (_∷_ x) (++ass xs)

{-# REWRITE ++ass #-}
{-# REWRITE ++ru #-}

-- We used Agda rewriting feature to turn the propositional equalities
-- ++ass and ++ru into judgemental equalities. This is not necessary,
-- but it makes many things easier.

-- Function extensionality

postulate
  funext : {A : Set}{B : A → Set} {f g : (x : A) → B x}
    → (∀ x → f x ≡ g x) → f ≡ g
  ifunext : {A : Set}{B : A → Set} {f g : {x : A} → B x}
    → (∀ x → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g


