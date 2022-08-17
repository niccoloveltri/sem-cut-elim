{-# OPTIONS --rewriting #-}

{- PROOF-RELEVANT SEMANTIC CUT ELIMINATION FOR THE LAMBEK CALCULUS -}

module Main where

-- Some utilities 
open import Utilities

-- The sequent calculus presentation of Lambek calculus
open import SequentCalculus

-- The model (a categorification of phase semantics, basically)
open import Model

-- The interpretation function from syntax to semantics
open import Interpretation

-- Okada's property (reflection/reification) providing cut admissibility
open import CutAdmissibility

-- Some equations of cut holding in the model
open import Equations
