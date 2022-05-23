open import Level

module ZKP
  { l₁ l₂ : Level
  }
  where

open import Data.List

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)

open import Function
open import Function.Core


import Relation.Binary.Lattice

import Relation.Binary

-- import Relation.Binary.Properties.HeytingAlgebra

{--

Conal's Recipie:

Proofs can be translated into probabilistic proofs such that:
 - the translated proof has zk property (which needs to be clarified).
 - proof translation is tractable, while reverse translation is intractable.
 - a expanded proof of a proposition is an infinite sequence of propositions
    and their corresponding proofs such that the least the upper bound of the propositions converges
    to the original proposition (in the entailment partial order).
     
look for a natural function that maps regular proofs to probabilistic proofs
or vice versa — whichever way is simpler.
simplicity of definition is crucial.

--} 
-- Op₂ : ∀ a b c → (a → b → c) → a → b → c
-- Op₂ = λ (a) (b) (c) f a b → f a b
-- Op₂ f = f


-- Possible Right hand sides
postulate
  prop : Set
  proof : Set
  
  ptrue      : prop
  pfalse      : prop
  
  _p∧_ : prop → prop → prop
  _p⊢_ : prop → prop → prop
  prove : prop → proof → Set
  ptruth : prop → Set
  _p≤_ : prop → prop → Set
  lub : ∀ {a : Set} → (a → prop) → prop

module ZKP-Plays where
  open import Data.Bool hiding (_≤_)
  open import Relation.Nullary using (¬_)


  zkp₀ = List ( (∃ λ (p : Set) → p ) )

  n≤10 = ∃ λ (n : ℕ) → n ≤ 10

  pr-n≤10 : n≤10
  pr-n≤10 = ⟨ 2 , s≤s (s≤s z≤n) ⟩

  ex-0 : zkp₀
  ex-0 = ⟨ ℕ , 1 ⟩ ∷ ⟨ Bool , true ⟩ ∷ []

  zkp₁ : Set
  zkp₁ = ℕ → prop

  p∀ : (ℕ → prop) → prop
  p∀ = lub

  postulate
    zkp : Set

    prop-to-zkp : (p : prop) → zkp

    get-prop : ℕ → zkp → prop
  
    seed-proposition-dominates : ∀ (p : prop) (n : ℕ) → ptruth (p p⊢ (get-prop n (prop-to-zkp p)))

    -- Completeness: if the statement is true, an honest verifier will be convinced of this fact by an honest prover.
    zkp-completeness : ∀ (p : prop) → ptruth ((p∀ λ n → get-prop n (prop-to-zkp p)) p⊢ p)

    -- Soundness: if the statement is false,
    -- no cheating prover can convince an honest verifier that it is true in the limit.
    -- In this maximally insular (anthony's phrasing) setting, a proof of the false statement
    -- allows any prop to be proven. If you can be convinced using a zkp for false you can be
    -- convinced of anything (anthony's actual phrasing).
    zkp-soundness : ∀ (p : prop) → ptruth ((p∀ λ n → get-prop n (prop-to-zkp pfalse)) p⊢ p)
    -- This formulation is closer to the traditional zkp setting where soundness is interpreted as
    -- the limit of the zkp of a false proposition should not be convincing.
    zkp-soundness₁ : ¬ ptruth (p∀ λ n → get-prop n (prop-to-zkp pfalse))

    -- None of the subpropositions for the zkp of p imply p
    zero-knowledge? : ∀ (p : prop) (n : ℕ) → ¬ ptruth ((get-prop n (prop-to-zkp p) p⊢ p))

    lub-ub-property : ∀ (a : Set) (f : a → prop) (x : a) → f x p≤ (lub f) 
    lub-lb-property : ∀ (a : Set) (f : a → prop) (p : prop) → (∀ (x : a) → f x p≤ p) → lub f p≤ p
