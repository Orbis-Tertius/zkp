open import Level

module ZKP where

open import Data.List

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)

import Function hiding (Equivalence)

-- import Relation.Binary.Properties.HeytingAlgebra

{--

Conal's Recipie:

Proofs can be translated into probabilistic proofs such that:
 - the translated proof has zk property (which needs to be clarified). --  zero-knowledge?
 - proof translation is tractable, while reverse translation is intractable. -- accounted for by the infinite sequence
 - a expanded proof of a proposition is an infinite sequence of propositions
    and their corresponding proofs such that the least the upper bound of the propositions converges
    to the original proposition (in the entailment partial order).
     
look for a natural function that maps regular proofs to expanded proofs
or vice versa — whichever way is simpler.
simplicity of definition is crucial.

--} 
-- Op₂ : ∀ a b c → (a → b → c) → a → b → c
-- Op₂ = λ (a) (b) (c) f a b → f a b
-- Op₂ f = f


-- Possible Right hand sides
postulate
  A : Set
  proof : A
  ptrue : A
  pfalse : A
  _p∧_ : A → A → A
  _p⊢_ : A → A → A
  prove : A → A → Set
  ptruth : A → Set
  _p≤_ : A → A → Set
  lub : ∀ {a : Set} → (a → A) → A


module ⊨-PartialOrder where
  open import Relation.Binary using (Rel; IsPreorder; IsPartialOrder;
                                    IsEquivalence; Setoid; _Preserves_⟶_)
  open import Function.Bundles using (_⇔_; Equivalence; Func)
  open import Function.Related.Propositional
    using (Related; K-refl;
          K-trans; _∼[_]_;
          SK-isEquivalence; SK-setoid;
          equivalence; implication)
  open import Function.Properties.Equivalence using (⇔-isEquivalence)

  _⊨_ : ∀ {ℓ : Level} → Rel (Set ℓ) ℓ
  _⊨_ a b = a → b


  ⊨-isPreorder : ∀ {ℓ : Level} → IsPreorder _⇔_ _⊨_
  ⊨-isPreorder {ℓ} = record
    { isEquivalence = ⇔-isEquivalence {ℓ}
    ; reflexive = Equivalence.to
    ; trans = λ z z₁ z₂ → z₁ (z z₂)
    }

  ⊨-isPartialOrder : ∀ {ℓ : Level} → IsPartialOrder _⇔_ _⊨_
  ⊨-isPartialOrder {ℓ} = record
    { isPreorder = ⊨-isPreorder {ℓ}
    ; antisym = λ fg gf → record
      { to = fg
      ; from = gf
      ; to-cong = λ {i} {j} ≈-fg → cong fg ≈-fg
      ; from-cong = λ {i} {j} ≈-gf → cong gf ≈-gf
      } 
    } where
        open Relation.Binary.PropositionalEquality
            
open ⊨-PartialOrder public



module Denotation where
  open import Data.Bool hiding (_≤_)
  open import Relation.Nullary using (¬_)
  

  zkp₀ = List ( (∃ λ (p : Set) → p ) )

  n≤10 = ∃ λ (n : ℕ) → n ≤ 10

  pr-n≤10 : n≤10
  pr-n≤10 = ⟨ 2 , s≤s (s≤s z≤n) ⟩

  ex-0 : zkp₀
  ex-0 = ⟨ ℕ , 1 ⟩ ∷ ⟨ Bool , true ⟩ ∷ ⟨ n≤10 , pr-n≤10 ⟩ ∷ []

  zkp₁ : Set
  zkp₁ = ℕ → A

  p∀ : (ℕ → A) → A
  p∀ = lub

  postulate
    zkp : Set

    prop-to-zkp : (p : A) → zkp

    get-prop : ℕ → zkp → A
  
    seed-proposition-dominates : ∀ (p : A) (n : ℕ) → ptruth (p p⊢ (get-prop n (prop-to-zkp p)))

    -- Completeness: if the statement is true, an honest verifier will be convinced of this fact by an honest prover.
    zkp-completeness : ∀ (p : A) → ptruth ((p∀ λ n → get-prop n (prop-to-zkp p)) p⊢ p)

    -- Soundness: if the statement is false,
    -- no cheating prover can convince an honest verifier that it is true in the limit.
    -- In this maximally insular (anthony's phrasing) setting, a proof of the false statement
    -- allows any prop to be proven. If you can be convinced using a zkp for false you can be
    -- convinced of anything (anthony's actual phrasing).
    zkp-soundness : ∀ (p : A) → ptruth ((p∀ λ n → get-prop n (prop-to-zkp pfalse)) p⊢ p)
    -- This formulation is closer to the traditional zkp setting where soundness is interpreted as
    -- the limit of the zkp of a false proposition should not be convincing.
    zkp-soundness₁ : ¬ ptruth (p∀ λ n → get-prop n (prop-to-zkp pfalse))

    -- None of the subpropositions for the zkp of p imply p
    zero-knowledge? : ∀ (p : A) (n : ℕ) → ¬ ptruth ((get-prop n (prop-to-zkp p) p⊢ p))

    lub-ub-property : ∀ (a : Set) (f : a → A) (x : a) → f x p≤ (lub f) 
    lub-lb-property : ∀ (a : Set) (f : a → A) (p : A) → (∀ (x : a) → f x p≤ p) → lub f p≤ p

open Denotation
