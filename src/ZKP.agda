open import Level

module ZKP where

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
-- postulate
--   A : Set
--   p : A
--   ptrue : A
--   pfalse : A
--   _p∧_ : A → A → A
--   _p⊢_ : A → A → A
--   prove : A → A → Set
--   ptruth : A → Set
--   _p≤_ : A → A → Set
--   lub : ∀ {a : Set} → (a → A) → A


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
  open import Relation.Binary.Lattice using (Supremum; IsJoinSemilattice)


  _⊨_ : ∀ {ℓ : Level} → Rel (Set ℓ) ℓ
  _⊨_ b a = a → b


  ⊨-isPreorder : ∀ {ℓ : Level} → IsPreorder _⇔_ _⊨_
  ⊨-isPreorder {ℓ} = record
    { isEquivalence = ⇔-isEquivalence {ℓ}
    ; reflexive = Equivalence.from
    ; trans = λ x x₁ x₂ → x (x₁ x₂)
    }

  ⊨-isPartialOrder : ∀ {ℓ : Level} → IsPartialOrder _⇔_ _⊨_
  ⊨-isPartialOrder {ℓ} = record
    { isPreorder = ⊨-isPreorder {ℓ}
    ; antisym = λ fg gf → record
      { to = gf
      ; from = fg
      ; to-cong = λ ≈-fg → cong gf ≈-fg
      ; from-cong = λ ≈-gf → cong fg ≈-gf
      } 
    } where
        open Relation.Binary.PropositionalEquality

  ⊨-lub : ∀ {ℓ : Level} → Supremum (_⊨_ {ℓ}) _×_
  ⊨-lub {ℓ} = λ x y → ⟨ proj₁ , ⟨ proj₂ , (λ z z₁ z₂ z₃ → ⟨ z₁ z₃ , z₂ z₃ ⟩) ⟩ ⟩

  ⊨-joinSL : {ℓ : Level} → IsJoinSemilattice _⇔_ (_⊨_ {ℓ}) _×_
  ⊨-joinSL = record
    { isPartialOrder = ⊨-isPartialOrder
    ; supremum = ⊨-lub
    }
    
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

  zkp : Set _
  zkp = ∀ (A : Set) → (ℕ → A)

  -- p∀ : ∀ (A : Set) → (ℕ → A) → A
  -- p∀ = λ A z → z ℕ.zero

  -- prop-to-zkp : ∀ (A : Set) → (p : A) → zkp
  -- prop-to-zkp = λ A p A₁ x → {!!}

  get-prop : ∀ (A : Set) → ℕ → zkp → A
  get-prop = λ A x x₁ → x₁ A x

  -- seed-proposition-dominates : ∀ (A : Set)(p : A) (n : ℕ)
  --   → true ≡ (p ⊨ (get-prop n (prop-to-zkp p)))
  -- seed-proposition-dominates = ?

  -- -- Completeness: if the statement is true, an honest verifier will be convinced of this fact by an honest prover.
  -- zkp-completeness : ∀ (A : Set)(p : A) → true ((p∀ λ n → get-prop n (prop-to-zkp p)) ⊨ p)
  -- zkp-completeness = ?
  
  -- -- Soundness: if the statement is false,
  -- -- no cheating prover can convince an honest verifier that it is true in the limit.
  -- -- In this maximally insular (anthony's phrasing) setting, a proof of the false statement
  -- -- allows any prop to be proven. If you can be convinced using a zkp for false you can be
  -- -- convinced of anything (anthony's actual phrasing).
  -- zkp-soundness : ∀ (A : Set)(p : A) → true ((p∀ λ n → get-prop n (prop-to-zkp false)) ⊨ p)
  -- zkp-soundness = ?
  
  -- -- This formulation is closer to the traditional zkp setting where soundness is interpreted as
  -- -- the limit of the zkp of a false proposition should not be convincing.
  -- zkp-soundness₁ : ¬ true (p∀ λ n → get-prop n (prop-to-zkp false))
  -- zkp-soundness₁ = ?
  
  -- -- None of the subpropositions for the zkp of p imply p
  -- zero-knowledge? : ∀ (A : Set)(p : A) (n : ℕ) → ¬ true ((get-prop n (prop-to-zkp p) ⊨ p))
  -- zero-knowledge? = ?

open Denotation
