open import Level

module ZKP
  { l₁ l₂ : Level
  }
  where

open import Data.List

import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Binary
open import Function

import Relation.Binary.Lattice
import Relation.Binary.Properties.HeytingAlgebra

{--

Conal's Recipie:

Proofs can be translated into probabilistic proofs such that:
 - the translated proof has zk property (which needs to be clarified).
 - proof translation is tractable, while reverse translation is intractable.
 - a probabilistic proof of a proposition is an infinite sequence of propositions
    and their corresponding proofs such that the least upper bound of the propositions converges
    to the original proposition (in the entailment partial order).
     
look for a natural function that maps regular proofs to probabilistic proofs
or vice versa — whichever way is simpler.
simplicity of definition is crucial.

--}



-- translate : ∀ ₗ (x : Set ₗ) (p : Set ₗ → Set)
--           → p x
--           → ( List ((∃ q : Set ₗ → Set) → q x))
-- translate (l) (x) (p) prop = {!!!}

-- translate' : ∀ ₗ (x : Set ₗ)
--            → x
--            → List ((∃ q : Set ₗ → Set) → q x)
-- translate' l x prop = {!!}


module ⊨⊔-Poset where
  open Poset
  open Relation.Binary.Lattice

  idp : ∀ {c : Set} → (c → c)
  idp = id
  
  -- lub via poset
  ⊢⊔ : ∀ (a : Level) (c : Carrier a l₁ l₂) →  c → c → Set _
  ⊢⊔ = λ a b x x₁ → {! Supremum  x x₁!}
    where open IsHeytingAlgebra 
  infixr 5 ⊢⊔

open ⊨⊔-Poset




-- What is entailment? Where is its partial order?
-- module HeytingAlgebra.Entailment where
--   data _⊢_ : (∀ ₗ l. Set ₗ → Set l → Set (ₗ ⊔ l)) where
--     ⊢ : ⇒ → ⊢

  -- ToDo: Look at Co-Shure Functors

  -- ⊢-preorder : IsPreorder ℓ ℓ ℓ
  -- ⊢-preorder = record
  --   { isPreorder = ⊢-isPreorder
  --   }

  -- ⊢-totalPreorder : IsTotalPreorder 0ℓ 0ℓ 0ℓ
  -- ⊢-totalPreorder = record
  --   { isTotalPreorder = ⊢-isTotalPreorder
  --   }

  -- ⊢-poset : IsPoset 0ℓ 0ℓ 0ℓ
  -- ⊢-poset = record
  --   { isPartialOrder = ⊢-isPartialOrder
  --   }

