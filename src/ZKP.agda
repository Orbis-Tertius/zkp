open import Level

module ZKP
  { l₁ l₂ : Level
  }
  where

open import Data.List

import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


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
--Op₂ f = f

data fn (a b : Set) : Set where
  fₙ : a → b → fn a b

module ⊨⊔-Poset where
  open Poset
  open Relation.Binary.Lattice

  data _⊢_ (a : Set) (b : Set) : Set where
    e : (a → b) → (a ⊢ b)


  idp : ∀ {c : Set} → (c → c)
  idp = id


  ⊨⊔ : ∀ (p : Set) → p × p → p
  ⊨⊔  (p) ⟨ p' , p'' ⟩ = lub p' p''
    where open IsHeytingAlgebra
          lub = supremum (IsHeytingAlgebra _≡_ _⊢_ (_⊎_) (_×_) (_⇒_) ⊤ ⊥)
  infixr 5 ⊨⊔

open ⊨⊔-Poset


translate : ∀ (x : Set) ( l : (List ((∃ q : Set) → q))) 
            →  x ⊨⊔ l
translate (p) (l) prop = {!!}


translate' : ∀ ₗ (x : Set ₗ)
           → x
           → List ((∃ q : Set ₗ) → q)
translate' l x prop = {!!}


-- module Conjunction where
--   open import Isomorphism
--   data _×_ (A : Set l₁) (B : Set l₂) : Set (l₁ ⊔ l₂) where
--     ⟨_,_⟩ : A → B → A × B

--   infixr 2 _×_

--   proj₁ : ∀ {A : Set l₁} {B : Set l₂} → A × B → A
--   proj₁ ⟨ x , y ⟩ = x

--   proj₂ : ∀ {A : Set l₁} {B : Set l₂} → A × B → B
--   proj₂ ⟨ x , y ⟩ = y

--   η-× : ∀ {A : Set l₁} {B : Set l₂} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
--   η-× ⟨ x , y ⟩ = refl

--   -- ×-comm : ∀ {A : Set l₁} {B : Set l₂} → A × B ≃ B × A
--   -- ×-comm =
--   --   record
--   --     { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
--   --     ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
--   --     ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
--   --     ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
--   --     }

-- module Top where
--   open import Isomorphism
--   data ⊤ : Set where
--     tt : ⊤

--   η-⊤ : ∀ (w : ⊤) → tt ≡ w
--   η-⊤ tt = refl

--   ⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
--   ⊤-identityˡ =
--     record
--       { to      = λ{ ⟨ tt , x ⟩ → x }
--       ; from    = λ{ x → ⟨ tt , x ⟩ }
--       ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
--       ; to∘from = λ{ x → refl }
--       }


-- module Disjunction where






-- What is entailment? Where is its partial order?
module Entailment where
  open Poset
  

  -- ToDo: Look at Co-Shure Functors

  -- ⊢-isPreorder = ?
  -- ⊢-isTotalPreorder = ?
  -- ⊢-isPartialOrder = ?
    
  -- ⊢-preorder : IsPreorder ⊢ l₁ l₂
  -- ⊢-preorder = record
  --   { isPreorder = ⊢-isPreorder
  --   }

  -- ⊢-totalPreorder : IsTotalPreorder ⊢ l₁ l₂
  -- ⊢-totalPreorder = record
  --   { isTotalPreorder = ⊢-isTotalPreorder
  --   }

  -- ⊢-poset : Poset ⊢ l₁ l₂
  -- ⊢-poset = record
  --   { isPartialOrder = ⊢-isPartialOrder
  --   }

