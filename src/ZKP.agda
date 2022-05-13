open import Level

module ZKP
  { l₁ l₂ : Level
  }
  where

open import Data.List

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
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



module ⊨⊔-Poset where
  open Relation.Binary.Lattice
  open Relation.Binary

  zkp = List ( ∀ (p : Set) (q : Set → Set)  → q p )

  data Id : (x : Set) → Set where
    id' : ∀ x → x → (Id x)

  _⊨⊔_ : (p : Set l₁) (q : zkp) → zkp → p
    -- _⊢_ : p → q p Id → p ⊨⊔ q 
  _⊨⊔_  (p)  = foldl ? ?
    where open IsHeytingAlgebra
          h : IsHeytingAlgebra _≡_ _≤_ _⊎_ _×_ _⇒_ ⊤ ⊥
          h = ?
          lub : zkp 
          lub = ?
  infixr 5 _⊨⊔_ -- _⊢_

open ⊨⊔-Poset



translate : ∀ (x : Set) ( l : zkp) → x ⊨⊔ l → x
translate (p) (l) = λ x → {! !}



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

