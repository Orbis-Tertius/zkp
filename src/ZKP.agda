open import Level

module ZKP where

open import Data.List

open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Product
  using (_×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty

open import Function hiding (Equivalence)



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



module ⊨-Structures where
  open import Relation.Unary using (Pred; Universal; _⟨×⟩_)

  data PList {ℓ} {A : Set ℓ} : Set (Level.suc ℓ) where
    [_]ₚ : PList {ℓ} {A}
    _∷ₚ_ : ∀ {X : Set ℓ} → Pred X ℓ → PList {ℓ} {A} → PList {ℓ} {A}

  foldlₚ : ∀ {ℓ} {A : Set ℓ}
    -- → ({X : Set ℓ} {Y : Set ℓ} → Pred X ℓ → Pred Y ℓ → Pred (X × Y) ℓ)
    → PList {ℓ} {A}
    → A
  foldlₚ [_]ₚ = {!!}
  foldlₚ (x ∷ₚ ps) = {!!}
  
  zkp : ∀ {ℓ} {A : Set ℓ} → ({X : Set ℓ} {P : Pred X ℓ} → Universal P) → PList {ℓ} {A} → A 
  zkp {ℓ} {A} f ps = {!!} -- (foldlₚ ( _⟨×⟩_ ) ps )
open ⊨-Structures


module ⊣-Structures where
  open import Relation.Binary using (Rel; REL; IsPreorder; IsPartialOrder;
                                    IsEquivalence; Setoid; _Preserves_⟶_;
                                    Maximum;
                                    Minimum
                                    )
  open import Function.Bundles using (_⇔_; Equivalence; Func)
  open import Function.Related.Propositional
    using (Related; K-refl;
          K-trans; _∼[_]_;
          SK-isEquivalence; SK-setoid;
          equivalence; implication)
  open import Function.Properties.Equivalence using (⇔-isEquivalence)
  open import Relation.Binary.Lattice using (Infimum; Supremum;
                                            IsLattice; IsBoundedLattice;
                                            IsDistributiveLattice;
                                            IsHeytingAlgebra;
                                            IsBooleanAlgebra)

  _⊣_ : ∀ {ℓ : Level} → Rel (Set ℓ) _
  _⊣_ b a = a → b

  _⊢_ : ∀ {ℓ : Level} → Rel (Set ℓ) _
  _⊢_ a b = a → b


  ⊣-isPreorder : ∀ {ℓ : Level} → IsPreorder _⇔_ _⊣_
  ⊣-isPreorder {ℓ} = record
    { isEquivalence = ⇔-isEquivalence {ℓ}
    ; reflexive = Equivalence.from
    ; trans = λ z z₁ z₂ → z (z₁ z₂)
    }

  ⊣-isPartialOrder : ∀ {ℓ : Level} → IsPartialOrder _⇔_ _⊣_
  ⊣-isPartialOrder {ℓ} = record
    { isPreorder = ⊣-isPreorder {ℓ}
    ; antisym = λ fg gf → record
      { to = gf
      ; from = fg
      ; to-cong = λ ≈-fg → cong gf ≈-fg
      ; from-cong = λ ≈-gf → cong fg ≈-gf
      } 
    } where
        open Relation.Binary.PropositionalEquality

  ⊣-sup : ∀ {ℓ : Level} → Supremum (_⊣_ {ℓ}) _×_
  ⊣-sup = λ x y → ⟨ proj₁ , ⟨ proj₂ , (λ z z₁ z₂ z₃ → ⟨ z₁ z₃ , z₂ z₃ ⟩) ⟩ ⟩

  ⊣-inf : ∀ {ℓ : Level} → Infimum (_⊣_ {ℓ}) _⊎_
  ⊣-inf = λ A B → ⟨ inj₁ , ⟨ inj₂ , (λ Z za zb aOrb → case-⊎ za zb aOrb ) ⟩ ⟩

  ⊣-Lattice : ∀ {ℓ : Level} → IsLattice _⇔_ _⊣_ _×_ _⊎_
  ⊣-Lattice {ℓ} = record
    { isPartialOrder = ⊣-isPartialOrder {ℓ}
    ; supremum = ⊣-sup
    ; infimum = ⊣-inf
    }

  ⊣-lub : {ℓ : Level} {x y z : Set ℓ} → x ⊣ z → y ⊣ z → (x × y) ⊣ z
  ⊣-lub {ℓ} = IsLattice.∨-least (⊣-Lattice {ℓ})

  ⊢-isPreorder : ∀ {ℓ : Level} → IsPreorder _⇔_ _⊢_
  ⊢-isPreorder {ℓ} = record
    { isEquivalence = ⇔-isEquivalence {ℓ}
    ; reflexive = Equivalence.to
    ; trans = λ z z₁ z₂ → z₁ (z z₂)
    }

  ⊢-isPartialOrder : ∀ {ℓ : Level}
    → IsPartialOrder _⇔_ _⊢_
  ⊢-isPartialOrder {ℓ} = record
    { isPreorder = ⊢-isPreorder {ℓ}
    ; antisym = λ fg gf → record
      { to = fg
      ; from = gf
      ; to-cong = λ ≈-fg → cong fg ≈-fg
      ; from-cong = λ ≈-gf → cong gf ≈-gf
      } 
    } where
        open Relation.Binary.PropositionalEquality

  ⊢-lub : {ℓ : Level} {x y z : Set ℓ} → x ⊢ z → y ⊢ z → (x × y) ⊢ z
  ⊢-lub {ℓ} = λ _ z z₁ → z (proj₂ z₁)
      
open ⊣-Structures public


module Denotation where
  open import Data.Bool hiding (_≤_)
  open import Relation.Nullary using (¬_)
  open import Relation.Unary

  zkp₀ : ∀ {ℓ} → Set (Level.suc ℓ) 
  zkp₀ {ℓ} = ∃ λ (p : Set ℓ) → p
  
  -- prop = ∀ {ℓ} {A : Set ℓ} → Pred A ℓ

  -- zkp' : ∀ {ℓ} {A : Set ℓ} → Pred A ℓ → Set ℓ
  -- zkp' {ℓ} {A} P = (Π[ P ] → A)

  -- verify : ∀ {ℓ} {A : Set ℓ} (p : Pred A ℓ) → zkp' p
  -- verify = λ p x → {!!}
  -- propositions = ℕ → (∀ {ℓ} {A : Set ℓ} → p {ℓ} {A})
  
  -- verify : ∀ {A : Set} → A → propositions → Set  
  -- verify = {!!}

  fin-zkp = List (zkp₀ {0ℓ})

  --fin-zkp' = List (prop)

  -- lubs : fin-zkp → zkp₀
  -- lubs l = foldr ⊢-lub _ l
  --   where
  --     go : ∀ {ℓ} {a b c : Set ℓ} → (b ⊣ a) → (c ⊣ a) → (b × c) ⊣ a
  --     go = ⊣-lub


  n≤10 = ∃ λ (n : ℕ) → n ≤ 10
  
  pr-n≤10 : n≤10
  pr-n≤10 = ⟨ 2 , s≤s (s≤s z≤n) ⟩

  ex-0 : fin-zkp
  ex-0 = ⟨ ℕ , 1 ⟩ ∷ ⟨ Bool , true ⟩ ∷ ⟨ n≤10 , pr-n≤10 ⟩ ∷ []

  

  -- lubs : List (zkp₀) → _
  -- lubs : _ 


  -- zkp : ∀ {A : Set} → ℕ → A
  -- zkp = {!!}
  -- prop-to-zkp : ∀ {ℓ} (A : Set ℓ) → zkp
  -- prop-to-zkp = λ A x → {!!}

  -- get-prop : ∀ {A : Set} → ℕ → zkp → A
  -- get-prop = λ i p → p i

  -- zkp-to-prop : zkp → 

  -- seed-proposition-dominates : ∀ (A : Set)(p : A) (n : ℕ)
  --   → (get-prop n (λ _ → A) (prop-to-zkp p) ⊨ p)
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

open Denotation public


module Yoneda where

  hom : ∀ {ℓ} (A : Set ℓ) (P Q : A → Set ℓ) → Set _
  hom (A) (P) (Q) = (x : A) → (P x → Q x)


open Yoneda public
