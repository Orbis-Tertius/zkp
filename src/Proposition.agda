module Proposition where

open import Function
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Axiom.Extensionality.Propositional using (∀-extensionality)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Isomorphism as Iso
open Iso
open Iso._≃_



∀-elim : ∀ {A : Set} {B : A → Set}
       → (L : ∀ (x : A) -> B x)
       → (M : A)
       → B M
∀-elim L M = L M


fork : ∀ {A : Set} {B C : A -> Set}
  → (∀ (x : A) → B x) × (∀ (x : A) → C x)
  → (∀ (x : A) → B x × C x)
fork {A} {B} {C} p = λ x → ⟨ proj₁ p x , proj₂ p x ⟩

v-distrib-x : ∀ {A : Set} {B C : A → Set} →
   (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
v-distrib-x = record
  { to = λ p → ⟨ (proj₁ ∘ p), (proj₂ ∘ p) ⟩
  ; from = fork
  ; from∘to = λ x → refl
  ; to∘from = λ y → refl
  } 
