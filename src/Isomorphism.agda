module Isomorphism where

open import Function
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning


infix 0 _≃_
record _≃_ (a b : Set) : Set where
  field
    to : a → b
    from : b → a
    from∘to : ∀ (x : a) → from (to x) ≡ x
    to∘from : ∀ (y : b) → to (from y) ≡ y
open _≃_

≃-refl : ∀ {a : Set}
  → a ≃ a
≃-refl = record
  { to = λ{x → x}
  ; from = λ{x → x}
  ; from∘to = λ{x → refl}
  ; to∘from = λ{y -> refl}
  }

≃-sym : ∀ {a b : Set}
  → a ≃ b
  → b ≃ a
≃-sym a2b = record
  { to = from a2b
  ; from = to a2b
  ; from∘to = to∘from a2b
  ; to∘from = from∘to a2b
  } 

≃-trans : ∀ {a b c : Set}
  → a ≃ b
  → b ≃ c
  → a ≃ c
≃-trans a2b b2c = record
  { to = to b2c ∘ to a2b
  ; from = from a2b ∘ from b2c
  ; from∘to = λ{x →
    begin
      (from a2b ∘ from b2c) ((to b2c ∘ to a2b) x)
    ≡⟨⟩
      (from a2b (from b2c (to b2c (to a2b x))))
    ≡⟨ cong (from a2b) (from∘to b2c (to a2b x)) ⟩
      from a2b (to a2b x)
    ≡⟨ from∘to a2b x ⟩
    x ∎
    }
  ; to∘from = λ{y →
    begin
      (to b2c ∘ to a2b) ((from a2b ∘ from b2c) y)
    ≡⟨⟩
      (to b2c (to a2b (from a2b (from b2c y))))
    ≡⟨ cong (to b2c) (to∘from a2b (from b2c y)) ⟩
      to b2c (from b2c y)
    ≡⟨ to∘from b2c y ⟩
    y ∎
    }
  }


module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning
