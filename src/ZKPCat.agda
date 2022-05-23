module ZKPCat where

open import Data.Product
open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality

import Categories.Category
import Categories.Category.Cartesian
import Categories.Category.Cocartesian

-- snd ∘ E† = μ ∘ !
module Abs where
  postulate
    key : Set
    message : Set
    cyphertext : Set

    encrypt : key × message → cyphertext
    -- decrypt : key × cyphertext → message

    D : Set → Set
    return : ∀ {a} → a → D a
    bind : ∀ {a b} → D a → (a → D b) → D b

    dKey : D key
    dMessage : D message

    † : ∀ {a b} → (a → D b) → (b → D a)
  
  lift : ∀ {a b : Set} → (a → b) → (a → D b)
  lift = λ f x → return (f x)

  -- snd ∘ E† = dMessage ∘ !

  lhs : cyphertext → D message
  lhs c = bind († (lift encrypt) c) (return ∘ proj₂)

  rhs : cyphertext → D message
  rhs = const dMessage


  postulate
    comm-sqr : ∀ (c : cyphertext) → lhs c ≡ rhs c
    ×-message : message → message → message
    ×-cypher : cyphertext → cyphertext → cyphertext

-- module EncryptIsMessageHomomorphism where
--   postulate
--     enc-preserves-× : ∀ (a b : message) (k : key)
--       → (encrypt ( k , (×-message a b))) ≡ ×-cypher (encrypt ( k , a )) (encrypt ( k , b )) 
    
module MessageCat where
  open Categories.Category
  open Categories.Category.Cartesian
  open import Relation.Binary using (Rel)
  open import Agda.Primitive using (lzero)
  postulate
    messageKind : Set
    _m-×_ : messageKind → messageKind → messageKind
    _m-+_ : messageKind → messageKind → messageKind
    m-top : messageKind
    m-bot : messageKind
    m-⇒ : Rel messageKind lzero
  instance
    mcat : Category _ _ lzero
    mcat = record
             { Obj = messageKind
             ; _⇒_ = m-⇒
             ; _≈_ = _≡_
             ; id = {!!}
             ; _∘_ = {!!}
             ; assoc = {!!}
             ; sym-assoc = {!!}
             ; identityˡ = {!!}
             ; identityʳ = {!!}
             ; identity² = {!!}
             ; equiv = {!!}
             ; ∘-resp-≈ = {!!}
             }
    
