module PolyP where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality 
open import Data.Nat
open import Data.Unit

Unop : Set → Set
Unop A = A → A

Binop : Set → Set
Binop A = A → A → A


data Poly (A : Set) : Set where
  Ind : Poly A
  Lit : A → Poly A
  _:+:_ : Binop (Poly A)
  _:×:_ : Binop (Poly A)



foldP : {A B : Set}
  → B
  → (A → B)
  → Binop B × Binop B
  → Poly A
  → B
foldP x f ( _⊕_ , _⊗_ ) Ind = x
foldP x f ( _⊕_ , _⊗_ ) (Lit y) = f y
foldP x f ( _⊕_ , _⊗_ ) (ps :+: ps₁) = foldP x f ( _⊕_ , _⊗_ ) ps
                                ⊕ foldP x f ( _⊕_ , _⊗_ ) ps₁
foldP x f ( _⊕_ , _⊗_ ) (ps :×: ps₁) = foldP x f ( _⊕_ , _⊗_ ) ps
                                ⊗ foldP x f ( _⊕_ , _⊗_ ) ps₁


record Ring (A : Set) : Set where
  field
    _⊕_ : Binop A
    _⊗_ : Binop A
    :0 : A
    :1 : A
    neg : A → A

-- ring-ranged functions are rings
ring→ : ∀ {A B} → Ring B → Ring (A → B)
ring→ r = record
  { _⊕_ = λ f g x → (f x) ⊕ (g x)
  ; _⊗_ = λ f g x → (f x) ⊗ (g x)
  ; :0 = const :0
  ; :1 = const :1
  ; neg = neg ∘_
  }
  where
    open Ring (r)

-- Evaluating a univariate polynomial over a ring
sem₁ : ∀ {A} → Ring A → Poly A → A → A
sem₁ r = foldP id const (( _⊕_ ) , ( _⊗_ ))
  where
    open Ring (ring→ r)

-- polynomials over rings are rings
ringP : ∀ {A} → Ring A → Ring (Poly A)
ringP r = record
  { _⊕_ = _:+:_
  ; _⊗_ = _:×:_
  ; :0 = Lit :0
  ; :1 = Lit :1
  ; neg = Lit (neg :1) :×:_
  } where open Ring (r)

-- Evaluate a bivariate polynomial over a ring
sem₂ : ∀ {A} → Ring A → Poly (Poly A) → Poly A → A → A
sem₂ r pp p a = sem₁ r (sem₁ (ringP r) pp p) a


litDist : ∀ {A} → Poly (Poly A) → Poly (Poly A)
litDist {A} p = foldP Ind (foldP (Lit Ind) (Lit ∘ Lit) x) x p 
  where
    x : ∀ {X} → Binop (Poly X) × Binop (Poly X)
    x = (_:+:_ , _:×:_ )

-- th-lit-dist : ∀ {A} (e : Poly (Poly A)) (r : Ring A)
--   → sem₂ r (litDist e) ≡ sem₂ r e  
-- th-lit-dist Ind r = refl
-- th-lit-dist (Lit e) r = {!!}
-- th-lit-dist (e :+: e₁) r = {!!}
-- th-lit-dist (e :×: e₁) r = {!!}



-- n-dimensional polynomials are n-variate polynomials
PolyN : Set → ℕ → Set
PolyN A zero = A
PolyN A (suc n) = Poly (PolyN A n) 

-- Descending Chain
DChain : Set → ℕ → Set
DChain A zero = ⊤
DChain A (suc n) = PolyN A n × DChain A n

-- multi-dimensional polynomials are a ring
ringP* : ∀ {A} → Ring A → ∀ n → Ring (PolyN A n)
ringP* r zero = r
ringP* r (suc n) = ringP (ringP* r n)


-- Evaluating a multivariate polynomial over a ring
semₙ : ∀ {A} → Ring A → (n : ℕ) → PolyN A n → DChain A n → A
semₙ r zero x tt = x
semₙ r (suc n) e (t , es) = semₙ r n (sem₁ (ringP* r n) e t) es

-- rotation
