open import Level using (Level; _⊔_)
module IOP { ℓₚ ℓₘ : Level } where

open import Data.Product
open import Data.List
--open import Data.Nat
open import Data.Bool
open import Data.Sum
open import Function hiding (_↔_)

-- Interactive Oracle Proofs


module InteractiveProof (p : Set ℓₚ) (m : Set ℓₘ) where

  data Verification : Set ℓₘ where
    terminal : Bool → Verification
    nextStep : (m × (m → Verification)) → Verification

  onV : ∀ {ℓx : Level} {a : Set ℓx}
    → (Bool → a) → ((m × (m → Verification)) → a) → Verification → a
  onV r l (terminal x) = r x
  onV r l (nextStep x) = l x

  data Argument : Set ℓₘ where
    arg : m × (m → Argument) → Argument

  unarg : Argument → m × (m → Argument)
  unarg (arg a) = a
  msg : Argument → m
  msg (arg x) = proj₁ x
  narg : Argument → (m → Argument)
  narg (arg x) = proj₂ x


  pₙ : m → Argument → m
  pₙ m a = msg (narg a m)

  Prover : ∀ {ℓ} → (p : Set ℓ) → Set (ℓₘ ⊔ ℓ)
  Prover p = p → Argument
  
  Verifier : ∀ {ℓ} → (p : Set ℓ) → Set (ℓₘ ⊔ ℓ)
  Verifier p = p → (m → Verification)

  data IP (p : Set ℓₚ) : Set (ℓₚ ⊔ ℓₘ) where
    _↔_ : Prover p → Verifier p → IP p 

  ip : IP p → p → Bool
  ip (pr ↔ vr) x = let ia = pr x
    in oneStep ia (vr x (msg ia))
    where
      oneStep : Argument → Verification → Bool
      oneStep _ (terminal x) = x
      oneStep a (nextStep ( mv , cv ) ) = let
              ( pᵢ , aᵢ ) = unarg (narg a mv)
              in onV id (λ ( vₘ , vf ) → oneStep (aᵢ vₘ) (vf (msg (aᵢ vₘ)))) (cv pᵢ)

open InteractiveProof public 
