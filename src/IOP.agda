open import Level using (Level; _⊔_)
module IOP { ℓₚ ℓₘ : Level } where


-- Interactive Oracle Proofs

module InteractiveProof (p : Set ℓₚ) (m : Set ℓₘ) where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Bool
  open import Data.Sum
  open import Data.Product
  open import Function hiding (_↔_)

  data Verification : {i : ℕ} → Set ℓₘ where
    terminal : Bool → Verification {zero}
    nextStep : ∀ {n : ℕ} → m × (m → Verification {suc n}) → Verification {n}

  onV : ∀ {ℓx : Level} {a : Set ℓx} {i : ℕ}
    → (Bool → a) → (m × (m → Verification {i})) → a → Verification {suc i} → a
  onV = {!!}

  data Argument : Set ℓₘ where
    arg : m × (m → Argument) → Argument

  unarg : Argument → m × (m → Argument)
  unarg (arg a) = a
  msg : Argument → m
  msg = proj₁ ∘ unarg
  narg : Argument → (m → Argument)
  narg = proj₂ ∘ unarg


  pₙ : m → Argument → m
  pₙ m a = msg (narg a m)

  Prover : ∀ {ℓ} → (p : Set ℓ) → Set (ℓₘ ⊔ ℓ)
  Prover p = p → Argument
  
  Verifier : ∀ {ℓ} {k : ℕ} → (p : Set ℓ) → Set (ℓₘ ⊔ ℓ)
  Verifier {ℓ} {k} p = p → (m → Verification {k})

  data IP {k : ℕ} (p : Set ℓₚ) : Set (ℓₚ ⊔ ℓₘ) where
    _↔_ : Prover p → Verifier {k = k} p → IP p 

  ip : ∀ {k : ℕ} → IP {k} p → p → Bool
  ip (pr ↔ vr) x = let ia = pr x
    in oneStep ia (vr x (msg ia))
    where
      oneStep : Argument → Verification → Bool
      oneStep _ (terminal x) = x
      oneStep a (nextStep ( mv , cv ) ) = let
              ( pᵢ , aᵢ ) = unarg (narg a mv)
              in onV id (λ ( vₘ , vf ) → oneStep (aᵢ vₘ) (vf (msg (aᵢ vₘ)))) (cv pᵢ)

open InteractiveProof public 



-- open import Relation.Binary

-- module IP (Prog : Set) (IO : Set) (M : Set)
--   (a : (REL Prog IO 0ℓ)) where
  
--   record P : Set where
--     field
--       Λ : M
--       encode : Decidable a → M
--       process : M → M → M

-- open IP public
