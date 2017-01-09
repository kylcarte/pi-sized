
module Pi.Metric where

open import Prelude as ℙ
open import Data.Integer
open import Pi
open import Pi.Iso

variance : ∀ {A B}
         → {f g : A ↔ B} → f ≅ g
         → ΔSize
variance {f = f} {g} _ = Δsize f g

abstract : ∀ {A B C}
         → (A ↔ B
         → (ΔSize → ΔSize)
