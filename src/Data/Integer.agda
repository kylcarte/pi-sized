
module Data.Integer where

open import Prelude as P
  hiding
    ( neg
    ; pos
    ; negsuc
    )
  renaming
    ( _⊔_ to lmax
    )

pred : Nat → Nat
pred zero    = zero
pred (suc x) = x

infixl 5 _⊔_
_⊔_ : Nat → Nat → Nat
zero  ⊔   y   = y
suc x ⊔ zero  = suc x
suc x ⊔ suc y = suc (x ⊔ y)
{-# INLINE _⊔_ #-}

data Integer : Set where
  pos negsuc : Nat → Integer

pattern zero! = pos zero

neg : Nat → Integer
neg zero    = pos zero
neg (suc x) = negsuc x

negateℤ : Integer → Integer

negateℤ (pos zero)    = pos zero
negateℤ (pos (suc x)) = negsuc x
negateℤ (negsuc x)    = pos (suc x)

infixl 6 _+ℤ_ _-ℤ_
infixl 7 _*ℤ_
_+ℤ_ _-ℤ_ _*ℤ_ : Integer → Integer → Integer

pos    x       +ℤ pos    y       = pos (x + y)
pos    zero    +ℤ y              = y
pos    (suc x) +ℤ negsuc zero    = pos x
pos    (suc x) +ℤ negsuc (suc y) = pos x +ℤ negsuc y
negsuc x       +ℤ pos zero       = negsuc x
negsuc zero    +ℤ pos (suc y)    = pos y
negsuc (suc x) +ℤ pos (suc y)    = negsuc x +ℤ pos y
negsuc x       +ℤ negsuc y       = negsuc (suc (x + y))

x -ℤ y = x +ℤ negateℤ y

pos zero       *ℤ y = pos zero
pos (suc x)    *ℤ y = pos x *ℤ y +ℤ y
negsuc zero    *ℤ y = negateℤ y
negsuc (suc x) *ℤ y = negsuc x *ℤ y -ℤ y

infixl 6 _-ℕ_
_-ℕ_ : Nat → Nat → Integer
zero  -ℕ y     = neg y
x     -ℕ zero  = pos x
suc x -ℕ suc y = x -ℕ y
{-# INLINE _-ℕ_ #-}

instance
  NumberInteger : Number Integer
  NumberInteger = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ x → pos x
    }

  NegativeInteger : Negative Integer
  NegativeInteger = record
    { Constraint = λ _ → ⊤
    ; fromNeg    = λ x → neg x
    }

  SubtractiveInteger : Subtractive Integer
  SubtractiveInteger = record
    { _-_    = _-ℤ_
    ; negate = negateℤ
    }

  SemiringInteger : Semiring Integer
  SemiringInteger = record
    { zro = 0
    ; one = 1
    ; _+_ = _+ℤ_
    ; _*_ = _*ℤ_
    }

{-
record Size : Set where
  field
    width length : Nat
open Size public

size : ∀ {A B} → A ↔ B → Size

-- Case: Axiom -------------------------
size {A} {B} [ _ ] = record
  { width = space A ⊔ space B
  ; length  = 1
  }

-- Case: Identity ----------------------
size {A} id = record
  { width = space A
  ; length  = 0
  }

-- Case: Inverse -----------------------
size (f ⁻¹) = record
  { width = f.width
  ; length  = f.length
  }
  where
  module f = Size (size f)

-- Case: Composition -------------------
{-
alternative temporal-spatial arrangements for _∘_:
i = space(f)
j = time(f)
k = space(g)
l = time(g)
run in parallel ↦ space(g ∘ f) = space(f) + space(g) (i + k) × (j ⊔ l) = run in parallel
(i ⊔ k) × (j + l) = run in sequence
(i + k) × (j + l) = run disjointly
-}
size (g ∘ f) = record
  { width = f.width ⊔ g.width
  ; length  = f.length + g.length
  }
  where
  module f = Size (size f)
  module g = Size (size g)

-- Case: Composition -------------------
size (g ⊗ f) = record
  { width = f.width + g.width
  ; length  = f.length ⊔ g.length
  }
  where
  module f = Size (size f)
  module g = Size (size g)

-- Case: Composition -------------------
size (g ⊕ f) = record
  { width = f.width + g.width
  ; length  = f.length ⊔ g.length
  }
  where
  module f = Size (size f)
  module g = Size (size g)

record ΔSize : Set where
  field
    Δwidth Δlength : Integer
open ΔSize public

Δsize : ∀ {A B} {f g : A ↔ B} → f ≅ g → ΔSize
Δsize {f = f} {g} p = record
  { Δwidth  = g.width  -ℕ f.width
  ; Δlength = g.length -ℕ f.length
  }
  where
  module f = Size (size f)
  module g = Size (size g)
-}

module NatProp where
  +zero : (x : Nat) → x + 0 ≡ x
  +zero zero    = refl
  +zero (suc x) = suc $≡ +zero x

  +suc : (x y : Nat) → x + suc y ≡ suc (x + y)
  +suc zero    y = refl
  +suc (suc x) y = suc $≡ +suc x y

  +comm : (x y : Nat) → x + y ≡ y + x
  +comm zero    y       =
    sym (+zero y)
  +comm (suc x) zero    =
    suc $≡ +zero x
  +comm (suc x) (suc y) =
    suc $≡
      ( +suc x y
    ⟨≡⟩ +comm (suc x) y
      )

  +assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
  +assoc zero    y z = refl
  +assoc (suc x) y z = suc $≡ +assoc x y z

  ⊔zero : (x : Nat) → x ⊔ 0 ≡ x
  ⊔zero zero    = refl
  ⊔zero (suc x) = refl

  ⊔sucₗ : (x y : Nat) → Σ Nat λ z → suc x ⊔ y ≡ suc z
  ⊔sucₗ x zero    = x     , refl
  ⊔sucₗ x (suc y) = x ⊔ y , refl

  ⊔sucᵣ : (x y : Nat) → Σ Nat λ z → x ⊔ suc y ≡ suc z
  ⊔sucᵣ zero    y       = y , refl
  ⊔sucᵣ (suc x) zero    = x , suc $≡ ⊔zero x
  ⊔sucᵣ (suc x) (suc y) = (suc *** cong suc) (⊔sucᵣ x y)

  ⊔idem : (x : Nat) → x ⊔ x ≡ x
  ⊔idem zero    = refl
  ⊔idem (suc x) = suc $≡ ⊔idem x

  ⊔idemₗ : (x y : Nat) → x ⊔ y ⊔ x ≡ x ⊔ y
  ⊔idemₗ zero    zero    = refl
  ⊔idemₗ zero    (suc y) = refl
  ⊔idemₗ (suc x) zero    = suc $≡ ⊔idem x
  ⊔idemₗ (suc x) (suc y) = suc $≡ ⊔idemₗ x y

  ⊔idemᵣ : (x y : Nat) → x ⊔ y ⊔ y ≡ x ⊔ y
  ⊔idemᵣ zero    zero    = refl
  ⊔idemᵣ zero    (suc y) = suc $≡ ⊔idem y
  ⊔idemᵣ (suc x) zero    = refl
  ⊔idemᵣ (suc x) (suc y) = suc $≡ ⊔idemᵣ x y

  ⊔comm : (x y : Nat) → x ⊔ y ≡ y ⊔ x
  ⊔comm zero    y       = sym (⊔zero y)
  ⊔comm (suc x) zero    = refl
  ⊔comm (suc x) (suc y) = suc $≡ ⊔comm x y

  ⊔assoc : (x y z : Nat) → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)
  ⊔assoc zero    y       z       = refl
  ⊔assoc (suc x) zero    z       = refl
  ⊔assoc (suc x) (suc y) zero    = refl
  ⊔assoc (suc x) (suc y) (suc z) = suc $≡ ⊔assoc x y z

  ⊔ord₁ : (x y : Nat)
       → x ≤ y
       → x ⊔ y ≡ y
  ⊔ord₁ zero    zero    (diff z eq) = refl
  ⊔ord₁ zero    (suc y) (diff z eq) = refl
  ⊔ord₁ (suc x) zero    (diff z eq) with pred $≡ eq ⟨≡⟩ +suc z x
  ...| ()
  ⊔ord₁ (suc x) (suc y) (diff z eq) = suc $≡ ⊔ord₁ x y (diff z (pred $≡ eq ⟨≡⟩ +suc z x))

  ⊔ord₂ : (x y : Nat)
        → x ⊔ y ≡ y
        → x ≤ y
  ⊔ord₂ zero    zero    eq = diff! 0
  ⊔ord₂ zero    (suc y) eq = diff (suc y) (Nat.suc ∘ suc $≡ sym (+zero y))
  ⊔ord₂ (suc x) zero ()
  ⊔ord₂ (suc x) (suc y) eq with ⊔ord₂ x y (pred $≡ eq)
  ...| (diff k eq') = diff k (Nat.suc $≡ (eq' ⟨≡⟩ sym (+suc k x)))

