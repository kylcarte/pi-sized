
module Pi where

open import Prelude as ℙ
  hiding
    ( [_]
    ; pos ; neg
    ; negsuc
    ; length
    ; id
    ; _∘_
    )
  renaming
    ( _∎ to _■
    ; refl to 𝕣
    ; sym to 𝕤
    ; trans to 𝕥
    ; _⊔_ to lmax
    ; Either to _ℙ+_
    ; _×_ to _ℙ×_
    ; left to inl
    ; right to inr
    )

open import Data.Integer

instance
  SemiringSet : Semiring Set
  SemiringSet = record { zro = ⊥ ; one = ⊤ ; _+_ = _ℙ+_ ; _*_ = _ℙ×_ }

infixr 3 _+++_
_+++_ : ∀ {a b c d}
      → {A : Set a} {B : Set b} {C : Set c} {D : Set d}
      → (f : A → B) (g : C → D)
      → A ℙ+ C → B ℙ+ D
f +++ g = either (inl ℙ.∘ f) (inr ℙ.∘ g)

infix 4 _≃_
_≃_ : ∀ {a b} {A : Set a} {B : A → Set b}
    → (f g : ∀ x → B x)
    → Set (lmax a b)
f ≃ g = ∀ x → f x ≡ g x

infixr 6 _⊕_
infixr 7 _⊗_
data U : Set where
  𝟘 𝟙     : U
  _⊕_ _⊗_ : U → U → U

infix 1 _∼_
data _∼_ : U → U → Set where
  ⊕λ : ∀ {A}
     → 𝟘 ⊕ A ∼ A
  ⊕ρ : ∀ {A}
     → A ⊕ 𝟘 ∼ A
  ⊕σ : ∀ {A B}
     → A ⊕ B ∼ B ⊕ A
  ⊕α : ∀ {A B C}
     → (A ⊕ B) ⊕ C ∼ A ⊕ (B ⊕ C)
  ⊗λ : ∀ {A}
     → 𝟙 ⊗ A ∼ A
  ⊗ρ : ∀ {A}
     → A ⊗ 𝟙 ∼ A
  ⊗σ : ∀ {A B}
     → A ⊗ B ∼ B ⊗ A
  ⊗α : ∀ {A B C}
     → (A ⊗ B) ⊗ C ∼ A ⊗ (B ⊗ C)
  δ  : ∀ {A B C}
     → A ⊗ (B ⊕ C) ∼ (A ⊗ B) ⊕ (A ⊗ C)

space : U → Nat
space 𝟘 = 0
space 𝟙 = 1
space (A ⊕ B) = space A ⊔ space B
space (A ⊗ B) = space A + space B

infix 1 _↔_
infixr 5 _∘_
data _↔_ : U → U → Set where
  [_] : ∀ {A B}
      → A ∼ B
      → A ↔ B
  id : ∀ {A}
    → A ↔ A
  _⁻¹ : ∀ {A B}
    → A ↔ B
    → B ↔ A
  _∘_ : ∀ {A B C}
      → B ↔ C
      → A ↔ B
      → A ↔ C
  _⊗_ : ∀ {A B C D}
      → A ↔ B
      → C ↔ D
      → A ⊗ C ↔ B ⊗ D
  _⊕_ : ∀ {A B C D}
      → A ↔ B
      → C ↔ D
      → A ⊕ C ↔ B ⊕ D

El : U → Set
El 𝟘       = zro
El 𝟙       = one
El (A ⊕ B) = El A + El B
El (A ⊗ B) = El A * El B

fwd : ∀ {A B}
    → A ∼ B
    → El A → El B
bwd : ∀ {A B}
    → A ∼ B
    → El B → El A

fwd ⊕λ (inl ())
fwd ⊕λ (inr x)          = x
fwd ⊕ρ (inl x)          = x
fwd ⊕ρ (inr ())
fwd ⊕σ (inl x)          = inr x
fwd ⊕σ (inr x)          = inl x
fwd ⊕α (inl (inl x))    = inl x
fwd ⊕α (inl (inr x))    = inr (inl x)
fwd ⊕α (inr x)          = inr (inr x)
fwd ⊗λ (tt , x)         = x
fwd ⊗ρ (x , tt)         = x
fwd ⊗σ (x , y)          = y , x
fwd ⊗α ((x , y) , z)    = x , y , z
fwd δ (x , inl y) = inl (x , y)
fwd δ (x , inr y) = inr (x , y)

bwd ⊕λ x                   = inr x
bwd ⊕ρ x                   = inl x
bwd ⊕σ (inl x)             = inr x
bwd ⊕σ (inr x)             = inl x
bwd ⊕α (inl x)             = inl (inl x)
bwd ⊕α (inr (inl x))       = inl (inr x)
bwd ⊕α (inr (inr x))       = inr x
bwd ⊗λ x                   = tt , x
bwd ⊗ρ x                   = x , tt
bwd ⊗σ (x , y)             = y , x
bwd ⊗α (x , y , z)         = (x , y) , z
bwd δ (inl  (x , y)) = x , inl y
bwd δ (inr (x , y))  = x , inr y

fwd-bwd : ∀ {A B}
        → (f : A ∼ B)
        → bwd f ℙ.∘ fwd f ≃ ℙ.id

fwd-bwd ⊕λ (inl ())
fwd-bwd ⊕λ (inr x)       = 𝕣
fwd-bwd ⊕ρ (inl x)       = 𝕣
fwd-bwd ⊕ρ (inr ())
fwd-bwd ⊕σ (inl x)       = 𝕣
fwd-bwd ⊕σ (inr x)       = 𝕣
fwd-bwd ⊕α (inl (inl x)) = 𝕣
fwd-bwd ⊕α (inl (inr x)) = 𝕣
fwd-bwd ⊕α (inr x)       = 𝕣
fwd-bwd ⊗λ (tt , x)      = 𝕣
fwd-bwd ⊗ρ (x , tt)      = 𝕣
fwd-bwd ⊗σ (x , y)       = 𝕣
fwd-bwd ⊗α ((x , y) , z) = 𝕣
fwd-bwd δ (x , inl y)    = 𝕣
fwd-bwd δ (x , inr y)    = 𝕣

bwd-fwd : ∀ {A B}
        → (f : A ∼ B)
        → fwd f ℙ.∘ bwd f ≃ ℙ.id
bwd-fwd ⊕λ x             = 𝕣
bwd-fwd ⊕ρ x             = 𝕣
bwd-fwd ⊕σ (inl x)       = 𝕣
bwd-fwd ⊕σ (inr x)       = 𝕣
bwd-fwd ⊕α (inl x)       = 𝕣
bwd-fwd ⊕α (inr (inl x)) = 𝕣
bwd-fwd ⊕α (inr (inr x)) = 𝕣
bwd-fwd ⊗λ x             = 𝕣
bwd-fwd ⊗ρ x             = 𝕣
bwd-fwd ⊗σ (x , y)       = 𝕣
bwd-fwd ⊗α (x , y , z)   = 𝕣
bwd-fwd δ (inl (x , y))  = 𝕣
bwd-fwd δ (inr (x , y))  = 𝕣

ap : ∀ {A B}
   → A ↔ B
   → El A → El B
ap⁻¹ : ∀ {A B}
     → A ↔ B
     → El B → El A

ap [ f ]   = fwd f
ap id      = ℙ.id
ap (f ⁻¹)  = ap⁻¹ f
ap (g ∘ f) = ap g ℙ.∘ ap f
ap (f ⊗ g) = ap f *** ap g
ap (f ⊕ g) = ap f +++ ap g

ap⁻¹ [ f ]   = bwd f
ap⁻¹ id      = ℙ.id
ap⁻¹ (f ⁻¹)  = ap f
ap⁻¹ (g ∘ f) = ap⁻¹ f ℙ.∘ ap⁻¹ g
ap⁻¹ (f ⊗ g) = ap⁻¹ f *** ap⁻¹ g
ap⁻¹ (f ⊕ g) = ap⁻¹ f +++ ap⁻¹ g

ap-inv : ∀ {A B}
       → (f : A ↔ B)
       → ap⁻¹ f ℙ.∘ ap f ≃ ℙ.id
inv-ap : ∀ {A B}
       → (f : A ↔ B)
       → ap f ℙ.∘ ap⁻¹ f ≃ ℙ.id

ap-inv [ f ]   x = fwd-bwd f x
ap-inv id      x = 𝕣
ap-inv (f ⁻¹)  x = inv-ap f x
ap-inv (g ∘ f) x =
  ap⁻¹ f $≡ ap-inv g (ap f x)
  ⟨≡⟩ ap-inv f x
ap-inv (f ⊗ g) (x , y) = cong₂ _,_ (ap-inv f x) (ap-inv g y)
ap-inv (f ⊕ g) (inl x)  = inl  $≡ ap-inv f x
ap-inv (f ⊕ g) (inr x) = inr $≡ ap-inv g x

inv-ap [ f ]   x = bwd-fwd f x
inv-ap id      x = 𝕣
inv-ap (f ⁻¹)  x = ap-inv f x
inv-ap (g ∘ f) x =
  ap g $≡ inv-ap f (ap⁻¹ g x)
  ⟨≡⟩ inv-ap g x
inv-ap (f ⊗ g) (x , y) = cong₂ _,_ (inv-ap f x) (inv-ap g y)
inv-ap (f ⊕ g) (inl x)  = inl  $≡ inv-ap f x
inv-ap (f ⊕ g) (inr x) = inr $≡ inv-ap g x

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

Δsize : ∀ {A B} (f g : A ↔ B) → ΔSize
Δsize f g = record
  { Δwidth  = g.width  -ℕ f.width
  ; Δlength = g.length -ℕ f.length
  }
  where
  module f = Size (size f)
  module g = Size (size g)

{-
Ufwd : ∀ {A B} → A ↔ B → (El B → Nat → Σ U El) → El A → Nat → Σ U El
Ubwd : ∀ {A B} → A ↔ B → (El A → Nat → Σ U El) → El B → Nat → Σ U El

Ufwd {A} [ f ] k t zero    = A , t
Ufwd     [ f ] k t (suc x) = k (fwd f t) x
Ufwd  id      = ℙ.id
Ufwd  (f ⁻¹)  = Ubwd f
Ufwd  (g ∘ f) = Ufwd f ℙ.∘ Ufwd g
Ufwd  (f ⊗ g) k = {!!}
Ufwd  (f ⊕ g) k = {!!}

Ubwd {B = B} [ f ] k t zero    = B , t
Ubwd         [ f ] k t (suc x) = k (bwd f t) x
Ubwd id      = ℙ.id
Ubwd (f ⁻¹)  = Ufwd f
Ubwd (g ∘ f) = Ubwd g ℙ.∘ Ubwd f
Ubwd {A = A ⊗ C} {B = B ⊗ D} (f ⊗ g) k (t , u) x = fst f' ⊗ fst g' , snd f' , snd g'
  where
  f' : Σ U El
  f' = Ubwd f
    {!!}
    t x
  g' : Σ U El
  g' = Ubwd g
    {!!}
    u x
Ubwd (f ⊕ g) k = {!!}
-}
