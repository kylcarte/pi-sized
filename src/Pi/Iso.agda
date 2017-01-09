
module Pi.Iso where

open import Prelude as ℙ
  hiding
    ( [_]
    ; id
    ; _∘_
    )
  renaming
    ( left to inl
    ; right to inr
    )
open import Pi

infix 4 _≅_
record _≅_ {A B} (f g : A ↔ B) : Set where
  constructor natl
  field
    cmpt : ap f ≃ ap g
open _≅_ public

infix 1 Iso
Iso : ∀ A B (f g : A ↔ B) → Set
Iso A B = _≅_
{-# INLINE Iso #-}

syntax Iso A B f g = f ≅ g ∶ A ↔ B

∘idₗ : ∀ {A B} (f : A ↔ B)
     → id ∘ f ≅ f
∘idₗ f = natl λ x → ℙ.refl

∘idᵣ : ∀ {A B} (f : A ↔ B)
     → f ∘ id ≅ f
∘idᵣ f = natl λ x → ℙ.refl

∘invₗ : ∀ {A B} (f : A ↔ B)
      → f ⁻¹ ∘ f ≅ id
∘invₗ f = natl (ap-inv f)

∘invᵣ : ∀ {A B} (f : A ↔ B)
      → f ∘ f ⁻¹ ≅ id
∘invᵣ f = natl (inv-ap f)

∘assoc : ∀ {A B C D}
       → (f : A ↔ B) (g : B ↔ C) (h : C ↔ D)
       → (h ∘ g) ∘ f ≅ h ∘ (g ∘ f)
∘assoc f g h = natl λ x → ℙ.refl

⁻¹cong : ∀ {A B}
       → {f g : A ↔ B} → f ≅ g
       → f ⁻¹ ≅ g ⁻¹
⁻¹cong {f = f} {g} p = natl λ x →
  ap⁻¹ f x
    ≡⟨ ap⁻¹ f $≡ ℙ.sym (inv-ap g x) ⟩
  ap⁻¹ f (ap g (ap⁻¹ g x))
    ≡⟨ ap⁻¹ f $≡ ℙ.sym (cmpt p (ap⁻¹ g x)) ⟩
  ap⁻¹ f (ap f (ap⁻¹ g x))
    ≡⟨ ap-inv f (ap⁻¹ g x) ⟩
  ap⁻¹ g x ∎

∘cong : ∀ {A B C}
      → {f g : A ↔ B} → f ≅ g
      → {h i : B ↔ C} → h ≅ i
      → h ∘ f ≅ i ∘ g
∘cong {g = g} p {h} q = natl λ x → ap h $≡ cmpt p x ⟨≡⟩ cmpt q (ap g x)

⊗cong : ∀ {A B C D}
      → {f g : A ↔ B} → f ≅ g
      → {h i : C ↔ D} → h ≅ i
      → f ⊗ h ≅ g ⊗ i
⊗cong p q = natl λ { (x , y) → cong₂ _,_ (cmpt p x) (cmpt q y) }

⊕cong : ∀ {A B C D}
      → {f g : A ↔ B} → f ≅ g
      → {h i : C ↔ D} → h ≅ i
      → f ⊕ h ≅ g ⊕ i
⊕cong p q = natl λ
  { (inl x) → inl $≡ cmpt p x
  ; (inr x) → inr $≡ cmpt q x
  }

∘/⁻¹ : ∀ {A B C}
     → (f : A ↔ B) (g : B ↔ C)
     → (g ∘ f) ⁻¹ ≅ f ⁻¹ ∘ g ⁻¹
∘/⁻¹ f g = natl λ x → ℙ.refl

⊗tri : ∀ {A B}
     → (id ⊗ [ ⊗λ ]) ∘ [ ⊗α ] ≅ [ ⊗ρ ] ⊗ id ∶ (A ⊗ 𝟙) ⊗ B ↔ A ⊗ B
⊗tri = natl λ { ((x , tt) , y) → ℙ.refl }

⊕tri : ∀ {A B}
     → (id ⊕ [ ⊕λ ]) ∘ [ ⊕α ] ≅ [ ⊕ρ ] ⊕ id ∶ (A ⊕ 𝟘) ⊕ B ↔ A ⊕ B
⊕tri = natl λ
  { (inl (inl x))  → ℙ.refl
  ; (inl (inr ()))
  ; (inr x)        → ℙ.refl
  }

⊕pent : ∀ {A B C D}
      → [ ⊕α ] ∘ [ ⊕α ] ≅ (id ⊕ [ ⊕α ]) ∘ [ ⊕α ] ∘ ([ ⊕α ] ⊕ id) ∶ ((A ⊕ B) ⊕ C) ⊕ D ↔ A ⊕ (B ⊕ (C ⊕ D))
⊕pent = natl λ
  { (inl (inl (inl x))) → ℙ.refl
  ; (inl (inl (inr x))) → ℙ.refl
  ; (inl (inr x))       → ℙ.refl
  ; (inr x)             → ℙ.refl
  }

⊗pent : ∀ {A B C D}
      → [ ⊗α ] ∘ [ ⊗α ] ≅ (id ⊗ [ ⊗α ]) ∘ [ ⊗α ] ∘ ([ ⊗α ] ⊗ id) ∶ ((A ⊗ B) ⊗ C) ⊗ D ↔ A ⊗ (B ⊗ (C ⊗ D))
⊗pent = natl λ
  { (((w , x) , y) , z) → ℙ.refl
  }

⊗hex : ∀ {A B C}
     → (id ⊗ [ ⊗σ ]) ∘ [ ⊗α ] ∘ ([ ⊗σ ] ⊗ id) ≅ [ ⊗α ] ∘ [ ⊗σ ] ∘ [ ⊗α ] ∶ (A ⊗ B) ⊗ C ↔ B ⊗ (C ⊗ A)
⊗hex = natl λ
  { ((x , y) , z) → ℙ.refl
  }

⊕hex : ∀ {A B C}
     → (id ⊕ [ ⊕σ ]) ∘ [ ⊕α ] ∘ ([ ⊕σ ] ⊕ id) ≅ [ ⊕α ] ∘ [ ⊕σ ] ∘ [ ⊕α ] ∶ (A ⊕ B) ⊕ C ↔ B ⊕ (C ⊕ A)
⊕hex = natl λ
  { (inl (inl x)) → ℙ.refl
  ; (inl (inr x)) → ℙ.refl
  ; (inr x)       → ℙ.refl
  }

⊗hex⁻¹ : ∀ {A B C}
       → ([ ⊗σ ] ⊗ id) ∘ [ ⊗α ] ⁻¹ ∘ (id ⊗ [ ⊗σ ]) ≅ [ ⊗α ] ⁻¹ ∘ [ ⊗σ ] ∘ [ ⊗α ] ⁻¹ ∶ A ⊗ (B ⊗ C) ↔ (C ⊗ A) ⊗ B
⊗hex⁻¹ = natl λ
  { (x , y , z) → ℙ.refl
  }

⊕hex⁻¹ : ∀ {A B C}
       → ([ ⊕σ ] ⊕ id) ∘ [ ⊕α ] ⁻¹ ∘ (id ⊕ [ ⊕σ ]) ≅ [ ⊕α ] ⁻¹ ∘ [ ⊕σ ] ∘ [ ⊕α ] ⁻¹ ∶ A ⊕ (B ⊕ C) ↔ (C ⊕ A) ⊕ B
⊕hex⁻¹ = natl λ
  { (inl x)       → ℙ.refl
  ; (inr (inl x)) → ℙ.refl
  ; (inr (inr x)) → ℙ.refl
  }
