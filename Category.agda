module Category where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core

TransitiveFlip : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
TransitiveFlip _∼_ = TransFlip _∼_ _∼_ _∼_

private
  variable
    c d ℓ ℓ₁ ℓ₂ : Level
  
record IsCategory
  (ob : Set c)
  (hom : Rel ob ℓ)
  (_∘_ : TransitiveFlip hom)
  (id : Reflexive hom)
  : Set (c ⊔ ℓ) where
  field
    ∘-assoc : ∀ {x y z w} {f : hom x y} {g : hom y z} {h : hom z w} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    id∘f≡f : ∀ {x y} (f : hom x y) → id ∘ f ≡ f
    f∘id≡f : ∀ {x y} (f : hom x y) → f ∘ id ≡ f

record Category c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    ob : Set c
    hom : Rel ob ℓ
    _∘_ : TransitiveFlip hom
    id : Reflexive hom
    isCategory : IsCategory ob hom _∘_ id
  open IsCategory isCategory public

open Category

record IsFunctor
  (C : Category c ℓ₁)
  (D : Category d ℓ₂)
  (F₀ : ob C → ob D)
  (F₁ : ∀ {x y} → hom C x y → hom D (F₀ x) (F₀ y))
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  open Category C renaming (_∘_ to _∘₁_)
  open Category D renaming (_∘_ to _∘₂_)
  field
    respect-id : ∀ {x} → F₁ (id C {x}) ≡ id D {F₀ x}
    respect-∘ : ∀ {x y z} {f : hom C x y} {g : hom C y z} → F₁ (g ∘₁ f) ≡ F₁ g ∘₂ F₁ f

record Functor
  (C : Category c ℓ₁)
  (D : Category d ℓ₂)
  : Set (c ⊔ d ⊔ ℓ₁ ⊔ ℓ₂) where
  open Category C renaming (_∘_ to _∘₁_)
  open Category D renaming (_∘_ to _∘₂_)
  field
    F₀ : ob C → ob D
    F₁ : ∀ {x y} → hom C x y → hom D (F₀ x) (F₀ y)
    isFunctor : IsFunctor C D F₀ F₁
  open IsFunctor isFunctor public

Endofunctor : (C : Category c ℓ) → Set (c ⊔ ℓ)
Endofunctor C = Functor C C

record IsInitialObject
  (C : Category c ℓ)
  (∅ : ob C)
  (! : ∀ {x} → hom C ∅ x)
  : Set (c ⊔ ℓ) where
  field
    !-unique : ∀ {x} (!₁ : hom C ∅ x) → !₁ ≡ !

record InitialObject (C : Category c ℓ) : Set (c ⊔ ℓ) where
  field
    ∅ : ob C
    ! : ∀ {x} → hom C ∅ x
    isInitialObject : IsInitialObject C ∅ !
  open IsInitialObject isInitialObject public

record IsTerminalObject
  (C : Category c ℓ)
  (∗ : ob C)
  (! : ∀ {x} → hom C x ∗)
  : Set (c ⊔ ℓ) where
  field
    !-unique : ∀ {x} (!₁ : hom C x ∗) → !₁ ≡ !

record TerminalObject (C : Category c ℓ) : Set (c ⊔ ℓ) where
  field
    ∗ : ob C
    ! : ∀ {x} → hom C x ∗
    isTerminalObject : IsTerminalObject C ∗ !
  open IsTerminalObject isTerminalObject public

