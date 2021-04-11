module Category where

open import Level
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core

TransitiveFlip : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
TransitiveFlip _∼_ = TransFlip _∼_ _∼_ _∼_

private
  variable
    c d ℓ ℓ₁ ℓ₂ : Level

record IsCategory
  (Ob : Set c)
  (_⟶_ : Rel Ob ℓ)
  (_∘_ : TransitiveFlip _⟶_)
  (id : Reflexive _⟶_)
  : Set (c ⊔ ℓ) where
  field
    ∘-assoc : ∀ {x y z w} (h : z ⟶ w) (g : y ⟶ z) (f : x ⟶ y) → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    id∘f≡f : ∀ {x y} (f : x ⟶ y) → id ∘ f ≡ f
    f∘id≡f : ∀ {x y} (f : x ⟶ y) → f ∘ id ≡ f

record Category c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 4 _⟶_
  infixr 9 _∘_
  field
    Ob : Set c
    _⟶_ : Rel Ob ℓ
    _∘_ : TransitiveFlip _⟶_
    id : Reflexive _⟶_
    isCategory : IsCategory Ob _⟶_ _∘_ id
  open IsCategory isCategory public

ob : (C : Category c ℓ) → Set c
ob C = Category.Ob C

hom : (C : Category c ℓ) → Rel (ob C) ℓ
hom C = Category._⟶_ C

record IsFunctor
  (C : Category c ℓ₁)
  (D : Category d ℓ₂)
  (F₀ : ob C → ob D)
  (F₁ : ∀ {x y} → hom C x y → hom D (F₀ x) (F₀ y))
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  open Category C renaming (id to id₁; _∘_ to _∘₁_)
  open Category D renaming (id to id₂; _∘_ to _∘₂_)
  field
    respect-id : ∀ {x} → F₁ (id₁ {x}) ≡ id₂ {F₀ x}
    respect-∘ : ∀ {x y z} (g : hom C y z) (f : hom C x y) → F₁ (g ∘₁ f) ≡ F₁ g ∘₂ F₁ f

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

_[_] : ∀ {C : Category c ℓ₁} {D : Category d ℓ₂} → Functor C D → ob C → ob D
F [ x ] = Functor.F₀ F x

_⟦_⟧ : ∀ {C : Category c ℓ₁} {D : Category d ℓ₂} → (F : Functor C D) →
       ∀ {x y} → hom C x y → hom D (F [ x ]) (F [ y ])
F ⟦ f ⟧ = Functor.F₁ F f
 
Endofunctor : (C : Category c ℓ) → Set (c ⊔ ℓ)
Endofunctor C = Functor C C

UniqueMorphism : ∀ (C : Category c ℓ) (X Y : ob C) (u : hom C X Y) → Set ℓ
UniqueMorphism C X Y u = ∀ (u' : hom C X Y) → u' ≡ u

IsInitialObject : ∀ (C : Category c ℓ) (∅ : ob C) (! : ∀ x → hom C ∅ x) → Set (c ⊔ ℓ)
IsInitialObject C ∅ ! = ∀ {x} → UniqueMorphism C ∅ x (! x)

IsTerminalObject : ∀ (C : Category c ℓ) (∗ : ob C) (! : ∀ x → hom C x ∗) → Set (c ⊔ ℓ)
IsTerminalObject C ∗ ! = ∀ {x} → UniqueMorphism C x ∗ (! x)

record InitialObject (C : Category c ℓ) : Set (c ⊔ ℓ) where
  constructor initial
  field
    ∅ : ob C
    !ᵢ : ∀ x → hom C ∅ x
    !ᵢ-unique : IsInitialObject C ∅ !ᵢ

record TerminalObject (C : Category c ℓ) : Set (c ⊔ ℓ) where
  constructor terminal
  field
    ∗ : ob C
    !ₜ : ∀ x → hom C x ∗
    !ₜ-unique : IsTerminalObject C ∗ !ₜ

IsIsomorphism : ∀ (C : Category c ℓ) (X Y : ob C) (f : hom C X Y) (g : hom C Y X) → Set ℓ
IsIsomorphism C X Y f g = (g ∘ f ≡ id) × (f ∘ g ≡ id)
  where open Category C

record Isomorphic (C : Category c ℓ) (X Y : ob C) : Set (c ⊔ ℓ) where
  constructor iso
  open Category C
  field
    to : hom C X Y
    from : hom C Y X
    isIsomorphism : IsIsomorphism C X Y to from
