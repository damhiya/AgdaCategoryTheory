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
  (C₀ : Set c)
  (C₁ : Rel C₀ ℓ)
  (_∘_ : TransitiveFlip C₁)
  (id : Reflexive C₁)
  : Set (c ⊔ ℓ) where
  field
    ∘-assoc : ∀ {x y z w} {f : C₁ x y} {g : C₁ y z} {h : C₁ z w} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    id∘f≡f : ∀ {x y} (f : C₁ x y) → id ∘ f ≡ f
    f∘id≡f : ∀ {x y} (f : C₁ x y) → f ∘ id ≡ f

record Category c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 9 _∘_
  field
    C₀ : Set c
    C₁ : Rel C₀ ℓ
    _∘_ : TransitiveFlip C₁
    id : Reflexive C₁
    isCategory : IsCategory C₀ C₁ _∘_ id
  open IsCategory isCategory public

ob : (C : Category c ℓ) → Set c
ob C = Category.C₀ C

hom : (C : Category c ℓ) → Rel (ob C) ℓ
hom C = Category.C₁ C

open Category using (id)

infixr 9 _∘_
_∘_ : ∀ {C : Category c ℓ} {x y z} → hom C y z → hom C x y → hom C x z
_∘_ {C = C} = Category._∘_ C
  
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

_[_] : ∀ {C : Category c ℓ₁} {D : Category d ℓ₂} → Functor C D → ob C → ob D
F [ x ] = Functor.F₀ F x

_⟦_⟧ : ∀ {C : Category c ℓ₁} {D : Category d ℓ₂} → (F : Functor C D) →
       ∀ {x y} → hom C x y → hom D (F [ x ]) (F [ y ])
F ⟦ f ⟧ = Functor.F₁ F f
 
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
