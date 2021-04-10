open import Level
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Category as Cat hiding (_∘_)

open import Relation.Binary.HeterogeneousEquality.Core
import Relation.Binary.HeterogeneousEquality as HeteroEq
  
module F-algebra {c ℓ} {C : Category c ℓ} {F : Endofunctor C} where

open Category C
open Functor F

Algebra : ob C → Set ℓ
Algebra X = hom C (F [ X ]) X

[_,_]⟶[_,_] : ∀ (X : ob C) (α : Algebra X) (Y : ob C) (β : Algebra Y) → Set ℓ
[ X , α ]⟶[ Y , β ] = ∃[ m ] m ∘ α ≡ β ∘ F ⟦ m ⟧

infixr 5 _∘₁_
_∘₁_ : ∀ {X Y Z α β γ} →
      [ Y , β ]⟶[ Z , γ ] →
      [ X , α ]⟶[ Y , β ] →
      [ X , α ]⟶[ Z , γ ]
_∘₁_ {X} {Y} {Z} {α} {β} {γ} (m₂ , m₂∘β≡γ∘F[m₂]) (m₁ , m₁∘α≡β∘F[m₁]) = m , m∘α≡γ∘F[m]
  where
    open ≡-Reasoning
  
    m : hom C X Z
    m = m₂ ∘ m₁
  
    m∘α≡γ∘F[m] : m ∘ α ≡ γ ∘ F ⟦ m ⟧
    m∘α≡γ∘F[m] = begin
      m ∘ α ≡⟨ ∘-assoc ⟩
      m₂ ∘ (m₁ ∘ α) ≡⟨ cong (m₂ ∘_) m₁∘α≡β∘F[m₁] ⟩
      m₂ ∘ (β ∘ F ⟦ m₁ ⟧) ≡˘⟨ ∘-assoc ⟩
      (m₂ ∘ β) ∘ F ⟦ m₁ ⟧ ≡⟨ cong (_∘ F ⟦ m₁ ⟧) m₂∘β≡γ∘F[m₂] ⟩
      (γ ∘ F ⟦ m₂ ⟧) ∘ F ⟦ m₁ ⟧ ≡⟨ ∘-assoc ⟩
      γ ∘ (F ⟦ m₂ ⟧ ∘ F ⟦ m₁ ⟧) ≡˘⟨ cong (γ ∘_) respect-∘ ⟩
      γ ∘ F ⟦ m ⟧ ∎

private
  ≡-heterogeneous-irrelevantˡ : ∀ {a} {A B : Set a} {w x : A} {y z : B} (p : w ≡ x) (q : y ≡ z) → w ≅ y → p ≅ q
  ≡-heterogeneous-irrelevantˡ refl refl refl = refl

  Σ-≡,≅→≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
            a₁ ≡ a₂ → b₁ ≅ b₂ → p₁ ≡ p₂
  Σ-≡,≅→≡ refl refl = refl

∘₁-assoc : ∀ {X Y Z W α β γ δ}
             {f : [ X , α ]⟶[ Y , β ]}
             {g : [ Y , β ]⟶[ Z , γ ]}
             {h : [ Z , γ ]⟶[ W , δ ]} →
             (h ∘₁ g) ∘₁ f ≡ h ∘₁ (g ∘₁ f)
∘₁-assoc {X} {Y} {Z} {W} {α} {β} {γ} {δ} {f} {g} {h} = Σ-≡,≅→≡ ≡-proj₁ ≅-proj₂
  where
    mₗ : hom C X W
    mₗ = proj₁ ((h ∘₁ g) ∘₁ f)
  
    mᵣ : hom C X W
    mᵣ = proj₁ (h ∘₁ (g ∘₁ f))
  
    ≡-proj₁ : mₗ ≡ mᵣ
    ≡-proj₁ = ∘-assoc

    commuteₗ : mₗ ∘ α ≡ δ ∘ F ⟦ mₗ ⟧
    commuteₗ = proj₂ ((h ∘₁ g) ∘₁ f)

    commuteᵣ : mᵣ ∘ α ≡ δ ∘ F ⟦ mᵣ ⟧
    commuteᵣ = proj₂ (h ∘₁ (g ∘₁ f))
  
    ≅-proj₂ : commuteₗ ≅ commuteᵣ
    ≅-proj₂ = ≡-heterogeneous-irrelevantˡ commuteₗ commuteᵣ (≡-to-≅ (cong (_∘ α) ≡-proj₁))

id₁ : ∀ {X α} → [ X , α ]⟶[ X , α ]
id₁ {X} {α} = id , id∘α≡α∘F[id]
  where
    open ≡-Reasoning

    id∘α≡α∘F[id] : id ∘ α ≡ α ∘ F ⟦ id ⟧
    id∘α≡α∘F[id] = begin
      id ∘ α ≡⟨ id∘f≡f α ⟩
      α ≡˘⟨ f∘id≡f α ⟩
      α ∘ id ≡˘⟨ cong (α ∘_) respect-id ⟩
      α ∘ F ⟦ id ⟧ ∎
