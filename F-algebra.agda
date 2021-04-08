module F-algebra where

open import Level
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Category as Cat hiding (_∘_)

private
  variable
    c ℓ : Level

F-algebra : ∀ (C : Category c ℓ) (F : Endofunctor C) → Set (c ⊔ ℓ)
F-algebra C F = ∃[ x ] hom C (F [ x ]) x

carrier : ∀ {C : Category c ℓ} F → F-algebra C F → ob C
carrier F (X , α) = X
  
algebra : ∀ {C : Category c ℓ} F → (alg : F-algebra C F) → hom C (F [ carrier F alg ]) (carrier F alg)
algebra F (X , α) = α

record FAlgebraHomomorphism
  (C : Category c ℓ)
  (F : Endofunctor C)
  ([X,α] : F-algebra C F)
  ([Y,β] : F-algebra C F)
  : Set (c ⊔ ℓ) where
  private
    X = carrier F [X,α]
    Y = carrier F [Y,β]
    α = algebra F [X,α]
    β = algebra F [Y,β]
    open Category C
  field
    m : hom C X Y
    m∘α≡β∘F[m] : m ∘ α ≡ β ∘ F ⟦ m ⟧

infixr 5 _∘₁_
_∘₁_ : ∀ {C : Category c ℓ} {F : Endofunctor C} {[X,α] [Y,β] [Z,γ]} →
      FAlgebraHomomorphism C F [Y,β] [Z,γ] →
      FAlgebraHomomorphism C F [X,α] [Y,β] →
      FAlgebraHomomorphism C F [X,α] [Z,γ]
_∘₁_ {C = C} {F = F}
  {[X,α] = (X , α)}
  {[Y,β] = (Y , β)}
  {[Z,γ] = (Z , γ)}
  g f = record {m = m; m∘α≡β∘F[m] = m∘α≡γ∘F[m]}
  where
    open Category C
    open Functor F
    open FAlgebraHomomorphism f renaming (m to m₁; m∘α≡β∘F[m] to m₁∘α≡β∘F[m₁])
    open FAlgebraHomomorphism g renaming (m to m₂; m∘α≡β∘F[m] to m₂∘β≡γ∘F[m₂])
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
