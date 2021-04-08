open import Level
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Category as Cat hiding (_∘_)

module F-algebra {c ℓ} {C : Category c ℓ} {F : Endofunctor C} where

F-algebra : Set (c ⊔ ℓ)
F-algebra = ∃[ x ] hom C (F [ x ]) x

carrier : F-algebra → ob C
carrier (X , α) = X
  
algebra : (alg : F-algebra) → hom C (F [ carrier alg ]) (carrier alg)
algebra (X , α) = α

record FAlgebraHomomorphism
  ([X,α] : F-algebra)
  ([Y,β] : F-algebra)
  : Set (c ⊔ ℓ) where
  private
    X = carrier [X,α]
    Y = carrier [Y,β]
    α = algebra [X,α]
    β = algebra [Y,β]
    open Category C
  field
    m : hom C X Y
    m∘α≡β∘F[m] : m ∘ α ≡ β ∘ F ⟦ m ⟧

infixr 5 _∘₁_
_∘₁_ : ∀ {[X,α] [Y,β] [Z,γ]} →
      FAlgebraHomomorphism [Y,β] [Z,γ] →
      FAlgebraHomomorphism [X,α] [Y,β] →
      FAlgebraHomomorphism [X,α] [Z,γ]
_∘₁_ {[X,α] = (X , α)} {[Y,β] = (Y , β)} {[Z,γ] = (Z , γ)} g f =
  record {m = m; m∘α≡β∘F[m] = m∘α≡γ∘F[m]}
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
