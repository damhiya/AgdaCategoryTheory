open import Level
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality.Core
open import Category as Cat
open import Relation.Binary.HeterogeneousEquality.Core
import Relation.Binary.HeterogeneousEquality as HeteroEq
  
module F-algebra {c ℓ} {C : Category c ℓ} {F : Endofunctor C} where

open Category C
open Functor F

Extract : ob C → Set ℓ
Extract X = hom C (F [ X ]) X

FAlgebra : Set (c ⊔ ℓ)
FAlgebra = ∃[ X ] Extract X

[_,_]⟶[_,_] : ∀ (X : ob C) (α : Extract X) (Y : ob C) (β : Extract Y) → Set ℓ
[ X , α ]⟶[ Y , β ] = ∃[ m ] m ∘ α ≡ β ∘ F ⟦ m ⟧

FAlgebraHom : FAlgebra → FAlgebra → Set ℓ
FAlgebraHom (X , α) (Y , β) = [ X , α ]⟶[ Y , β ]
  
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
      m ∘ α ≡⟨ ∘-assoc _ _ _ ⟩
      m₂ ∘ (m₁ ∘ α) ≡⟨ cong (m₂ ∘_) m₁∘α≡β∘F[m₁] ⟩
      m₂ ∘ (β ∘ F ⟦ m₁ ⟧) ≡˘⟨ ∘-assoc _ _ _  ⟩
      (m₂ ∘ β) ∘ F ⟦ m₁ ⟧ ≡⟨ cong (_∘ F ⟦ m₁ ⟧) m₂∘β≡γ∘F[m₂] ⟩
      (γ ∘ F ⟦ m₂ ⟧) ∘ F ⟦ m₁ ⟧ ≡⟨ ∘-assoc _ _ _ ⟩
      γ ∘ (F ⟦ m₂ ⟧ ∘ F ⟦ m₁ ⟧) ≡˘⟨ cong (γ ∘_) (respect-∘ _ _) ⟩
      γ ∘ F ⟦ m ⟧ ∎

private
  ≡-heterogeneous-irrelevantˡ : ∀ {a} {A B : Set a} {w x : A} {y z : B} (p : w ≡ x) (q : y ≡ z) → w ≅ y → p ≅ q
  ≡-heterogeneous-irrelevantˡ refl refl refl = refl

  Σ-≡,≅→≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
            a₁ ≡ a₂ → b₁ ≅ b₂ → p₁ ≡ p₂
  Σ-≡,≅→≡ refl refl = refl

commute-irrelevant : ∀ {X Y α β} →
                     {f : [ X , α ]⟶[ Y , β ]} →
                     {g : [ X , α ]⟶[ Y , β ]} →
                     proj₁ f ≡ proj₁ g → f ≡ g
commute-irrelevant {X} {Y} {α} {β} {f} {g} ≡-proj₁ = Σ-≡,≅→≡ ≡-proj₁ ≅-proj₂
  where
    ≅-proj₂ : proj₂ f ≅ proj₂ g
    ≅-proj₂ = ≡-heterogeneous-irrelevantˡ (proj₂ f) (proj₂ g) (≡-to-≅ (cong (_∘ α) ≡-proj₁))
  
∘₁-assoc : ∀ {X Y Z W α β γ δ}
             (h : [ Z , γ ]⟶[ W , δ ])
             (g : [ Y , β ]⟶[ Z , γ ])
             (f : [ X , α ]⟶[ Y , β ]) →
             (h ∘₁ g) ∘₁ f ≡ h ∘₁ (g ∘₁ f)
∘₁-assoc h g f = commute-irrelevant (∘-assoc (proj₁ h) (proj₁ g) (proj₁ f))

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

id₁∘₁f≡f : ∀ {X Y α β} (f : [ X , α ]⟶[ Y , β ]) → id₁ ∘₁ f ≡ f
id₁∘₁f≡f f = commute-irrelevant (id∘f≡f (proj₁ f))
  
f∘₁id₁≡f : ∀ {X Y α β} (f : [ X , α ]⟶[ Y , β ]) → f ∘₁ id₁ ≡ f
f∘₁id₁≡f f = commute-irrelevant (f∘id≡f (proj₁ f))

FAlgebraIsCategory : IsCategory FAlgebra FAlgebraHom _∘₁_ id₁
FAlgebraIsCategory = record
  { ∘-assoc = ∘₁-assoc
  ; id∘f≡f = id₁∘₁f≡f
  ; f∘id≡f = f∘₁id₁≡f
  }

FAlgebraCategory : Category (c ⊔ ℓ) ℓ
FAlgebraCategory = record
  { C₀ = FAlgebra
  ; C₁ = FAlgebraHom
  ; _∘_ = _∘₁_
  ; id = id₁
  ; isCategory = FAlgebraIsCategory
  }

InitialAlgebra : Set (c ⊔ ℓ)
InitialAlgebra = InitialObject FAlgebraCategory

module _ ((initial (X , α) ! !-unique) : InitialAlgebra) where
  open ≡-Reasoning
  
  private
    [α] : [ F [ X ] , F ⟦ α ⟧ ]⟶[ X , α ]
    [α] = α , refl
  
    [i] : [ X , α ]⟶[ F [ X ] , F ⟦ α ⟧ ]
    [i] = ! (F [ X ] , F ⟦ α ⟧)
    
    i : hom C X (F [ X ])
    i = proj₁ [i]

    [α∘i] : [ X , α ]⟶[ X , α ]
    [α∘i] = [α] ∘₁ [i]
 
    [!ₓ] : [ X , α ]⟶[ X , α ]
    [!ₓ] = ! (X , α)
 
    !ₓ : hom C X X
    !ₓ = proj₁ [!ₓ]
 
    idₓ : hom C X X
    idₓ = id
 
    [idₓ] : [ X , α ]⟶[ X , α ]
    [idₓ] = idₓ , idₓ∘α≡α∘F[idₓ]
      where
        idₓ∘α≡α∘F[idₓ] : idₓ ∘ α ≡ α ∘ F ⟦ idₓ ⟧
        idₓ∘α≡α∘F[idₓ] = begin
          idₓ ∘ α ≡⟨ id∘f≡f α ⟩
          α ≡˘⟨ f∘id≡f α ⟩
          α ∘ id {F [ X ]} ≡˘⟨ cong (α ∘_) respect-id ⟩
          α ∘ F ⟦ idₓ ⟧ ∎
 
  lambek : IsIsomorphism C (F [ X ]) X α i
  lambek = i∘α≡F[idₓ] , α∘i≡idₓ
    where
      α∘i≡idₓ : α ∘ i ≡ idₓ
      α∘i≡idₓ = begin
        α ∘ i ≡⟨ ,-injectiveˡ (!-unique (X , α) [α∘i]) ⟩
        !ₓ ≡˘⟨ ,-injectiveˡ (!-unique (X , α) [idₓ]) ⟩
        idₓ ∎

      i∘α≡F[idₓ] : i ∘ α ≡ id {F [ X ]}
      i∘α≡F[idₓ] = begin
        i ∘ α ≡⟨ proj₂ [i] ⟩
        F ⟦ α ⟧ ∘ F ⟦ i ⟧ ≡˘⟨ respect-∘ α i ⟩
        F ⟦ α ∘ i ⟧ ≡⟨ cong (F ⟦_⟧) α∘i≡idₓ ⟩
        F ⟦ idₓ ⟧ ≡⟨ respect-id ⟩
        id ∎
