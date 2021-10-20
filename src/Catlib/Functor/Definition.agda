module Catlib.Functor.Definition where
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Catlib.Category.Definition

record Functor {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  (ℂ : Category {a} {b} obℂ) (𝔻 : Category {c} {d} ob𝔻)
  : Set (a ⊔ (suc b) ⊔ c ⊔ (suc d)) where
  constructor aFunctor
  field
    ₀ : obℂ → ob𝔻
    ₁ : {X Y : obℂ} → ( ℂ ⦅ X ⟶ Y ⦆ ) → ( 𝔻 ⦅ ₀ X ⟶ ₀ Y ⦆ )
    id-id : {X : obℂ} → ₁ id[ ℂ , X ] ≡ id[ 𝔻 , ₀ X ]
    comp-comp : {X Y Z : obℂ} → (f : ℂ ⦅ X ⟶ Y ⦆) → (g : ℂ ⦅ Y ⟶ Z ⦆)
      → ₁ (g ∘[ ℂ ] f) ≡ ₁ g ∘[ 𝔻 ] ₁ f

₀-syntax : {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  {ℂ : Category {a} {b} obℂ} {𝔻 : Category {c} {d} ob𝔻}
  (F : Functor ℂ 𝔻)
  → (obℂ → ob𝔻)
₀-syntax F X = Functor.₀ F X
syntax ₀-syntax F X = F [ X ]

₁-syntax : {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  {ℂ : Category {a} {b} obℂ} {𝔻 : Category {c} {d} ob𝔻}
  {X Y : obℂ}
  (F : Functor ℂ 𝔻)
  → ( ℂ ⦅ X ⟶ Y ⦆ ) → ( 𝔻 ⦅ F [ X ] ⟶ F [ Y ] ⦆)
₁-syntax F f = Functor.₁ F f
syntax ₁-syntax F f = F ⟨ f ⟩
