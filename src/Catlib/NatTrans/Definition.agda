module Catlib.NatTrans.Definition where
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Catlib.Category.Definition
open import Catlib.Functor.Definition

record NatTrans {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  {ℂ : Category {a} {b} obℂ} {𝔻 : Category {c} {d} ob𝔻}
  (F G : Functor ℂ 𝔻)
  : Set (a ⊔ (suc b) ⊔ c ⊔ (suc d)) where
  constructor aNatTrans
  field
    α : {X : obℂ} → 𝔻 ⦅ F [ X ] ⟶ G [ X ] ⦆
    {-
    foall f : X → Y in ℂ,
    FX -Ff→ FY
    |        |
    αX  ↺    αY
    ↓        ↓
    GX -Gf→ GY
    in ob𝔻
    -}
    com : {X Y : obℂ} {f : ℂ ⦅ X ⟶ Y ⦆} → (G ⟨ f ⟩) ∘[ 𝔻 ] α ≡ α ∘[ 𝔻 ] (F ⟨ f ⟩)

nat : {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  {ℂ : Category {a} {b} obℂ} {𝔻 : Category {c} {d} ob𝔻}
  {F G : Functor ℂ 𝔻}
  (α : NatTrans F G)
  → {X : obℂ} → 𝔻 ⦅ F [ X ] ⟶ G [ X ] ⦆
nat α = NatTrans.α α

α-syntax : {a b c d : Level} {obℂ : Set a} {ob𝔻 : Set c}
  {ℂ : Category {a} {b} obℂ} {𝔻 : Category {c} {d} ob𝔻}
  {F G : Functor ℂ 𝔻}
  (α : NatTrans F G)
  → (X : obℂ) → 𝔻 ⦅ F [ X ] ⟶ G [ X ] ⦆
α-syntax α X = nat α {X}
syntax α-syntax α X = α ⟦ X ⟧
