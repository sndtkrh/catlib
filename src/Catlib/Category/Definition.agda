module Catlib.Category.Definition where
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Category {a b : Level} (obj : Set a) : Set (a ⊔ (suc b)) where
  constructor aCategory
  field
    hom : obj → obj → Set b
    id : {X : obj} → hom X X
    comp : {X Y Z : obj} → hom X Y → hom Y Z → hom X Z
    id-comp : {X Y : obj} → (f : hom X Y) → comp id f ≡ f
    comp-id : {X Y : obj} → (f : hom X Y) → comp f id ≡ f
    assoc : {W X Y Z : obj} → (f : hom W X) → (g : hom X Y) → (h : hom Y Z)
      → comp (comp f g) h ≡ comp f (comp g h)

hom-syntax : {a b : Level} {obj : Set a}
  → (ℂ : Category {a} {b} obj)
  → (X Y : obj)
  → Set b
hom-syntax ℂ X Y = Category.hom ℂ X Y
syntax hom-syntax ℂ X Y = ℂ ⦅ X ⟶ Y ⦆

id-syntax : {a b : Level} {obj : Set a}
  → (ℂ : Category {a} {b} obj)
  → (X : obj)
  → Category.hom ℂ X X
id-syntax ℂ X = Category.id ℂ
syntax id-syntax ℂ X = id[ ℂ , X ]

comp-syntax :  {a b : Level} {obj : Set a} {X Y Z : obj}
  → (ℂ : Category {a} {b} obj)
  → (f : ℂ ⦅ X ⟶ Y ⦆) → (g : ℂ ⦅ Y ⟶ Z ⦆)
  → ℂ ⦅ X ⟶ Z ⦆
comp-syntax ℂ f g = Category.comp ℂ f g
syntax comp-syntax ℂ f g = g ∘[ ℂ ] f
