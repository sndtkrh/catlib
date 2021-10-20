module Catlib.Category.Instance where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; _≤_; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

open import Catlib.Category.Definition

data one : Set where
  • : one

Trivial : Category one
Trivial = Cat hom id comp id-comp comp-id assoc
  where
    hom : one → one → Set
    hom • • = one

    id : {X : one} → hom X X
    id {•} = •

    comp : {X Y Z : one} → hom X Y → hom Y Z → hom X Z
    comp {•} {•} {•} • • = •

    id-comp : {X Y : one} (f : hom X Y) → comp id f ≡ f
    id-comp {•} {•} • = refl

    comp-id : {X Y : one} (f : hom X Y) → comp f id ≡ f
    comp-id {•} {•} • = refl

    assoc : {W X Y Z : one} (f : hom W X) (g : hom X Y) (h : hom Y Z) →
      comp (comp f g) h ≡ comp f (comp g h)
    assoc {•} {•} {•} {•} • • • = refl

Types : Category Set
Types = Cat (λ X Y → (X → Y)) (λ x → x) (λ f g x → g (f x))
  (λ f → refl) (λ f → refl) (λ f g h → refl)

ℕ≤ : Category ℕ
ℕ≤ = Cat _≤_ ≤-refl ≤-trans id-comp comp-id assoc
 where
   id-comp : {X Y : ℕ} (f : X ≤ Y) → ≤-trans ≤-refl f ≡ f
   id-comp {.zero} {Y} z≤n = refl
   id-comp {.(suc _)} {.(suc _)} (s≤s f) = cong s≤s (id-comp f)

   comp-id : {X Y : ℕ} (f : X ≤ Y) → ≤-trans f ≤-refl ≡ f
   comp-id {.zero} {Y} z≤n = refl
   comp-id {.(suc _)} {.(suc _)} (s≤s f) = cong s≤s (comp-id f)

   assoc : {W X Y Z : ℕ} (f : W ≤ X) (g : X ≤ Y) (h : Y ≤ Z) →
     ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
   assoc {.zero} {X} {Y} {Z} z≤n g h = refl
   assoc {.(suc _)} {.(suc _)} {.(suc _)} {.(suc _)} (s≤s f) (s≤s g) (s≤s h) =
     cong s≤s (assoc f g h)
   
