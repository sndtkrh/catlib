module Catlib.Functor.Definition where
open import Level using (Level; _â_; suc)
open import Relation.Binary.PropositionalEquality using (_â¡_)

open import Catlib.Category.Definition

record Functor {a b c d : Level} {obâ : Set a} {obð» : Set c}
  (â : Category {a} {b} obâ) (ð» : Category {c} {d} obð»)
  : Set (a â (suc b) â c â (suc d)) where
  constructor aFunctor
  field
    â : obâ â obð»
    â : {X Y : obâ} â ( â â¦ X â¶ Y â¦ ) â ( ð» â¦ â X â¶ â Y â¦ )
    id-id : {X : obâ} â â id[ â , X ] â¡ id[ ð» , â X ]
    comp-comp : {X Y Z : obâ} â (f : â â¦ X â¶ Y â¦) â (g : â â¦ Y â¶ Z â¦)
      â â (g â[ â ] f) â¡ â g â[ ð» ] â f

â-syntax : {a b c d : Level} {obâ : Set a} {obð» : Set c}
  {â : Category {a} {b} obâ} {ð» : Category {c} {d} obð»}
  (F : Functor â ð»)
  â (obâ â obð»)
â-syntax F X = Functor.â F X
syntax â-syntax F X = F [ X ]

â-syntax : {a b c d : Level} {obâ : Set a} {obð» : Set c}
  {â : Category {a} {b} obâ} {ð» : Category {c} {d} obð»}
  {X Y : obâ}
  (F : Functor â ð»)
  â ( â â¦ X â¶ Y â¦ ) â ( ð» â¦ F [ X ] â¶ F [ Y ] â¦)
â-syntax F f = Functor.â F f
syntax â-syntax F f = F â¨ f â©
