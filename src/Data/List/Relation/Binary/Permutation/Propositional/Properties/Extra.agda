{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Extra properties about permutations
------------------------------------------------------------------------
module Data.List.Relation.Binary.Permutation.Propositional.Properties.Extra where

open import Data.List.Base
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; cong; cong₂; module ≡-Reasoning)

productPreserves↭⇒≡ : product Preserves _↭_ ⟶ _≡_
productPreserves↭⇒≡ refl = refl
productPreserves↭⇒≡ (prep x r) = cong (x *_) (productPreserves↭⇒≡ r)
productPreserves↭⇒≡ (trans r s) = ≡.trans (productPreserves↭⇒≡ r) (productPreserves↭⇒≡ s)
productPreserves↭⇒≡ (swap {xs} {ys} x y r) = begin
  x * (y * product xs) ≡˘⟨ *-assoc x y (product xs) ⟩
  (x * y) * product xs ≡⟨ cong₂ _*_ (*-comm x y) (productPreserves↭⇒≡ r) ⟩
  (y * x) * product ys ≡⟨ *-assoc y x (product ys) ⟩
  y * (x * product ys) ∎
  where
    open ≡-Reasoning
