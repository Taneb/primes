{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Extra properties of prime numbers
------------------------------------------------------------------------
module Data.Nat.Primality.Extra where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Sum.Base
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

∣p⇒≡p∨≡1 : ∀ m {p} → Prime p → m ∣ p → m ≡ p ⊎ m ≡ 1
∣p⇒≡p∨≡1 zero {p} p-prime m∣p = contradiction (0∣⇒≡0 m∣p) λ p≡0 → subst Prime p≡0 p-prime
∣p⇒≡p∨≡1 (suc zero) {p} p-prime m∣p = inj₂ refl
∣p⇒≡p∨≡1 (suc (suc m)) {suc (suc p)} p-prime m∣p = inj₁ (≤∧≮⇒≡ (∣⇒≤ m∣p) λ m<p → p-prime (s≤s (s≤s z≤n)) m<p m∣p)

Prime⇒NonZero : ∀ {n} → Prime n → NonZero n
Prime⇒NonZero {suc n} n-prime = _
