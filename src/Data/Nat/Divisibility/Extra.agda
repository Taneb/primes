{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Extra properties of divisibility of naturals
------------------------------------------------------------------------
module Data.Nat.Divisibility.Extra where

open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- if m ∣ n, the quotient of the division also ∣ n
∣-comm : ∀ {m n} → (m∣n : m ∣ n) → quotient m∣n ∣ n
∣-comm {m = m} m∣n = record
  { quotient = m
  ; equality = trans (_∣_.equality m∣n) (*-comm (quotient m∣n) m)
  }
