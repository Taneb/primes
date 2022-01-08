{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- A rough number is a one without small prime factors.
------------------------------------------------------------------------
module Data.Nat.Rough where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.Induction
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Product
open import Function.Base
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality

-- A number is k-rough if all its prime factors are greater than or equal to k
_Rough_ : ℕ → ℕ → Set
k Rough n = ∀ {d} → d < k → Prime d → d ∤ n

-- any number is 2-rough because all primes are greater than or equal to 2
2-rough-n : ∀ n → 2 Rough n
2-rough-n n {suc (suc d)} (s≤s (s≤s ())) d-prime

-- if a number is k-rough, and it's not a multiple of k, then it's (k+1)-rough
extend-∤ : ∀ {k n} → k Rough n → k ∤ n → suc k Rough n
extend-∤ {k = k} k-rough-n k∤n {suc d} (s≤s d<k) d-prime with suc d ≟ k
... | yes refl = k∤n
... | no  d≢k  = k-rough-n (≤∧≢⇒< d<k d≢k) d-prime

-- if a number is k-rough, and k is composite, then the number is (k+1)-rough
extend-composite : ∀ {k n} → k Rough n → ¬ Prime k → suc k Rough n
extend-composite {k = k} k-rough-n ¬k-prime {d} (s≤s d<k) d-prime with d ≟ k
... | yes refl = contradiction d-prime ¬k-prime
... | no  d≢k  = k-rough-n (≤∧≢⇒< d<k d≢k) d-prime

-- 1 is always rough
b-rough-1 : ∀ k → k Rough 1
b-rough-1 k {d} d<k d-prime d∣1 with ∣1⇒≡1 d∣1
... | refl = d-prime

-- if a number is k-rough, then so are all of its divisors
reduce-∣ : ∀ {k m n} → k Rough m → n ∣ m → k Rough n
reduce-∣ k-rough-n n∣m d<k d-prime d∣n = k-rough-n d<k d-prime (∣-trans d∣n n∣m)

-- if a number is k-rough, then no number 2 ≤ d < k will divide it, whether prime or not
rough⇒∤ : ∀ {d k n} → k Rough n → 2 ≤ d → d < k → d ∤ n
rough⇒∤ {d} {k} {n} k-rough-n = <-rec (λ d′ → 2 ≤ d′ → d′ < k → d′ ∤ n) (rough⇒∤Rec k-rough-n) d
  where
    rough⇒∤Rec : ∀ {n k} → k Rough n → ∀ d → <-Rec (λ d′ → 2 ≤ d′ → d′ < k → d′ ∤ n) d → 2 ≤ d → d < k → d ∤ n
    rough⇒∤Rec {n} {k} k-rough-n (suc (suc d)) rec (s≤s (s≤s z≤n)) d<k with composite? (2 + d)
    ... | yes (d′ , 2≤d′ , d′<d , d′∣d) = rec d′ d′<d 2≤d′ (<-trans d′<d d<k) ∘ ∣-trans d′∣d
    ... | no ¬d-composite = k-rough-n {2 + d} d<k (¬composite⇒prime (s≤s (s≤s z≤n)) ¬d-composite)

-- if a number is k-rough, and k divides it, then it must be prime
roughn∧∣n⇒prime : ∀ {k n} → k Rough n → 2 ≤ k → k ∣ n → Prime k
roughn∧∣n⇒prime {k = suc (suc k)} {n = n} k-rough-n (s≤s (s≤s z≤n)) k∣n
  = <-rec (λ d → 2 ≤ d → d < 2 + k → d ∤ 2 + k) (roughn∧∣n⇒primeRec k-rough-n k∣n) _
  where
  roughn∧∣n⇒primeRec : ∀ {k n} → k Rough n → k ∣ n → ∀ d → <-Rec (λ d′ → 2 ≤ d′ → d′ < k → d′ ∤ k) d → 2 ≤ d → d < k → d ∤ k
  roughn∧∣n⇒primeRec {k} {n} k-rough-n k∣n (suc (suc d)) rec (s≤s (s≤s z≤n)) d<k with composite? (2 + d)
  ... | yes (d′ , 2≤d′ , d′<d , d′∣d) = rec d′ d′<d 2≤d′ (<-trans d′<d d<k) ∘ ∣-trans d′∣d
  ... | no ¬d-composite = k-rough-n d<k (¬composite⇒prime (s≤s (s≤s z≤n)) ¬d-composite) ∘ flip ∣-trans k∣n

