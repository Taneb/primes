{-# OPTIONS --without-K --guardedness #-}
module Main where

open import IO
open import Data.Nat.Base
open import Data.Nat.Show
open import Data.Nat.Primality.Factorization
open import Data.Maybe.Base hiding (_>>=_)
open import Function.Base

main : Main
main = run do
  n ← readMaybe 10 <$> getLine
  case n of λ
    { nothing  → pure _
    ; (just zero) → pure _
    ; (just (suc m)) → List.mapM′ (putStrLn ∘ show) (factors (factorize (suc m)))
    }

