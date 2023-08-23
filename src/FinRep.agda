
module FinRep where
open import Data.Nat
open import Data.Integer
open import Data.Fin

Mod : ℕ → Set
Mod 0 = ℤ
Mod (suc n) = Fin (ℕ.suc n)

meaning : (k : ℕ) → ℤ → Mod k
meaning zero x = x
meaning (ℕ.suc k) x = {!!}
