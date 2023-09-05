open import Data.Nat using (ℕ ; suc)
module fin (n : ℕ) where
open import Data.Integer hiding (suc)
open import Data.Fin using (Fin ; toℕ)



-- this is a hack to avoid mod 0
-- while mod 0 is mathematically valid
-- mod 0 does not produce any computational insights
-- I wish there were a more elegant way of doing this
kℕ : ℕ
kℕ = suc n
k : ℤ
k = + kℕ

modk : Set
modk = Fin kℕ

variable
  a b c d e : ℤ
  A B : Set
  f : ℤ → ℤ


⟦_⟧ : modk → ℤ
⟦ mk ⟧ = + (toℕ mk)

-- congruence modulo k
infix 4 _≈’_
data _≈’_ : ℤ → ℤ → Set where
  step≈ : (c : ℤ) →  a ≈’ a + c * k
