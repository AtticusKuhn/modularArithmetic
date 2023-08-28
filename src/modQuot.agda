{-# OPTIONS --rewriting --prop -v rewriting:50 #-}

module modQuot where
open import rewritingQuot

open import Data.Product using (∃; _,_)
open import Data.Integer

open import Relation.Binary.PropositionalEquality


data divides : ℤ → ℤ → Prop where
  makeDiv : (a b x : ℤ) → (b ≐ (a * x)) → divides a b

equivk : ℤ → ℤ → ℤ → Prop
equivk k a b = divides k (a - b)

mod : ℤ → Set
mod k = ℤ // equivk k

-- divides+ : (a b k : ℤ) → divides k a → divides k b → divides k (a + b)
-- divides+ a b k kda kdb = {!!}


addModfst : (j x y k : ℤ) →   equivk k x y → proj {R = equivk k} (j + x) ≐ proj (j + y)
addModfst j x y k (makeDiv .k .(x - y) r s) = quot (makeDiv k ((j + x) - (j + y)) r (symP (transP (symP s) {!!})))


-- addModsnd : (j x y k : ℤ) →   equivk k x y → proj {R = equivk k} (x + j) ≐ proj ( y + j)
-- addModsnd j x y k (makeDiv .k .(x - y) r s) = transportR (λ c  →  {!!}) {!!} {!!} {!!}

addMod : (k : ℤ) → mod k → mod k → mod k
addMod k a b = //-elim
  (λ _ →   mod k)
  (λ j → //-elim
    (λ _ → mod k )
    (λ z → proj (j + z)) (λ r → {!!}) a)
  (λ r → {!!}) b
