
module pairs where

open import Data.Nat -- hiding (_%_)
open import Data.Product
open import Data.Bool hiding (_≤?_)
open import Relation.Nullary.Decidable using (isYes ; ⌊_⌋; True; toWitness; fromWitness)
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
ℤ : Set
ℤ = ℕ × ℕ

normalize : ℤ → ℤ
normalize (x  , 0 ) = (x , 0)
normalize (0  , y ) = (0 , y)
normalize (suc x , suc y) = normalize (x , y)
postulate
  norm-id : (x : ℤ) → normalize x ≡ x
-- {-# TERMINATING #-}
-- _%_ : ℕ → ℕ → ℕ
-- a % 0 = a
-- a % (suc b) with (compare a (suc b))
-- ... | less m k = a
-- ... | equal m = 0
-- ... | greater m k = (suc k) % (suc b)

_%ℕ_ : ℕ → ℕ → ℕ
a %ℕ 0 = a
a %ℕ (suc b) = a % (suc b)
n%n : (n : ℕ) → n %ℕ n ≡ 0
n%n zero  = refl
n%n (suc n)  = n%n≡0 (suc n)

abs : ℤ → ℕ
abs (zero , zero) = zero
abs (zero , suc b) = suc b
abs (suc a , zero) = suc a
abs (suc a , suc b) = abs (a , b)

modℤ : ℤ → ℤ → ℤ
modℤ (x , y) mod = normalize (x %ℕ abs mod , y %ℕ abs mod)

addℤ : ℤ → ℤ → ℤ
addℤ (a , b) (x , y) = normalize (a + x , b + y)
test1 : modℤ (5 , 1) (4 , 2) ≡ ( 0 , 0 )
test1 = refl


⟦ℤ⟧ : Set
⟦ℤ⟧ = ℤ

meaning : ℤ →  ℤ → ⟦ℤ⟧
meaning x k = modℤ x  k

0ℤ : ℤ
0ℤ = ( 0 , 0 )
⟦k⟧=0 : (k : ℤ) → meaning k k ≡ 0ℤ
⟦k⟧=0 (zero , zero) = refl
⟦k⟧=0 (zero , suc snd) = {!!}
⟦k⟧=0 (suc fst , zero) = {!!}
⟦k⟧=0 (suc fst , suc snd) = {!!}

addMod : ⟦ℤ⟧ → ⟦ℤ⟧ → ℤ → ⟦ℤ⟧
addMod  x y k = modℤ (addℤ x y) k
modℤidempotent : (x k : ℤ) → modℤ (modℤ x k) k ≡ modℤ x k
modℤidempotent  = {!!}

mod-distributesover-add : (x y k : ℤ) →  modℤ (addℤ x y) k ≡  modℤ (addℤ (modℤ x k) (modℤ y k)) k
mod-distributesover-add (a , b) (c , d) (e , f) rewrite (norm-id (a + c , b + d)) | (norm-id ((a + c) %ℕ abs (e , f) , (b + d) %ℕ abs (e , f))) = begin
    ((a + c) %ℕ abs (e , f)  , (b + d) %ℕ abs (e , f))
    ≡⟨ {!!} ⟩
    modℤ (addℤ (modℤ (a , b) (e , f)) (modℤ (c , d) (e , f))) (e , f)
  ∎

⟦addMod⟧ : (x y k : ℤ) → meaning (addℤ x y) k ≡ addMod (meaning x k) (meaning y k) k
⟦addMod⟧ x y k = begin
         meaning (addℤ x y) k
         ≡⟨⟩
         modℤ (addℤ x y) k
         ≡⟨ mod-distributesover-add x y k ⟩
         modℤ (addℤ (modℤ x k) (modℤ y k)) k
         ≡⟨⟩
         addMod (meaning x k) (meaning y k) k
  ∎
