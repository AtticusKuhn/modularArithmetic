module cyclicGroup where

open import Data.Integer
open import Data.Integer.Properties
open import Data.Nat using ( ℕ ; suc ; zero )
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Data.Fin using (Fin)
open import Agda.Builtin.Nat
  using (div-helper; mod-helper)
open import Function using (id)



variable
  x y k : ℤ
test :  + 5 % + 2 ≡ 1
test = refl

-- 5 mod -3 = 2
test2 : + 5 % -[1+ 2 ] ≡ 2
test2 = refl




record CyclicGroup ( n : ℤ ) : Set₁  where
  field
    ℤₙ : Set
    ⟦_⟧ₙ : ℤ → ℤₙ
    _+ₙ_ : ℤₙ → ℤₙ → ℤₙ
    homomorphism :  (x y : ℤ) → ⟦ x ⟧ₙ +ₙ ⟦ y ⟧ₙ ≡ ⟦ x + y ⟧ₙ
    loop : ⟦ n ⟧ₙ ≡  ⟦ +0 ⟧ₙ

cyclic0 : CyclicGroup +0
cyclic0 = record
           { ℤₙ = ℤ
           ; ⟦_⟧ₙ = id
           ; _+ₙ_ = _+_
           ; homomorphism = λ x y → refl
           ; loop = refl }

-- (x % (1 + n)) + (y % (1 + n)) = (x + y) % (1 + n)
open import Data.Nat.DivMod hiding (_%_)
auxHomomorphism  : (n : ℕ) →  (x y : ℤ)→
    (x %ℕ (ℕ.suc n) Data.Nat.+ y % +[1+ n ]) Data.Nat.% ℕ.suc n ≡
    (x + y) %ℕ (ℕ.suc n)
auxHomomorphism n (+_ n₁) (+_ n₂) = {!!}
auxHomomorphism n (+_ n₁) (-[1+_] n₂) = {!!}
auxHomomorphism n (-[1+_] n₁) (+_ n₂) = {!!}
auxHomomorphism n (-[1+_] n₁) (-[1+_] n₂) = {!!}
postulate
  modAux : (x n : ℕ) →  mod-helper x (ℕ.suc n) (ℕ.suc n) n ≡ 0
-- modAux x zero = refl
-- modAux x (ℕ.suc zero) = refl
-- modAux x (ℕ.suc (ℕ.suc n)) = {!!}
auxLoop : (n : ℕ) →  +[1+ n ] % +[1+ n ] ≡ +0 % +[1+ n ]
auxLoop zero = refl
auxLoop (ℕ.suc n) = modAux 1 n
cyclicsuc : (n : ℕ) → CyclicGroup (+ (ℕ.suc n))
cyclicsuc n =  record
                { ℤₙ = ℕ
                ; ⟦_⟧ₙ = λ x → x % (+ ℕ.suc n)
                ; _+ₙ_ = λ a b → (a Data.Nat.+ b) Data.Nat.% (ℕ.suc n)  -- Data.Nat._+_
                ; homomorphism = auxHomomorphism n
                ; loop = auxLoop n }
