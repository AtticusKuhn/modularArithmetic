{-# OPTIONS --cubical #-}
module modular where

open import Data.Integer
open import Data.Integer.Properties
open import Data.Nat using ( ℕ ; suc ; zero )
-- open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Data.Fin using (Fin)
open import Agda.Builtin.Nat
  using (div-helper; mod-helper)

open import Cubical.Foundations.Prelude


variable
  x y k : ℤ

modℕ : ℕ → Type
modℕ 0 = ℤ
modℕ (suc n) = Fin (ℕ.suc n)

-- ⟦_⟧ : ℤ → modℕ k
-- ⟦ x ⟧ =
Modℤ : ℤ → Type
Modℤ (+ k) = modℕ k
Modℤ (-[1+ k ]) = modℕ (ℕ.suc k)
-- Mod’
-- data Mod2 : Type where
  -- meaning-2  : ℤ → Mod2
  -- 2-eq : meaning-2 (+0) ≡ meaning-2 (+2)
open import Function
data Mod’ (k : ℤ) : Type where
  meaning :  ℤ → Mod’ k
  eq : meaning ≡ meaning ∘ (_+ k)

data Modk (k : ℤ) : Type where
  ⟦_⟧ₖ :  ℤ → Modk k
  eq : ⟦ x ⟧ₖ ≡ ⟦ x + k ⟧ₖ


-- reduce : (n : ℤ) → (mod : ℤ) → ℤ
-- reduce n (+0) = n
-- reduce n +[1+ mod ] = (sign n) ◃ ( ∣ n ∣ % (ℕ.suc mod))
-- reduce n (-[1+ mod ]) = {!!}

test :  + 5 % + 2 ≡ 1
test = refl

-- 5 mod -3 = 2
test2 : + 5 % -[1+ 2 ] ≡ 2
test2 = refl

0mod : Mod’ k
0mod = meaning (+0)

ℤ→Mod0 : Mod’ (+0) → ℤ
ℤ→Mod0 (meaning x) = x
ℤ→Mod0 (eq i x) rewrite (+-identityʳ x) = x
open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism


record CyclicGroup ( n : ℤ ) : Type₁  where
  field
    ℤₙ : Type
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


auxHomomorphism  : (n : ℕ) →  (x y : ℤ)→
    (x % +[1+ n ] Data.Nat.+ y % +[1+ n ]) Data.Nat.% ℕ.suc n ≡
    (x + y) % +[1+ n ]
auxHomomorphism zero x y = {!!}
auxHomomorphism (ℕ.suc n) x y = {!!}
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
-- ncyclic : (n : ℤ) → CyclicGroup n
-- ncyclic  n = record
--               { ℤₙ = ℕ
--               ; ⟦_⟧ₙ = λ x → x % n
--               ; _+ₙ_ = {!!}
--               ; homomorphism = {!!}
--               ; loop = {!!} }

-- cyclicMod : (k : ℤ) →  CyclicGroup k
-- cyclicMod k = record {
--   t = Mod’ k
--   ; from-int = meaning
--   ; add = {!!}
--   ; homomorphism = {!!}
--   ; loop = {!!}
  -- }
    
-- ℤ≡mod0 : ℤ ≡ Mod’ (+0)
-- ℤ≡mod0 = isoToPath (iso meaning ℤ→Mod0 {!!} {!!})
-- isset : isSet (Mod’ k)
-- isset  = isSetRetract (λ x → {!!}) (meaning) {!!} {!isSetℤ!}

-- Mod’suc : Mod’ k → Mod’ k
-- Mod’suc (meaning x) = meaning (Data.Integer.suc x)
-- Mod’suc (eq  x i) = eq {!!} i


-- ⟦_⟧ₖ : {k : ℕ} →  ℤ → Mod k
-- ⟦ x ⟧ₖ = if (x < 0) th
postulate
  Mod : ℤ → Set
  -- ⟦_⟧ₖ : ℤ → Mod k
  -- mod-eq : ⟦ x + k ⟧ₖ ≡ ⟦ x ⟧ₖ
  _+ₖ_ :   Mod k → Mod k → Mod k
  -- _⟦+ₖ⟧ₖ_ : {k : ℕ} →  (x y : ℤ) → ⟦ x + y ⟧ₖ ≡ ⟦ x ⟧ₖ +ₖ ⟦ y ⟧ₖ
