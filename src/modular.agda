{-# OPTIONS --cubical #-}
module modular where

open import Data.Integer
open import Data.Integer.Properties
open import Data.Nat using ( ℕ ; suc ; zero )
-- open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Data.Fin using (Fin)

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
    homomorphism :  ⟦ x ⟧ₙ +ₙ ⟦ y ⟧ₙ ≡ ⟦ x + y ⟧ₙ
    loop : ⟦ n ⟧ₙ ≡  ⟦ +0 ⟧ₙ

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
