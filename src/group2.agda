
module group2 where

open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Data.Integer

record Group (T : Set) : Set where
  field
    add : T → T → T
    inverse : T → T
    Z : T
    -- laws:
    -- addZ : (x : T) → add Z x ≡ x
    -- addInv : (x : T) → add x (inverse x) ≡ Z
    -- Invadd : (x : T) → add (inverse x) x ≡ Z


open Group ⦃ ... ⦄ public

open import Data.Nat hiding (_+_)
open import Function using (const)
repeat : {T : Set} ⦃ _ : Group T ⦄ →  ℕ → T → T
repeat 0  = const Z
repeat (suc n) x = add x (repeat n x)

repeatℤ : {T : Set} ⦃ _ : Group T ⦄ → ℤ → T → T
repeatℤ  (+[1+ n ]) x = add x (repeatℤ (+ n) x)
repeatℤ (+0) = const Z
repeatℤ (-[1+ 0 ]) = inverse
repeatℤ (-[1+ (suc n) ]) x = add (inverse x) (repeatℤ (-[1+ n ]) x)

open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

record CyclicGroup (T  : Set) ⦃ _ : Group T ⦄ : Set where
  field
    generator : T
    --- Laws:
    -- generates :  (x : T) → Σ[ n ∈ ℤ ] repeatℤ n generator ≡ x

open CyclicGroup ⦃ ... ⦄ public


record GroupHomomorphism {T S : Set} (A : Group T) (B : Group S) : Set where
  field
    f : T → S
    -- Laws
    -- fZ : f (Z {{A}}) ≡ (Z {{B}})
    -- fadd : (a b : T) → f (add {{A}} a b) ≡ add {{B}} (f a) (f b)
open GroupHomomorphism ⦃ ... ⦄ public

record CyclicGroupHomomorphism {T S : Set} ⦃ GT : Group T ⦄ ⦃ GS : Group S ⦄ ⦃ _ : GroupHomomorphism GT GS ⦄  (A : CyclicGroup T) (B : CyclicGroup S) : Set where
  field
    mapsGens : f (generator {{GT}} {{A}} ) ≡ generator {{GS}} {{B}}

open import Data.Bool
ℕOdd : ℕ → Bool
ℕOdd 0 = false
ℕOdd 1 = true
ℕOdd (suc (suc n)) = ℕOdd n
ℤOdd : ℤ → Bool
ℤOdd (+ x) = ℕOdd x
ℤOdd (-[1+ x ]) = not (ℕOdd x)
instance
  ℤGroup : Group ℤ
  ℤGroup = record {
    add = _+_
    ; inverse = -_
    ; Z = +0
    }

  ℤcyclic : CyclicGroup ℤ
  ℤcyclic = record {
    generator = + 1
    }

  BoolGroup : Group Bool
  BoolGroup = record {
    add = _∧_
    ; inverse = not
    ; Z = false
    }

  BoolCyclic : CyclicGroup Bool
  BoolCyclic = record {
    generator = true
    }

  ℤ→Bool : GroupHomomorphism ℤGroup BoolGroup
  ℤ→Bool = record {
    f = ℤOdd
    }

  ℤ→Bool’ : CyclicGroupHomomorphism (ℤcyclic) (BoolCyclic)
  ℤ→Bool’ = record {
    mapsGens = refl
    }
