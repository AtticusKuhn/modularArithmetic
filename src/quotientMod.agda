
{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
module quotientMod where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Data.Nat
-- open import Data.Integer
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : ℕ
  xs ys zs    : List A

data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

congApp : {f : A → B} →  x ≐ y → f x ≐ f y
congApp refl = refl

postulate
  transportR : (P : A → Set ℓ) → x ≐ y → P x → P y
  transportR-refl : transportR P refl x ≡ x
{-# REWRITE transportR-refl #-}
-- Now we can define the quotient type _//_. Specifically, given a type A and a Prop-valued relation R : A → A → Prop, we construct the type A // R consisting of elements proj x where x : A and proj x ≡ proj y if and only if R x y.

variable
  R : A → A → Prop

postulate
  _//_    : (A : Set ℓ) (R : A → A → Prop) → Set ℓ
  proj    : A → A // R
  quot    : R x y → proj {R = R} x ≐ proj {R = R} y
-- The crucial element here is the elimination principle //-elim, which allows us to define functions that extract an element of A from a given element of A // R, as long as we have a proof quot* that the function behaves the same on proj x and proj y whenever R x y holds. The computation rule //-beta turns this definition of quotients into more than just a static blob of postulates by allowing //-elim to compute when it is applied to a proj x.

  //-elim : (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → (x : A // R) → P x
  //-beta : {R : A → A → Prop} (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → {u : A} → //-elim P proj* quot* (proj u) ≡ proj* u
  -- Note: The type of //-beta mysteriously does not
  -- check when I leave out the {R : A → A → Prop},
  -- I'm not sure what's up with that.
{-# REWRITE //-beta #-}


postulate
  ℤ : Set
  diff : ℕ → ℕ → ℤ
  diffsuc : diff (suc m) (suc n) ≡ diff m n
  {-# REWRITE diffsuc #-}
  ℤelim : (P : Set)
    → (f : (m n : ℕ) → (P ))
    → ((m n : ℕ) → (f m n) ≐ f (suc m) (suc n))
    → (x : ℤ) → P
  ℤ-beta  : {P : Set} {f : ℕ → ℕ → P} {eq : (m n : ℕ) →  f m n ≐ f (suc m ) (suc n) } → ℤelim P f eq (diff m n) ≡ f m n
  {-# REWRITE ℤ-beta #-}


postulate
  sorry : {P : Prop } → P
addℤ : ℤ → ℤ → ℤ
addℤ a b = ℤelim  ℤ (ℤelim ( ℕ → ℕ → ℤ) (λ m n a b → diff (m + a) (n + b)) (λ m n → refl) a) (λ m n → sorry) b
  -- (ℤelim (λ x → ℕ → ℕ → ℤ) (λ m₁ n₁ a₁ b₁ → diff (m₁ + a₁) (n₁ + b₁)) _ a m n)
  --
postulate
  add-comm : (x y z : ℤ) → addℤ (addℤ x y) z ≡ addℤ x (addℤ y z)
-- add-comm x y z = ℤelim (addℤ (addℤ x y) z ≡ addℤ x (addℤ y z)) {!!} {!!} z

testAdd : addℤ (diff 3 5) (diff 7 2) ≡ diff 3 0
testAdd = refl

postulate
  Mod : ℤ → Set
  _ℤ%_ : (x : ℤ) → (k : ℤ) → (Mod k)
  ℤ%-beta : (x k : ℤ) → (addℤ k x) ℤ% k ≡ x ℤ% k
  {-# REWRITE ℤ%-beta #-}
  ModElim : {k : ℤ} → (P : Set) → (f : ℤ → P ) → ((x : ℤ) → f x ≐ f (addℤ x k)) → Mod k → P
  ModBeta : {x k : ℤ} {P : Set} {f : ℤ → P} {eq  :(x : ℤ) → f x ≐ f (addℤ x k)} →  ModElim P f eq (x ℤ% k) ≡ f x
  {-# REWRITE ModBeta #-}

-- test2 : (diff 7 0 ) ℤ% (diff 2 0) ≡ (diff 1 0) ℤ% (diff 2 0)
-- test2 = refl

addMod : { k : ℤ } → Mod k → Mod k → Mod k
addMod {k} a b = ModElim (Mod k) (λ x → ModElim (Mod k) (λ y →  (addℤ x  y) ℤ% k) (λ y → {!!}) a) (λ x → {!!}) b
