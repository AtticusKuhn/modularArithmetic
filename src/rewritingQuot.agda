{-# OPTIONS --rewriting --prop -v rewriting:50 #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
-- As in the previous post, I will make heavy use of generalizable variables to make the code more readable. (Honestly, I’m not sure how I ever managed to write Agda code without them.)

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List A
-- Example 4: Quotient types
-- One of the well-known weak spots of intentional type theory is the poor handling of quotient types. One of the more promising attempts at adding quotients to Agda is by Guillaume Brunerie in the initiality project, which uses a combination of rewrite rules and Agda’s new (strict) Prop universe.

-- Before I can give the definition of the quotient type, we first need to define the Prop-valued equality type _≐_. We also define its corresponding notion of transport, which has to be postulated due to current limitations in the implementation of Prop. Luckily, we can actually make transportR compute in the expected way by postulating the expected computational behaviour and turning it into a rewrite rule.

data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

symP : {x y : A} → x ≐ y → y ≐ x
symP refl = refl

transP : { x y z : A } → x ≐ y → y ≐ z → x ≐ z
transP refl refl = refl
-- substP : ∀ {A : Set } {x y : A} (P : A → Set)
  -- → x ≐ y

  -- → P x → P y
-- substP P refl px = px
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
-- (As a side note, here is an interesting recent discussion on quotient types in Lean, Coq, and Agda.)
