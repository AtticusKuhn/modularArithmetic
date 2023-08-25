module homomorphism where

open import Relation.Binary.PropositionalEquality; open ≡-Reasoning

open import Data.Nat
variable
  t s : Set
record Ring (t : Set) : Set where
  field
    Rzero : t
    add : t → t → t
    x+0=x : (x : t) → add x Rzero ≡ x
    x+y=y+x : (x y : t) → add x y ≡ add y x
    associate+ : (x y z : t) → add x (add y z) ≡ add (add x y) z
    negate : t → t
    x-x=0 : (x : t) → add x (negate x) ≡ Rzero
    one : t
    mul : t → t → t
    x*1=x : (x : t) → mul x one ≡ x
    1*x=x : (x : t) → mul one x ≡ x
    associate* : (x y z : t) → mul x (mul y z) ≡ mul (mul x y) z
    distribr : (x y z : t) → mul x (add y z) ≡ add (mul x y) (mul x z)
    distribl : (x y z : t) → mul  (add y z) x ≡ add (mul y x) (mul z x)
open Ring public
repeatedAdd : {t : Set} (R : Ring t) (times : ℕ) → t
repeatedAdd R zero = one R
repeatedAdd R (suc n) = (add R (one R) (repeatedAdd R n))

record HasOrder {t : Set} (R : Ring t) (n : ℕ) : Set where
  field
    isZero : repeatedAdd R n ≡ Rzero R
    lessNumber : (m : ℕ) → (m < n) → repeatedAdd R n ≢ Rzero R


record Homomorphism {t s : Set} (R : Ring t) (S : Ring s) : Set where
  field
    f : t → s
    fone : f (one R) ≡ one S
    fadd : (a b : t) → f (add R a b) ≡ add S (f a) (f b)
    fmul : (a b : t) → f (mul R a b) ≡ mul S (f a) (f b)


record OrderedRing (t : Set) (n : ℕ) : Set where
  field
    {{ring}} : Ring t
    order : HasOrder ring n




data divides : ℕ → ℕ → Set where
  multiple : (a b : ℕ) → divides a (a * b)

mod : (a b : ℕ) → (R : Ring t ) → HasOrder R a → (S : Ring t) → HasOrder S b → (divides b a) →  Homomorphism R S
mod  a b R x S orderS b|a = record {
  f = λ t → t
  ; fone = {!!}
  ; fadd = {!!}
  ; fmul = {!!}
  }
