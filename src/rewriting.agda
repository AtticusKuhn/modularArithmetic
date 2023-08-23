{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
module rewriting where

open import Data.Nat
open import Data.Product
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

variable
  m n : ℕ

data ℤ : Set where
  diff : ℕ → ℕ → ℤ

variable
  x y k : ℤ

postulate
  diffsuc : diff (suc m) (suc n) ≡ diff m n

1ℤ : ℤ
1ℤ = diff 1 0
{-# REWRITE diffsuc #-}

_%ℕ_ : ℕ → ℕ → ℕ
a %ℕ 0 = a
a %ℕ (suc b) = a % (suc b)

abs : ℤ → ℕ
abs (diff x 0) = x
abs (diff 0 y) = y
abs (diff (suc x) (suc y)) = abs (diff x y)

modℤ : ℤ → ℤ → ℤ
modℤ (diff a b) k = diff (a %ℕ abs k) (b %ℕ abs k)

addℤ : ℤ → ℤ → ℤ
addℤ (diff a b) (diff x y) = diff (a + x) (b + y)

mulℤ : ℤ → ℤ → ℤ
mulℤ (diff a b) (diff x y) = diff (a * x + b * y) (a * y + b * x)

negateℤ : ℤ → ℤ
negateℤ (diff a b) = diff b a

%ℕ-distrib+ : (a b k : ℕ) → (a + b) %ℕ k ≡ ((a %ℕ k) + (b %ℕ k)) %ℕ k
%ℕ-distrib+ a b zero = refl
%ℕ-distrib+ a b (suc k) = %-distribˡ-+ a b (suc k)

%ℕ-distrib* : (a b k : ℕ) → (a * b) %ℕ k ≡ ((a %ℕ k) * (b %ℕ k)) %ℕ k
%ℕ-distrib* a b zero = refl
%ℕ-distrib* a b (suc k) = %-distribˡ-* a b (suc k)

%ℕ-idempotent : (a k : ℕ) → (a %ℕ k) %ℕ k ≡ a %ℕ k
%ℕ-idempotent a 0 = refl
%ℕ-idempotent a (suc k) = m%n%n≡m%n a (suc k)

mod-distributesover-add : (x y k : ℤ) →  modℤ (addℤ x y) k ≡  modℤ (addℤ (modℤ x k) (modℤ y k)) k
mod-distributesover-add (diff a b) (diff x y) k rewrite (%ℕ-distrib+ a x (abs k)) | (%ℕ-distrib+ b y (abs k)) = refl -- begin


mod-distributesover-mul : (x y k : ℤ) →  modℤ (mulℤ x y) k ≡  modℤ (mulℤ (modℤ x k) (modℤ y k)) k
mod-distributesover-mul (diff a b) (diff x y) k
  rewrite (%ℕ-distrib+ (a * x) ( b * y ) (abs k))
  | (%ℕ-distrib+ (a * y) (b * x) (abs k))
  |  (%ℕ-distrib* a x (abs k))
  | (%ℕ-distrib* b y (abs k))
  |  (%ℕ-distrib* a y (abs k))
  | (%ℕ-distrib* b x (abs k))
  | (%ℕ-distrib+ ((((a %ℕ abs k) * (x %ℕ abs k)))  )  ((b %ℕ abs k * y %ℕ abs k)) (abs k))
  | (%ℕ-distrib+ ((((a %ℕ abs k) * (y %ℕ abs k)))  )  ((b %ℕ abs k * x %ℕ abs k)) (abs k))
  | (%ℕ-distrib* (a %ℕ abs k) (x %ℕ abs k) (abs k))
  | (%ℕ-distrib* (b %ℕ abs k) (y %ℕ abs k) (abs k))
  | %ℕ-idempotent (a) (abs k)
  | %ℕ-idempotent b (abs k)
  | %ℕ-idempotent y (abs k)
  | %ℕ-idempotent x (abs k)
  = refl

mod-distributes-neg : (x k : ℤ) → modℤ (negateℤ x) k ≡ modℤ (negateℤ (modℤ x k)) k
mod-distributes-neg (diff a b) k rewrite (%ℕ-idempotent a (abs k)) | (%ℕ-idempotent b (abs k)) = refl

⟦ℤ⟧ : Set
⟦ℤ⟧ = ℤ × ℤ

Mod : ℤ → Set
Mod k = ℤ

meaning : ℤ → Mod k
meaning {k} x = (modℤ x k)

⟦_⟧ₖ : ℤ → Mod k
⟦_⟧ₖ {k} = meaning {k}

canonicalRepresentative : Mod k → ℤ
canonicalRepresentative x = x

addMod : Mod k → Mod k → Mod k
addMod {k}  x y = modℤ (addℤ x y) k


⟦addMod⟧ :  meaning {k} (addℤ x y) ≡ addMod ⟦ x ⟧ₖ ⟦ y ⟧ₖ
⟦addMod⟧ {k} {x} {y} = begin
         ⟦ addℤ x y ⟧ₖ
         ≡⟨⟩
         modℤ (addℤ x y) k
         ≡⟨  (mod-distributesover-add x y k) ⟩
         modℤ (addℤ (modℤ x k) (modℤ y k)) k
         ≡⟨⟩
         addMod ⟦ x ⟧ₖ  ⟦ y ⟧ₖ
  ∎


mulMod : Mod k → Mod k → Mod k
mulMod {k}  x y = modℤ (mulℤ x y) k


⟦mulMod⟧ : meaning {k} (mulℤ x y) ≡ mulMod ⟦ x ⟧ₖ ⟦ y ⟧ₖ
⟦mulMod⟧ {k} {x} {y} rewrite (mod-distributesover-mul x y k) = refl


modAddInverse : Mod k → Mod k
modAddInverse {k} x = modℤ (negateℤ x) k

⟦modAddInverse⟧ : meaning {k} (negateℤ x) ≡ modAddInverse {k} (meaning {k} x)
⟦modAddInverse⟧ {k} {x} = begin
    ⟦ negateℤ x ⟧ₖ
    ≡⟨⟩
    modℤ (negateℤ x) k
    ≡⟨ mod-distributes-neg x k ⟩
    modℤ (negateℤ (modℤ x k)) k
    ≡⟨⟩
    modAddInverse ⟦ x ⟧ₖ
  ∎

modExp : Mod k → ℕ → Mod k
modExp {k} _ zero = meaning {k} 1ℤ
modExp {k} base (suc n) = mulMod {k} base (modExp {k} base n)
