{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
module rewriting where

open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite

variable
  m n : ℕ

data ℤ : Set where
  diff : ℕ → ℕ → ℤ

postulate
  diffsuc : diff (suc m) (suc n) ≡ diff m n
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
--  %-distribˡ-+ : ∀ m n d .{{_ : NonZero d}} → (m + n) % d ≡ ((m % d) + (n % d)) % d
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
-- diff (((((a %ℕ abs k) * (x %ℕ abs k)) %ℕ abs k) + (((b %ℕ abs k) * (y %ℕ abs k)) %ℕ abs k)) %ℕ abs k) (((((a %ℕ abs k) * (y %ℕ abs k)) %ℕ abs k) + (((b %ℕ abs k) * (x %ℕ abs k)) %ℕ abs k))     %ℕ abs k)
-- diff (((a %ℕ abs k) * (x %ℕ abs k) + (b %ℕ abs k) * (y %ℕ abs k)) %ℕ abs k) (((a %ℕ abs k) * (y %ℕ abs k) + (b %ℕ abs k) * (x %ℕ abs k)) %ℕ     abs k)


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
  --   diff (((a %ℕ  abs k) + (x %ℕ abs k)) %ℕ (abs k))  (((b %ℕ  abs k) + (y %ℕ abs k)) %ℕ (abs k))  -- ((b + y) %ℕ (abs k) )
  --   ≡⟨⟩
  --   modℤ ()
  --   ≡⟨ {!!} ⟩
  --   modℤ (addℤ (modℤ (diff a b) k) (modℤ (diff x y) k)) k
  -- ∎

⟦ℤ⟧ : Set
⟦ℤ⟧ = ℤ

meaning : ℤ →  ℤ → ⟦ℤ⟧
meaning = modℤ

addMod : ⟦ℤ⟧ → ⟦ℤ⟧ → ℤ → ⟦ℤ⟧
addMod  x y = modℤ (addℤ x y)



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


mulMod : ⟦ℤ⟧ → ⟦ℤ⟧ → ℤ → ⟦ℤ⟧
mulMod  x y = modℤ (mulℤ x y)

⟦mulMod⟧ : (x y k : ℤ) → meaning (mulℤ x y) k ≡ mulMod (meaning x k) (meaning y k) k
⟦mulMod⟧ x y k rewrite (mod-distributesover-mul x y k) = refl
