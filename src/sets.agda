
open import Data.Integer
module sets ( k : ℤ ) where
open import Data.Product
open import Relation.Unary

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Integer.Properties
open Agda.Primitive

variable
  a b c d : ℤ
  A B : Set
  P Q : Pred A lzero

infix 4 _≈_
data _≈_ : ℤ → ℤ → Set where
  make≈ : (c : ℤ) → k * c ≡ a - b  → a ≈ b

refl≈ : a ≈ a
refl≈ {a} = make≈ +0 (trans (*-zeroʳ k) (sym (+-inverseʳ a)))

sym≈ : a ≈ b → b ≈ a
sym≈ (make≈ x kx=a-b) = make≈ (- x) {!!}

trans≈ : a ≈ b → b ≈ c → a ≈ c
trans≈ (make≈ x kx=a-b) (make≈ y ky=b-c) = make≈ (x + y) {!!}

add≈ : a ≈ b → c ≈ d → a + c ≈ b + d
add≈ {a} {b} {c} {d} (make≈ x kx=a-b) (make≈ y ky=c-d)  = make≈ (x + y) (begin
  k * (x + y)
  ≡⟨ *-distribˡ-+ k x y ⟩
  k * x + k * y
  ≡⟨ cong (λ p → p + k * y) kx=a-b ⟩
  a - b + k  * y
  ≡⟨ cong (λ p →  a - b + p) ky=c-d ⟩
  a + - b + (c + - d)
  ≡⟨ {!!} ⟩
  a + c - (b + d)
  ∎)

modk : Set₁
modk = Pred ℤ _

⟦_⟧ : ℤ → modk
⟦ x ⟧ =  _≈ x
addk : modk → modk → modk
addk a b x =  ∃ λ y → ∃ λ z → a y × b z × (x ≈ (y + z))


postulate
  predExt : P ≐′ Q → P ≡ Q

addkaux  : (a b y : ℤ) → addk ⟦ a ⟧ ⟦ b ⟧ y → ⟦ a + b ⟧ y
addkaux a b y (w , x , a≈w , x≈b , y≈w+x) = trans≈ y≈w+x w+x≈a+b
  where
    w+x≈a+b : w + x ≈ a + b
    w+x≈a+b = add≈ (a≈w) (x≈b)

⟦addk⟧ : ∀ a b → ⟦ a + b ⟧ ≡ addk ⟦ a ⟧ ⟦ b ⟧
⟦addk⟧ a b = predExt ((λ x x≈a+b → a , b , refl≈ ,  refl≈ , x≈a+b ) , addkaux a b)
