open import Data.Integer
module sets ( k : ℤ ) where
open import Data.Product
open import Data.Sum
open import Relation.Unary

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions renaming (Decidable to Decidable2)
open import Relation.Nullary.Decidable
open ≡-Reasoning
open import Data.Integer.Properties

open Agda.Primitive

variable
  a b c d e : ℤ
  A B : Set
  P Q : Pred A lzero
  f : ℤ → ℤ



infix 4 _≈’_
data _≈’_ : ℤ → ℤ → Set where
  step≈ : (c : ℤ) →  a ≈’ a + c * k

open import Algebra.Definitions using (Commutative)

step≈’ : a ≈’ b → a ≈’ b + c * k
step≈’ {a} {b} {c} (step≈ x) rewrite (+-assoc a (x * k) (c * k)) | (sym (*-distribʳ-+ k x c)) = step≈ {a} (x + c)

refl≈’ : Reflexive _≈’_
refl≈’ {a} = subst (λ x → a ≈’ x) (+-identityʳ a) (subst (λ x → a ≈’ a + x ) (*-zeroˡ k) (step≈ +0))


cong≈ : (ℤ → ℤ) → Set
cong≈ f =  {a b : ℤ} →  a ≈’ b → f a ≈’ f b

cong2≈ : (ℤ → ℤ → ℤ) → Set
cong2≈ f = {a b c d : ℤ} →  a ≈’ b → c ≈’ d →  f a c ≈’ f b d

congf : (ℤ → ℤ → ℤ) → Set
congf f = (c : ℤ) → cong≈ (λ x → f x c)

congs : (ℤ → ℤ → ℤ) → Set
congs f = (c : ℤ) → cong≈ (f c)

cong+ :  congf _+_
cong+ x {a} (step≈ m) rewrite (+-assoc a (m * k) x) | (+-comm (m * k) x) | (sym (+-assoc a (x) (m * k))) = step≈ m


infixl 6 _·_
variable
  _·_ : ℤ → ℤ → ℤ

congf→congs : Commutative _≡_ _·_ → congf _·_ → congs _·_
congf→congs com congf c {a} {b} rewrite (com c a) |(com c b) = congf c


+cong : congs _+_
+cong = congf→congs +-comm cong+



trans≈’ : Transitive _≈’_
trans≈’ {a} (step≈ x) (step≈ y) rewrite (+-assoc a (x * k) (y * k)) | (sym (*-distribʳ-+ k x y)) = step≈ (x + y)

congfcongs→cong2 : congf _·_ → congs _·_ → cong2≈ _·_
congfcongs→cong2 congf congs {a = a} {d = d} a=b c=d =  trans≈’ (congs a c=d) (congf d a=b)

congf→cong2 :  Commutative _≡_ _·_ → congf _·_ → cong2≈ _·_
congf→cong2 comm congf = congfcongs→cong2 congf (congf→congs comm congf)

cong2+ : cong2≈ _+_
cong2+  = congf→cong2 +-comm cong+


sym≈’ : Symmetric _≈’_
sym≈’ {a} (step≈ x) = {!!}

cong* : congf _*_
cong* c {a} (step≈ m)  rewrite (*-distribʳ-+ c a (m * k)) | (*-assoc m k c) | (*-comm k c) | (sym (*-assoc m c k)) = step≈ (m * c)

*cong : congs _*_
*cong =  congf→congs *-comm cong*

cong2* : cong2≈ _*_
cong2* = congf→cong2 *-comm cong*

cong- : cong≈ (-_)
cong- {a} (step≈ x)  rewrite (neg-distrib-+ a ( x * k )) | (neg-distribˡ-* x k) = step≈ (- x)



modk : Set₁
modk = Pred ℤ _

⟦_⟧ : ℤ → modk
⟦ x ⟧ =  _≈’ x

open import Data.Integer.Divisibility
open import Data.Nat.Divisibility using (_∣?_)
open import Data.Integer.Base using (∣_∣)
open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_ ; _^_ to _^ℕ_)
import Data.Sign renaming (_*_ to _*s_)

cong^ : (n : ℕ) → cong≈ ( _^ n)
cong^ zero a=b = refl≈’
cong^ (ℕ.suc n) a=b = cong2* a=b (cong^ n a=b)

decid| : Decidable2 _∣_
decid| x y with ((∣ x ∣) ∣? (∣ y ∣))
... | yes a = yes a
... | no b = no b

postulate
  b=a+c : b ≡ (a + (b - a))
  a-b=a-a+b-a : a - b ≡ a + - (a + (b + - a))


absdiff : (q : ℕ) →  ∣ (a - b) ∣ ≡ q Data.Nat.* ∣ k ∣  → a ≈’ b
absdiff {a} {b} q eq rewrite ( (b=a+c {b = b} {a = a}))  = {!!}

-- ≈|¬ : x ≈’ y →
--
≈→| : a ≈’ b → ∣ k ∣ Data.Nat.Divisibility.∣ ∣ (a - b) ∣
≈→| {a} (step≈  x) rewrite (neg-distrib-+ a (x * k)) | (sym (+-assoc a (- a) (- ( x * k )))) | (+-inverseʳ a) | (+-identityˡ (- (x * k))) | (abs-◃  (sign x Data.Sign.*s sign k) (∣ x ∣ *ℕ ∣ k ∣)) = divides  ∣ x ∣  {!!}

dec≈ : Decidable2 _≈’_
dec≈  x y with (decid| k (x - y))
... | yes (divides quotient equality) = yes (absdiff quotient equality)
... | no b = no λ d → b (≈→| d)

decid⟦⟧ : Decidable (⟦ a ⟧ )
decid⟦⟧ {a}  x = dec≈ x a

onRep : (ℤ → ℤ) → modk → modk
onRep f a x = ∃ λ y → a y × x ≈’ f y

negatek : modk → modk
negatek = onRep (-_)

expk : ℕ → modk → modk
expk n = onRep (_^ n)


⟦onRep⟧aux : cong≈ f → {a : ℤ} → onRep f ⟦ a ⟧ ⊆′ ⟦ f a ⟧
⟦onRep⟧aux cong _ (_ , a=z , y=fz) = trans≈’ y=fz (cong a=z)

⟦onRep⟧ : cong≈ f → (a  : ℤ) → ⟦ f a ⟧ ≐′ onRep f ⟦ a ⟧
⟦onRep⟧ cong a = (λ x x≈fa → a , refl≈’ , x≈fa) , ⟦onRep⟧aux cong


⟦negatek⟧ : ∀ a → ⟦ - a ⟧ ≐′ negatek ⟦ a ⟧
⟦negatek⟧ = ⟦onRep⟧ cong-

⟦expk⟧ : (n : ℕ) →  ∀ a →  ⟦ a ^ n ⟧ ≐′ expk n ⟦ a ⟧
⟦expk⟧ n = ⟦onRep⟧ (cong^ n)

onRep2 : (ℤ → ℤ → ℤ) → modk → modk → modk
onRep2 _·_ a b x =  ∃ λ y → ∃ λ z → a y × b z × x ≈’ y · z


⟦onRep2⟧aux : cong2≈ _·_  → onRep2 _·_ ⟦ a ⟧ ⟦ b ⟧ ⊆′ ⟦ a · b ⟧
⟦onRep2⟧aux cong _ (_ , _ , a≈w , x≈b , y≈w·x ) = trans≈’ y≈w·x (cong a≈w x≈b)

⟦onRep2⟧ : cong2≈ _·_ → (a b : ℤ) → ⟦ a · b ⟧ ≐′ onRep2 _·_ ⟦ a ⟧ ⟦ b ⟧
⟦onRep2⟧ cong a b = (λ _ x≈a·b → a , (b , (refl≈’ , refl≈’ , x≈a·b))) , ⟦onRep2⟧aux cong

addk : modk → modk → modk
addk = onRep2 _+_

⟦addk⟧ : ∀ a b → ⟦ a + b ⟧ ≐′ addk ⟦ a ⟧ ⟦ b ⟧
⟦addk⟧ =  ⟦onRep2⟧ cong2+

mulk : modk → modk → modk
mulk = onRep2 _*_

⟦mulk⟧ : ∀ a b → ⟦ a * b ⟧ ≐′ mulk ⟦ a ⟧ ⟦ b ⟧
⟦mulk⟧ =  ⟦onRep2⟧ cong2*

data Even  : ℕ →  Set where
  2n : (n : ℕ) → Even (2 *ℕ n)

data Odd  : ℕ →  Set where
  2n+1 : (n : ℕ) → Odd (ℕ.suc (2 *ℕ n))

even-or-odd : (n : ℕ) → (Even n) ⊎ (Odd n)
even-or-odd zero = inj₁ (2n zero)
even-or-odd (ℕ.suc zero) = inj₂ (2n+1 0)
even-or-odd (ℕ.suc (ℕ.suc n)) with (even-or-odd n)
... | (inj₁ (2n x)) = inj₁ (2n ({!!}))
... | (inj₂ (2n+1 y)) = inj₂ (2n+1 {!!})

fastExp : ℕ → ℤ → ℤ
fastExp 0 x = 1ℤ
fastExp (ℕ.suc n) x with (even-or-odd (n))
... | (inj₁ (2n n/2)) = fastExp n/2 x
... | (inj₂ (2n+1 n/2)) = {!!}
