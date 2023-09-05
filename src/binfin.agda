open import Data.Nat using (ℕ ; _^_ ; _+_ ; _*_ ; zero ; suc   ; ∣_-_∣)
open import Data.Nat.Properties -- using (*-identityʳ ; *-identityˡ)
open import Data.Nat.Divisibility using (_∣_)
module binfin where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; _∧_ ; not ; _∨_)
open import Data.Product -- using (_×_ ; _,_ ; proj₁ ; proj₂ ; uncurry ; curry ; map)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Function


vec : ℕ → Set → Set
vec 0 A = ⊤
vec (suc n) A = A × vec n A
bs : ℕ → Set
bs = flip vec Bool
variable
  m : ℕ
  xs : bs m
  A B C D E F : Set



⟦_⟧b : Bool → ℕ
⟦ true ⟧b =  1
⟦ false ⟧b = 0
shift : ℕ × ℕ → ℕ
shift = uncurry _+_ ∘ map₂ (2 *_)
⟦_⟧ : {n  : ℕ} → vec n Bool → ℕ
⟦_⟧ {n = 0} = const 0
⟦_⟧ {n = suc n} = shift ∘  map ⟦_⟧b ⟦_⟧


inAssocr :  ((A × B) × C → (D × E) × F) →   ((A × (B × C)) → (D × (E × F)))
inAssocr f = assocʳ′ ∘ f ∘ assocˡ′

halfAdd : Bool × Bool → Bool × Bool
halfAdd  = < uncurry _xor_ , uncurry _∧_ >

fullAdd : Bool × Bool × Bool → Bool × Bool
fullAdd = map₂ (uncurry _∨_ ) ∘  inAssocr (map₁ halfAdd) ∘  map₂ halfAdd

mapAcc : (A × C → D × A) → A × vec m C → vec m D
mapAcc {m = 0}  = const (const tt)
mapAcc {m = suc m} f = map₂ (mapAcc f) ∘ (inAssocr (map₁ f))

condsuc : Bool × bs m → bs m
condsuc = mapAcc halfAdd

sucb’ : bs m → bs m
sucb’ = curry condsuc true

equiv : ℕ → ℕ → ℕ → Set
equiv k a b = k ∣ ∣ a - b ∣

∣n-n∣ : (n : ℕ) → ∣ n - n ∣ ≡ 0
∣n-n∣ 0 = refl
∣n-n∣ (suc n) = ∣n-n∣ n
mod1equiv : (a b : ℕ) → equiv 1 a b
mod1equiv a b rewrite (sym (*-identityʳ ∣ a - b ∣)) = Data.Nat.Divisibility.divides ∣ a - b ∣ refl


reflequiv : {a : ℕ} (b : ℕ) → equiv a b b
reflequiv = Data.Nat.Divisibility.divides 0 ∘  ∣n-n∣

reflequivi : Reflexive (equiv m)
reflequivi {x = x} = reflequiv x

0b : ∀ m → bs m
0b 0 = tt
0b (suc m) = false , 0b m

0b=0 : ∀ m →  ⟦ 0b m ⟧ ≡ 0
0b=0 0 = refl
0b=0 (suc m) rewrite (0b=0 m) = refl

⟦0b⟧ : ∀ m → equiv (2 ^ m) ⟦ 0b m ⟧ 0
⟦0b⟧ m rewrite (0b=0 m) = reflequiv 0

condsucfalse : (m : ℕ) (xs : bs m ) → condsuc (false , xs) ≡ xs
condsucfalse zero  = const refl
condsucfalse (suc m) (_ , xs) rewrite (condsucfalse m xs) = refl


⟦sucb’⟧ :  (m : ℕ) → (xs : bs m) → equiv (2 ^ m) (suc ⟦ xs ⟧)  (⟦ sucb’ xs ⟧)
⟦sucb’⟧ zero  = const (mod1equiv 1 0)
⟦sucb’⟧ (suc m) (false , xs) rewrite (condsucfalse m xs) = reflequiv (2 * ⟦ xs ⟧)
⟦sucb’⟧ (suc m) (true , xs) = {!!}

addb : vec m (Bool × Bool) → bs m
addb = mapAcc fullAdd ∘  (false ,_)
