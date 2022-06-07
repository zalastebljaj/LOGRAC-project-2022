module Poskus where

open import Data.Nat
open import Data.Nat.Properties

open import Level        renaming (zero to lzero; suc to lsuc)
open import Data.Sum.Base
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≢_;_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

record Field : Set₁ where
  infixl 6 _+ₚ_
  infixl 7 _·ₚ_
  infixl 8 -ₚ_
  infixl 9 _⁻¹ₚ
  field
    M       : Set
    -- addition
    _+ₚ_ : M → M → M
    -- additive identity
    0ₚ : M
    0ₚ-proof : (m : M) → m +ₚ 0ₚ ≡ m
    -- associativity of addition
    +ₚ-assoc : (m₁ m₂ m₃ : M) → m₁ +ₚ (m₂ +ₚ m₃) ≡ (m₁ +ₚ m₂) +ₚ m₃
    -- commutativity of addition
    +ₚ-comm : (m₁ m₂ : M) → m₁ +ₚ m₂ ≡ m₂ +ₚ m₁
    -- additive inverses
    -ₚ_ : M → M
    -ₚ-proof : (m : M) → m +ₚ (-ₚ m) ≡ 0ₚ


    -- multiplication
    _·ₚ_ : M → M → M
    -- multiplicative identity
    1ₚ : M
    1ₚ-proof : (m : M) → m ·ₚ 1ₚ ≡ m
    -- associativity of multiplication
    ·ₚ-assoc : (m₁ m₂ m₃ : M) → (m₁ ·ₚ m₂) ·ₚ m₃ ≡ m₁ ·ₚ (m₂ ·ₚ m₃)
    -- commutativity of multiplication
    ·ₚ-comm : (m₁ m₂ : M) → m₁ ·ₚ m₂ ≡ m₂ ·ₚ m₁
    -- multiplicative inverses
    _⁻¹ₚ : M → M
    ⁻¹ₚ-proof : (m : M) → m ·ₚ m ⁻¹ₚ ≡ 1ₚ


    -- field laws
    +ₚ·ₚ-distr : (m₁ m₂ m₃ : M) → m₁ ·ₚ (m₂ +ₚ m₃) ≡ (m₁ ·ₚ m₂) +ₚ (m₁ ·ₚ m₃)
    
open Field

-- data FPS (F : Field) : Set where
--     Fps : (ℕ → F) → FPS F


--------------------------------------------------------------------
------------ FPS with natural coefficients -------------------------

fpsid : ℕ → ℕ
fpsid n = n

fps1 : ℕ → ℕ
fps1 n = 1

data FPS (ℕ : Set) : Set where
     Fps : (ℕ → ℕ) → FPS ℕ



to-function : FPS ℕ → (ℕ → ℕ)
to-function (Fps f) = f


identiteta : FPS ℕ
identiteta = Fps fpsid

enice : FPS ℕ
enice = Fps fps1


-------------------- ADDITION ------------------------------------------

-- addition of two functions

_+'_ : (f g : ℕ → ℕ) → ℕ → ℕ
(f +' g) n = f n + g n

-- commutativity for +' for every n
+'-comm' : (f g : ℕ → ℕ)  → ∀ (n : ℕ) → (f +' g) n ≡ (g +' f) n
+'-comm' f g n = 
    begin
        (f +' g) n
    ≡⟨⟩
        f n + g n
    ≡⟨ +-comm (f n) (g n) ⟩
        g n + f n
    ≡⟨⟩
        (g +' f) n
    ∎

-- commutativity for +' for functions, proof with function extentionality
+'-comm : (f g : ℕ → ℕ) → (f +' g) ≡ (g +' f)
+'-comm f g = fun-ext (+'-comm' f g)


-- addition of two power series
_+ᶠ_ : FPS ℕ → FPS ℕ → FPS ℕ
Fps f +ᶠ Fps g = Fps (f +' g)

-- commutativity for power series addition
+ᶠ-comm : (F G : FPS ℕ) → F +ᶠ G ≡ G +ᶠ F
+ᶠ-comm (Fps f) (Fps g) =
    begin
        ((Fps f) +ᶠ (Fps g))
    ≡⟨⟩
        Fps (f +' g)
    ≡⟨ cong Fps (+'-comm f g) ⟩
        Fps (g +' f)
    ≡⟨⟩
        ((Fps g) +ᶠ (Fps f))
    ∎


-- test
vsota : FPS ℕ
vsota = identiteta +ᶠ enice


------------------- MULTIPLICATION ------------------------------------

-- calculates koefficient of n-th monomial when multiplying two FPS
sum : (f g : ℕ → ℕ) → (i : ℕ) → (n : ℕ) → ℕ
sum f g n 0 = f(0) * g(n)
sum f g i (suc n) = (f(suc n) * g(i)) + sum f g (suc i) n   

multiply : (f g : ℕ → ℕ) → ℕ → ℕ
multiply f g n = sum f g 0 n

-- multiplication of two formal power series
_·ᶠ_ : FPS ℕ → FPS ℕ → FPS ℕ
(Fps f) ·ᶠ (Fps g) = Fps (multiply f g)

sum-comm' : (f g : ℕ → ℕ) → ∀ (n : ℕ) → sum f g 0 n ≡ sum g f 0 n
sum-comm' f g 0 =
    begin
        sum f g 0 0
    ≡⟨⟩
        f 0 * g 0
    ≡⟨ *-comm (f 0) (g 0) ⟩
        g 0 * f 0
    ≡⟨⟩
        sum g f 0 0
    ∎
sum-comm' f g (suc n) =
    begin
        sum f g 0 (suc n)
    ≡⟨⟩
        (f(suc n) * g(0)) + sum f g (suc 0) n
    ≡⟨ {!   !} ⟩
        {!   !}




sum-comm : (f g : ℕ → ℕ) → sum f g 0 ≡ sum g f 0
sum-comm f g = fun-ext (sum-comm' f g)


·ᶠ-comm : (F G : FPS ℕ) → F ·ᶠ G ≡ G ·ᶠ F
·ᶠ-comm (Fps f) (Fps g) =
    begin
        (Fps f ·ᶠ Fps g)
    ≡⟨⟩
        Fps (multiply f g)
    ≡⟨⟩
        Fps (sum f g 0)
    ≡⟨ cong Fps (sum-comm f g) ⟩
        Fps (sum g f 0)
    ≡⟨⟩
        Fps (multiply g f)
    ≡⟨⟩
        (Fps g ·ᶠ Fps f)
    ∎



-- test
produkt : FPS ℕ
produkt = identiteta ·ᶠ enice

produkt-rezultat : ℕ → ℕ
produkt-rezultat n = (to-function produkt) n          