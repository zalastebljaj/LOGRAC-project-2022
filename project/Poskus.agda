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

nvn : ℕ → ℕ
nvn n = n



data FPS (ℕ : Set) : Set where
     Fps : (ℕ → ℕ) → FPS ℕ



to-function : FPS ℕ → (ℕ → ℕ)
to-function (Fps f) = f


fps1 : FPS ℕ
fps1 = Fps nvn



-------------------- ADDITION ------------------------------------------

-- addition of two functions

_+'_ : (f g : ℕ → ℕ) → ℕ → ℕ
(f +' g) n = f n + g n

-- addition of two power series
_+ᶠ_ : FPS ℕ → FPS ℕ → FPS ℕ
Fps f +ᶠ Fps g = Fps (f +' g)

-- zero element
enice : ℕ → ℕ
enice n = 1

0ᶠ : FPS ℕ
0ᶠ = Fps enice


-- additive inverse (cannot make it for ℕ but it is -f)
-ᶠ_ : FPS ℕ → FPS ℕ
-ᶠ Fps f = {!   !}

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
vsota = fps1 +ᶠ 0ᶠ


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


-- multiplicative identity
multident : ℕ → ℕ
multident 0 = 1
multident (suc n) = 0

1ᶠ : FPS ℕ
1ᶠ = Fps multident

-- commutativity of multiplication not needed for algebra
-- also problems because sum is not defined in the best way
-- sum-comm' : (f g : ℕ → ℕ) → ∀ (n : ℕ) → sum f g 0 n ≡ sum g f 0 n
-- sum-comm' f g 0 =
--     begin
--         sum f g 0 0
--     ≡⟨⟩
--         f 0 * g 0
--     ≡⟨ *-comm (f 0) (g 0) ⟩
--         g 0 * f 0
--     ≡⟨⟩
--         sum g f 0 0
--     ∎
-- sum-comm' f g (suc n) =
--     begin
--         sum f g 0 (suc n)
--     ≡⟨⟩
--         (f(suc n) * g(0)) + sum f g (suc 0) n
--     ≡⟨ {!   !} ⟩
--         {!   !}


-- sum-comm : (f g : ℕ → ℕ) → sum f g 0 ≡ sum g f 0
-- sum-comm f g = fun-ext (sum-comm' f g)


-- ·ᶠ-comm : (F G : FPS ℕ) → F ·ᶠ G ≡ G ·ᶠ F
-- ·ᶠ-comm (Fps f) (Fps g) =
--     begin
--         (Fps f ·ᶠ Fps g)
--     ≡⟨⟩
--         Fps (multiply f g)
--     ≡⟨⟩
--         Fps (sum f g 0)
--     ≡⟨ cong Fps (sum-comm f g) ⟩
--         Fps (sum g f 0)
--     ≡⟨⟩
--         Fps (multiply g f)
--     ≡⟨⟩
--         (Fps g ·ᶠ Fps f)
--     ∎



-- test
produkt : FPS ℕ
produkt = fps1 ·ᶠ 0ᶠ

produkt-rezultat : ℕ → ℕ
produkt-rezultat n = (to-function produkt) n

identitytest : FPS ℕ
identitytest = fps1 ·ᶠ 1ᶠ

idtest : ℕ → ℕ
idtest n = (to-function identitytest) n





-------------------FORMAL DIFFERENTIATION-------------------------

diff : (f : ℕ → ℕ) → ℕ → ℕ
diff f n = f (suc n) * (suc n)

D_ : FPS ℕ → FPS ℕ
D Fps f = Fps (diff f)

