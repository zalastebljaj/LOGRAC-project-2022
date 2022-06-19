open import Algebra
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Function.Base using (_$_)
open import Relation.Binary using (IsEquivalence; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions

module PowerSeries {a ℓ} (F : CommutativeRing a ℓ) where

open CommutativeRing F using (setoid) renaming
    (Carrier to A; _≈_ to _≈ₐ_; _*_ to _*ₐ_; _+_ to _+ₐ_; -_ to -ₐ_; 0# to 0ₐ; 1# to 1ₐ;
    refl to ≈ₐ-refl; sym to ≈ₐ-sym; trans to ≈ₐ-trans;
    +-cong to +ₐ-cong; +-assoc to +ₐ-assoc; +-comm to +ₐ-comm;
    +-identityˡ to +ₐ-identityˡ; +-identityʳ to +ₐ-identityʳ;
    -‿cong to -ₐ‿cong; -‿inverseˡ to -ₐ‿inverseˡ; -‿inverseʳ to -ₐ‿inverseʳ;
    *-cong to *ₐ-cong; *-assoc to *ₐ-assoc; *-comm to *ₐ-comm;
    *-identityˡ to *ₐ-identityˡ; *-identityʳ to *ₐ-identityʳ;
    zeroˡ to zeroˡₐ; zeroʳ to zeroʳₐ;
    distribˡ to distribˡₐ; distribʳ to distribʳₐ)

open import Relation.Binary.Reasoning.Setoid setoid

-- type of formal power series over F

FPS : Set a
FPS = ℕ → A

-- additive identity

0# : FPS
0# n = 0ₐ

-- multiplicative identity

1# : FPS
1# zero = 1ₐ
1# (suc n) = 0ₐ

-- equivalence relation

infix 4 _≈_
_≈_ : (xs : FPS) (ys : FPS) → Set ℓ
xs ≈ ys = (n : ℕ) → (xs n) ≈ₐ (ys n)

-- addition

infixl 6 _+_
_+_ : FPS → FPS → FPS
(x + y) n = (x n) +ₐ (y n)

-- negation

infix 8 -_
-_ : FPS → FPS
(- x) n = -ₐ (x n)

-- scalar multiplication

infixl 7 _*ₛ_
_*ₛ_ : A → FPS → FPS
(a *ₛ x) n = a *ₐ (x n)

-- multiplication

*ᵢ : ℕ → ℕ → FPS → FPS → A
*ᵢ zero k₂ x y = (x zero) *ₐ (y k₂)
*ᵢ (suc k₁) k₂ x y = (*ᵢ k₁ (suc k₂) x y) +ₐ (x (suc k₁)) *ₐ (y k₂)

infixl 7 _*_
_*_ : FPS → FPS → FPS
(x * y) n = *ᵢ n zero x y

-- formal differentiation

toA : ℕ → A
toA zero = 0ₐ
toA (suc n) = 1ₐ +ₐ toA n

deriv : FPS → FPS
deriv x n = toA (suc n) *ₐ (x (suc n))

-- proof that formal power series form an F-algebra

-- ≈ is an equivalence relation
≈-equivalence : IsEquivalence _≈_
IsEquivalence.refl ≈-equivalence n = ≈ₐ-refl
IsEquivalence.sym ≈-equivalence x≈y n = ≈ₐ-sym (x≈y n)
IsEquivalence.trans ≈-equivalence x≈y y≈z n = ≈ₐ-trans (x≈y n) (y≈z n)

-- addition is well defined
+-cong : Congruent₂ _≈_ _+_
+-cong x≈y u≈v n = +ₐ-cong (x≈y n) (u≈v n)

-- addition is associative
+-assoc : Associative _≈_ _+_
+-assoc x y z n = +ₐ-assoc (x n) (y n) (z n)

-- addition is commutative
+-comm : Commutative _≈_ _+_
+-comm x y n = +ₐ-comm (x n) (y n)

-- 0# is an additive identity
+-ident : Identity _≈_ 0# _+_
proj₁ +-ident x n = +ₐ-identityˡ (x n)
proj₂ +-ident x n = +ₐ-identityʳ (x n)

-- additive inverse is well defined
+-icong : Congruent₁ _≈_ -_
+-icong x n = -ₐ‿cong (x n)

-- all elements have an additive inverse
+-inverse : Inverse _≈_ 0# -_ _+_
proj₁ +-inverse x n = -ₐ‿inverseˡ (x n)
proj₂ +-inverse x n = -ₐ‿inverseʳ (x n)

-- scalar multiplication is well defined
*ₛ-cong : _*ₛ_ Preserves₂ _≈ₐ_ ⟶ _≈_ ⟶ _≈_
*ₛ-cong a≈b x≈y n = *ₐ-cong a≈b (x≈y n)

-- scalar multiplication and field multiplication are compatible
*ₛ-compat : ∀ a b x → ((a *ₐ b) *ₛ x) ≈ (a *ₛ (b *ₛ x))
*ₛ-compat a b x n = *ₐ-assoc a b (x n)

-- field multiplicative identity is identity for scalar multiplication
*ₛ-ident : ∀ x → (1ₐ *ₛ x) ≈ x
*ₛ-ident x n = *ₐ-identityˡ (x n)

-- scalar multiplication distributes over addition
*ₛ-vdist : ∀ a x y → (a *ₛ (x + y)) ≈ (a *ₛ x + a *ₛ y)
*ₛ-vdist a x y n = distribˡₐ a (x n) (y n)

-- scalar multiplication distributes over field addition
*ₛ-fdist : ∀ x a b → ((a +ₐ b) *ₛ x) ≈ (a *ₛ x + b *ₛ x)
*ₛ-fdist x a b n = distribʳₐ (x n) a b

-- shuffle helpers
+ₐ-shuf : ∀ a b c d → (a +ₐ b +ₐ (c +ₐ d)) ≈ₐ (a +ₐ c +ₐ (b +ₐ d))
+ₐ-shuf a b c d =
    begin
        a +ₐ b +ₐ (c +ₐ d)
    ≈⟨ +ₐ-assoc a b (c +ₐ d) ⟩
        a +ₐ (b +ₐ (c +ₐ d))
    ≈⟨ +ₐ-cong ≈ₐ-refl (≈ₐ-sym $ +ₐ-assoc b c d) ⟩
        a +ₐ (b +ₐ c +ₐ d)
    ≈⟨ +ₐ-cong ≈ₐ-refl (+ₐ-cong (+ₐ-comm b c) ≈ₐ-refl) ⟩
        a +ₐ (c +ₐ b +ₐ d)
    ≈⟨ +ₐ-cong ≈ₐ-refl (+ₐ-assoc c b d) ⟩
        a +ₐ (c +ₐ (b +ₐ d))
    ≈⟨ ≈ₐ-sym $ +ₐ-assoc a c (b +ₐ d) ⟩
        a +ₐ c +ₐ (b +ₐ d)
    ∎

*ₐ-shuf : ∀ a b c d → (a *ₐ b *ₐ (c *ₐ d)) ≈ₐ (a *ₐ c *ₐ (b *ₐ d))
*ₐ-shuf a b c d =
    begin
        a *ₐ b *ₐ (c *ₐ d)
    ≈⟨ *ₐ-assoc a b (c *ₐ d) ⟩
        a *ₐ (b *ₐ (c *ₐ d))
    ≈⟨ *ₐ-cong ≈ₐ-refl (≈ₐ-sym $ *ₐ-assoc b c d) ⟩
        a *ₐ (b *ₐ c *ₐ d)
    ≈⟨ *ₐ-cong ≈ₐ-refl (*ₐ-cong (*ₐ-comm b c) ≈ₐ-refl) ⟩
        a *ₐ (c *ₐ b *ₐ d)
    ≈⟨ *ₐ-cong ≈ₐ-refl (*ₐ-assoc c b d) ⟩
        a *ₐ (c *ₐ (b *ₐ d))
    ≈⟨ ≈ₐ-sym $ *ₐ-assoc a c (b *ₐ d) ⟩
        a *ₐ c *ₐ (b *ₐ d)
    ∎

-- multiplication is left distributive
*ᵢ-distˡ : (k₁ : ℕ) → (k₂ : ℕ) → ∀ x y z → (*ᵢ k₁ k₂ x (y + z)) ≈ₐ ((*ᵢ k₁ k₂ x y) +ₐ (*ᵢ k₁ k₂ x z))
*ᵢ-distˡ zero k₂ x y z = distribˡₐ (x zero) (y k₂) (z k₂)
*ᵢ-distˡ (suc k₁) k₂ x y z =
    begin
        (*ᵢ k₁ (suc k₂) x (y + z)) +ₐ (x (suc k₁)) *ₐ ((y + z) k₂)
    ≈⟨ +ₐ-cong (*ᵢ-distˡ k₁ (suc k₂) x y z) (distribˡₐ (x (suc k₁)) (y k₂) (z k₂)) ⟩
        (*ᵢ k₁ (suc k₂) x y) +ₐ (*ᵢ k₁ (suc k₂) x z) +ₐ ((x (suc k₁)) *ₐ (y k₂) +ₐ (x (suc k₁)) *ₐ (z k₂))
    ≈⟨ +ₐ-shuf (*ᵢ k₁ (suc k₂) x y) (*ᵢ k₁ (suc k₂) x z) ((x (suc k₁)) *ₐ (y k₂)) ((x (suc k₁)) *ₐ (z k₂)) ⟩
        (*ᵢ k₁ (suc k₂) x y) +ₐ (x (suc k₁)) *ₐ (y k₂) +ₐ ((*ᵢ k₁ (suc k₂) x z) +ₐ (x (suc k₁)) *ₐ (z k₂))
    ∎

*-distˡ : _DistributesOverˡ_ _≈_ _*_ _+_
*-distˡ x y z n = *ᵢ-distˡ n zero x y z

-- multiplication is right distributive
*ᵢ-distʳ : (k₁ : ℕ) → (k₂ : ℕ) → ∀ x y z → (*ᵢ k₁ k₂ (y + z) x) ≈ₐ ((*ᵢ k₁ k₂ y x) +ₐ (*ᵢ k₁ k₂ z x))
*ᵢ-distʳ zero k₂ x y z = distribʳₐ (x k₂) (y zero) (z zero)
*ᵢ-distʳ (suc k₁) k₂ x y z =
    begin
        (*ᵢ k₁ (suc k₂) (y + z) x) +ₐ ((y + z) (suc k₁)) *ₐ (x k₂)
    ≈⟨ +ₐ-cong (*ᵢ-distʳ k₁ (suc k₂) x y z) (distribʳₐ (x k₂) (y (suc k₁)) (z (suc k₁))) ⟩
        (*ᵢ k₁ (suc k₂) y x) +ₐ (*ᵢ k₁ (suc k₂) z x) +ₐ ((y (suc k₁)) *ₐ (x k₂) +ₐ (z (suc k₁)) *ₐ (x k₂))
    ≈⟨ +ₐ-shuf (*ᵢ k₁ (suc k₂) y x) (*ᵢ k₁ (suc k₂) z x) ((y (suc k₁)) *ₐ (x k₂)) ((z (suc k₁)) *ₐ (x k₂)) ⟩
        (*ᵢ k₁ (suc k₂) y x) +ₐ (y (suc k₁)) *ₐ (x k₂) +ₐ ((*ᵢ k₁ (suc k₂) z x) +ₐ (z (suc k₁)) *ₐ (x k₂))
    ∎

*-distʳ : _DistributesOverʳ_ _≈_ _*_ _+_
*-distʳ x y z n = *ᵢ-distʳ n zero x y z

-- multiplication and scalar multiplication are compatible
*ᵢ-compat : (k₁ : ℕ) → (k₂ : ℕ) → ∀ a b x y → (*ᵢ k₁ k₂ (a *ₛ x) (b *ₛ y)) ≈ₐ ((a *ₐ b) *ₐ (*ᵢ k₁ k₂ x y))
*ᵢ-compat zero k₂ a b x y = *ₐ-shuf a (x zero) b (y k₂)
*ᵢ-compat (suc k₁) k₂ a b x y =
    begin
        (*ᵢ k₁ (suc k₂) (a *ₛ x) (b *ₛ y)) +ₐ ((a *ₛ x) (suc k₁)) *ₐ ((b *ₛ y) k₂)
    ≈⟨ +ₐ-cong (*ᵢ-compat k₁ (suc k₂) a b x y) (*ₐ-shuf a (x (suc k₁)) b (y k₂)) ⟩
        a *ₐ b *ₐ (*ᵢ k₁ (suc k₂) x y) +ₐ a *ₐ b *ₐ ((x (suc k₁)) *ₐ (y k₂))
    ≈⟨ ≈ₐ-sym $ distribˡₐ (a *ₐ b) (*ᵢ k₁ (suc k₂) x y) ((x (suc k₁)) *ₐ (y k₂)) ⟩
        a *ₐ b *ₐ ((*ᵢ k₁ (suc k₂) x y) +ₐ (x (suc k₁)) *ₐ (y k₂))
    ∎

*-compat : ∀ a b x y → ((a *ₛ x) * (b *ₛ y)) ≈ ((a *ₐ b) *ₛ (x * y))
*-compat a b x y n = *ᵢ-compat n zero a b x y

-- QED

-- some properties of formal differentiation

-- formal differentiation is additive
deriv-+ : ∀ x y → (deriv (x + y)) ≈ (deriv x + deriv y)
deriv-+ x y n = distribˡₐ (toA (suc n)) (x (suc n)) (y (suc n))

-- formal differentiation is scalar multiplicative
deriv-*ₛ : ∀ a x → (deriv (a *ₛ x)) ≈ (a *ₛ deriv x)
deriv-*ₛ a x n =
    begin
        toA (suc n) *ₐ (a *ₐ (x (suc n)))
    ≈⟨ ≈ₐ-sym $ *ₐ-assoc (toA (suc n)) a (x (suc n)) ⟩
        toA (suc n) *ₐ a *ₐ (x (suc n))
    ≈⟨ *ₐ-cong (*ₐ-comm (toA (suc n)) a) ≈ₐ-refl ⟩
        a *ₐ toA (suc n) *ₐ (x (suc n))
    ≈⟨ *ₐ-assoc a (toA (suc n)) (x (suc n)) ⟩
        a *ₐ (toA (suc n) *ₐ (x (suc n)))
    ∎

-- formal differentiation is linear
deriv-lin : ∀ a b x y → (deriv (a *ₛ x + b *ₛ y)) ≈ (a *ₛ deriv x + b *ₛ deriv y)
deriv-lin a b x y n =
    begin
        deriv (a *ₛ x + b *ₛ y) n
    ≈⟨ deriv-+ (a *ₛ x) (b *ₛ y) n ⟩
        (deriv (a *ₛ x) + deriv (b *ₛ y)) n
    ≈⟨ +ₐ-cong (deriv-*ₛ a x n) (deriv-*ₛ b y n) ⟩
        (a *ₛ deriv x + b *ₛ deriv y) n
    ∎

-- formal differentiation satisfies leibniz rule

-- helper function that shifts suc to left
shift-suc : (n : ℕ) → (k : ℕ) → toA n +ₐ toA (suc k) ≈ₐ toA (suc n) +ₐ toA k
shift-suc zero k =
    begin
        0ₐ +ₐ (1ₐ +ₐ toA k)
    ≈⟨ +ₐ-identityˡ (1ₐ +ₐ toA k) ⟩
        (1ₐ +ₐ toA k)
    ≈⟨ +ₐ-cong (≈ₐ-sym $ +ₐ-identityʳ 1ₐ) ≈ₐ-refl ⟩
        (1ₐ +ₐ 0ₐ) +ₐ toA k
    ∎
shift-suc (suc n) k =
    begin
        toA (suc n) +ₐ (1ₐ +ₐ toA k)
    ≈⟨ ≈ₐ-sym $ +ₐ-assoc (toA (suc n)) 1ₐ (toA k) ⟩
        (toA (suc n) +ₐ 1ₐ) +ₐ toA k
    ≈⟨ +ₐ-cong (+ₐ-comm (toA (suc n)) 1ₐ) ≈ₐ-refl ⟩
        (1ₐ +ₐ toA (suc n)) +ₐ toA k
    ∎

*ᵢ-leibniz : (n : ℕ) → (k : ℕ) → ∀ x y → (*ᵢ n k (deriv x) y) +ₐ (*ᵢ n k x (deriv y)) +ₐ toA k *ₐ x (suc n) *ₐ y (k) ≈ₐ (toA (suc n) +ₐ toA k) *ₐ (*ᵢ (suc n) k x y)
*ᵢ-leibniz zero k x y =
    begin
        toA (suc zero) *ₐ (x (suc zero)) *ₐ (y k) +ₐ (x zero) *ₐ (toA (suc k) *ₐ y (suc k)) +ₐ toA k *ₐ x 1 *ₐ y k
    ≈⟨ +ₐ-cong (+ₐ-comm (toA (suc zero) *ₐ (x (suc zero)) *ₐ (y k)) ((x zero) *ₐ (toA (suc k) *ₐ y (suc k)))) (*ₐ-assoc (toA k) (x 1) (y k)) ⟩
        (x zero) *ₐ (toA (suc k) *ₐ y (suc k)) +ₐ toA (suc zero) *ₐ x (suc zero) *ₐ (y k) +ₐ toA k *ₐ (x 1 *ₐ y k)
    ≈⟨ +ₐ-assoc ((x zero) *ₐ (toA (suc k) *ₐ y (suc k))) (toA (suc zero) *ₐ x (suc zero) *ₐ (y k)) (toA k *ₐ (x 1 *ₐ y k)) ⟩
        (x zero) *ₐ (toA (suc k) *ₐ y (suc k)) +ₐ (toA (suc zero) *ₐ x (suc zero) *ₐ (y k) +ₐ toA k *ₐ (x 1 *ₐ y k))
    ≈⟨ +ₐ-cong ≈ₐ-refl (+ₐ-cong (*ₐ-assoc (toA (suc zero)) (x (suc zero)) (y k)) ≈ₐ-refl) ⟩
        (x zero) *ₐ (toA (suc k) *ₐ y (suc k)) +ₐ (toA (suc zero) *ₐ (x (suc zero) *ₐ (y k)) +ₐ toA k *ₐ (x 1 *ₐ y k))
    ≈⟨ +ₐ-cong (≈ₐ-sym $ *ₐ-assoc (x zero) (toA (suc k)) (y (suc k))) (≈ₐ-sym $ distribʳₐ ((x (suc zero)) *ₐ (y k)) (toA (suc zero)) (toA k)) ⟩
        (x zero) *ₐ toA (suc k) *ₐ y (suc k) +ₐ (toA (suc zero) +ₐ toA k) *ₐ ((x (suc zero)) *ₐ (y k))
    ≈⟨ +ₐ-cong (*ₐ-cong (*ₐ-comm (x zero) (toA (suc k))) ≈ₐ-refl) ≈ₐ-refl ⟩
        toA (suc k) *ₐ (x zero) *ₐ y (suc k) +ₐ (toA (suc zero) +ₐ toA k) *ₐ ((x (suc zero)) *ₐ (y k))
    ≈⟨ +ₐ-cong (*ₐ-assoc (toA (suc k)) (x zero) (y (suc k))) ≈ₐ-refl ⟩
        toA (suc k) *ₐ ((x zero) *ₐ y (suc k)) +ₐ (toA (suc zero) +ₐ toA k) *ₐ ((x (suc zero)) *ₐ (y k))
    ≈⟨ +ₐ-cong (*ₐ-cong (≈ₐ-sym $ +ₐ-identityˡ (toA (suc k))) ≈ₐ-refl) ≈ₐ-refl ⟩
        (0ₐ +ₐ toA (suc k)) *ₐ ((x zero) *ₐ y (suc k)) +ₐ (toA (suc zero) +ₐ toA k) *ₐ ((x (suc zero)) *ₐ (y k))
    ≈⟨ +ₐ-cong (*ₐ-cong (shift-suc zero k) ≈ₐ-refl) ≈ₐ-refl ⟩
        (toA (suc zero) +ₐ toA k) *ₐ ((x zero) *ₐ y (suc k)) +ₐ (toA (suc zero) +ₐ toA k) *ₐ ((x (suc zero)) *ₐ (y k))
    ≈⟨ ≈ₐ-sym $ distribˡₐ (toA (suc zero) +ₐ toA k) ((x zero) *ₐ y (suc k)) ((x (suc zero)) *ₐ (y k)) ⟩
        (toA (suc zero) +ₐ toA k) *ₐ ((x zero) *ₐ y (suc k) +ₐ (x (suc zero)) *ₐ (y k))
    ∎
*ᵢ-leibniz (suc n) k x y =
    begin
        (*ᵢ n (suc k) (deriv x) y +ₐ toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k +ₐ (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k)))) +ₐ toA k *ₐ x (suc (suc n)) *ₐ y k
    ≈⟨ +ₐ-cong (+ₐ-assoc (*ᵢ n (suc k) (deriv x) y) (toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k) (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k)))) ≈ₐ-refl ⟩
        (*ᵢ n (suc k) (deriv x) y +ₐ (toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k +ₐ (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k))))) +ₐ toA k *ₐ x (suc (suc n)) *ₐ y k
    ≈⟨ +ₐ-cong (+ₐ-cong ≈ₐ-refl (+ₐ-comm (toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k) (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k))))) ≈ₐ-refl ⟩
        (*ᵢ n (suc k) (deriv x) y +ₐ (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k)) +ₐ toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k)) +ₐ toA k *ₐ x (suc (suc n)) *ₐ y k
    ≈⟨ +ₐ-cong (≈ₐ-sym $ +ₐ-assoc (*ᵢ n (suc k) (deriv x) y) (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k))) (toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k)) ≈ₐ-refl ⟩
        ((*ᵢ n (suc k) (deriv x) y +ₐ (*ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k)))) +ₐ toA (suc (suc n)) *ₐ x (suc (suc n)) *ₐ y k) +ₐ toA k *ₐ x (suc (suc n)) *ₐ y k
    ≈⟨ +ₐ-cong (+ₐ-cong (≈ₐ-sym $ +ₐ-assoc (*ᵢ n (suc k) (deriv x) y) (*ᵢ n (suc k) x (deriv y)) (x (suc n) *ₐ (toA (suc k) *ₐ y (suc k)))) (*ₐ-assoc (toA (suc (suc n))) (x (suc (suc n))) (y k))) (*ₐ-assoc (toA k) (x (suc (suc n))) (y k)) ⟩
        ((*ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ (toA (suc k) *ₐ y (suc k))) +ₐ toA (suc (suc n)) *ₐ (x (suc (suc n)) *ₐ y k)) +ₐ toA k *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ +ₐ-cong (+ₐ-cong (+ₐ-cong ≈ₐ-refl (≈ₐ-sym $ *ₐ-assoc (x (suc n)) (toA (suc k)) (y (suc k)))) ≈ₐ-refl) ≈ₐ-refl ⟩
        ((*ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ x (suc n) *ₐ toA (suc k) *ₐ y (suc k)) +ₐ toA (suc (suc n)) *ₐ (x (suc (suc n)) *ₐ y k)) +ₐ toA k *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ +ₐ-cong (+ₐ-cong (+ₐ-cong ≈ₐ-refl (*ₐ-cong (*ₐ-comm (x (suc n)) (toA (suc k))) ≈ₐ-refl)) ≈ₐ-refl) ≈ₐ-refl ⟩
        ((*ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ toA (suc k) *ₐ x (suc n) *ₐ y (suc k)) +ₐ toA (suc (suc n)) *ₐ (x (suc (suc n)) *ₐ y k)) +ₐ toA k *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ +ₐ-assoc (*ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ toA (suc k) *ₐ x (suc n) *ₐ y (suc k)) (toA (suc (suc n)) *ₐ (x (suc (suc n)) *ₐ y k)) (toA k *ₐ (x (suc (suc n)) *ₐ y k)) ⟩
        *ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ toA (suc k) *ₐ x (suc n) *ₐ y (suc k) +ₐ (toA (suc (suc n)) *ₐ (x (suc (suc n)) *ₐ y k) +ₐ toA k *ₐ (x (suc (suc n)) *ₐ y k))
    ≈⟨ +ₐ-cong ≈ₐ-refl (≈ₐ-sym $ distribʳₐ (x (suc (suc n)) *ₐ y k) (toA (suc (suc n))) (toA k)) ⟩
        *ᵢ n (suc k) (deriv x) y +ₐ *ᵢ n (suc k) x (deriv y) +ₐ toA (suc k) *ₐ x (suc n) *ₐ y (suc k) +ₐ (toA (suc (suc n)) +ₐ toA k ) *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ +ₐ-cong (*ᵢ-leibniz n (suc k) x y) ≈ₐ-refl ⟩
        (toA (suc n) +ₐ toA (suc k)) *ₐ (*ᵢ (suc n) (suc k) x y) +ₐ (toA (suc (suc n)) +ₐ toA k) *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ +ₐ-cong (*ₐ-cong (shift-suc (suc n) k) ≈ₐ-refl) ≈ₐ-refl ⟩
        (toA (suc (suc n)) +ₐ toA k) *ₐ (*ᵢ (suc n) (suc k) x y) +ₐ (toA (suc (suc n)) +ₐ toA k) *ₐ (x (suc (suc n)) *ₐ y k)
    ≈⟨ ≈ₐ-sym $ distribˡₐ (toA (suc (suc n)) +ₐ toA k) (*ᵢ (suc n) (suc k) x y) (x (suc (suc n)) *ₐ y k) ⟩
        (toA (suc (suc n)) +ₐ toA k) *ₐ ((*ᵢ (suc n) (suc k) x y) +ₐ (x (suc (suc n)) *ₐ y k))
    ∎

-- *ᵢ-leibniz for k = 0
deriv-leibniz' : (n : ℕ) → ∀ x y → (*ᵢ n 0 (deriv x) y) +ₐ (*ᵢ n 0 x (deriv y)) ≈ₐ toA (suc n) *ₐ (*ᵢ (suc n) 0 x y)
deriv-leibniz' n x y =
    begin
        *ᵢ n 0 (deriv x) y +ₐ *ᵢ n 0 x (deriv y)
    ≈⟨ ≈ₐ-sym (+ₐ-identityʳ (*ᵢ n 0 (deriv x) y +ₐ *ᵢ n 0 x (deriv y))) ⟩
        *ᵢ n 0 (deriv x) y +ₐ *ᵢ n 0 x (deriv y) +ₐ 0ₐ
    ≈⟨ +ₐ-cong ≈ₐ-refl (≈ₐ-sym $ zeroˡₐ (x (suc n) *ₐ y 0)) ⟩
        *ᵢ n 0 (deriv x) y +ₐ *ᵢ n 0 x (deriv y) +ₐ 0ₐ *ₐ (x (suc n) *ₐ y 0)
    ≈⟨ +ₐ-cong ≈ₐ-refl (≈ₐ-sym $ *ₐ-assoc 0ₐ (x (suc n)) (y 0)) ⟩
        *ᵢ n 0 (deriv x) y +ₐ *ᵢ n 0 x (deriv y) +ₐ toA zero *ₐ x (suc n) *ₐ y 0
    ≈⟨ *ᵢ-leibniz n 0 x y ⟩
        (toA (suc n) +ₐ toA 0) *ₐ (*ᵢ (suc n) 0 x y)
    ≈⟨ *ₐ-cong (+ₐ-identityʳ (toA (suc n))) ≈ₐ-refl ⟩
        toA (suc n) *ₐ (*ᵢ (suc n) 0 x y)
    ∎

deriv-leibniz : ∀ x y → (deriv x * y + x * deriv y) ≈ (deriv (x * y))
deriv-leibniz x y n = deriv-leibniz' n x y
