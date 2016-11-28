-- Proof of: ∀ (x : ND ℕ) → always (even (double (eo x))) ≡ tt

module even-double-eo where

open import bool
open import nat
open import eq
open import nat-thms
open import nondet
open import nondet-thms
open import functions

----------------------------------------------------------------------

-- A definition of double with addition.
double : ℕ → ℕ
double x = x + x

-- even is a deterministic predicate:
even : ℕ → 𝔹
even zero = tt
even (suc 0) = ff
even (suc (suc x)) = even x

-- eo yields an even and odd number close to the input value:
eo : ℕ → ND ℕ
eo n = Val n ?? Val (suc n)

-- auxiliary property for x+x instead of double:
even-x+x : (x : ℕ) → even (x + x) ≡ tt
even-x+x zero = refl
even-x+x (suc x) rewrite +suc x x | even-x+x x = refl

-- (even (double x)) is always true:
even-double-is-true : ∀ (x : ℕ) → even (double x) ≡ tt
even-double-is-true x rewrite even-x+x x = refl

-- Proof of main result:
even-double-eo-true : (n : ℕ) → always ((even ∘ double) $* (eo n)) ≡ tt
even-double-eo-true n = always-$* (even ∘ double) (eo n) even-double-is-true

-- Alternative statement and proof:
double-eo-satisfy-even : ∀ (n : ℕ) → (double $* (eo n)) satisfy even ≡ tt
double-eo-satisfy-even n
  rewrite even-double-is-true n | +suc n n | even-double-is-true n = refl


----------------------------------------------------------------------
