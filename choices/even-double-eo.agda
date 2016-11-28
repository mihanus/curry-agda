-- Non-deterministic insert and permutation with choose oracle
-- The oracle is passed through the individual functions.

open import bool

module even-double-eo
  (Choice : Set)
  (choose : Choice → 𝔹)
  (lchoice : Choice → Choice)
  (rchoice : Choice → Choice)
 where

open import eq
open import bool-thms
open import nat
open import nat-thms
open import list

----------------------------------------------------------------------

-- double is deterministic:
double : ℕ → ℕ
double x = x + x

-- even is a deterministic predicate:
even : ℕ → 𝔹
even zero = tt
even (suc 0) = ff
even (suc (suc x)) = even x

-- eo yields an even and odd number close to the input value:
eo : Choice → ℕ → ℕ
eo ch n = if choose ch then n else (suc n)

-- auxiliary property for x+x instead of double:
even-x+x : ∀ (x : ℕ) → even (x + x) ≡ tt
even-x+x zero = refl
even-x+x (suc x) rewrite +suc x x | even-x+x x = refl

-- (even (double x)) is always true:
even-double-is-true : ∀ (x : ℕ) → even (double x) ≡ tt
even-double-is-true x rewrite even-x+x x = refl

-- (even (double (eo n))) is always true:
even-double-eo-is-true : ∀ (ch : Choice) (n : ℕ)
                        → even (double (eo ch n)) ≡ tt
even-double-eo-is-true ch n = even-double-is-true (eo ch n)


----------------------------------------------------------------------
