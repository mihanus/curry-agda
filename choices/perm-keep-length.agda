-- Non-deterministic insert and permutation with choose oracle
-- The module abstracts over the choice structure by importing it.

open import bool

module perm-keep-length
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

-- Non-deterministic insert:
ndinsert : {a : Set} → Choice → a → 𝕃 a  → 𝕃 a
ndinsert _  n []        = n :: []
ndinsert ch n (x :: xs) =
  if choose ch then n :: x :: xs
               else x :: ndinsert (lchoice ch) n xs

perm : {a : Set} → Choice → 𝕃 a  → 𝕃 a
perm _  []        = []
perm ch (x :: xs) = ndinsert (lchoice ch) x (perm (rchoice ch) xs)

----------------------------------------------------------------------

-- Non-deterministic insertion increases the list length by one:
insert-inc-length : ∀ {a : Set} → (ch : Choice) (x : a) (xs : 𝕃 a)
                 → length (ndinsert ch x xs) ≡ suc (length xs)
insert-inc-length ch x [] = refl
insert-inc-length ch x (y :: ys) with choose ch
... | tt = refl
... | ff rewrite insert-inc-length (lchoice ch) x ys = refl

-- The length of a permuted list is identical to the length of the list:
perm-length : ∀ {a : Set} → (ch : Choice) (xs : 𝕃 a)
           → length (perm ch xs) =ℕ length xs ≡ tt
perm-length ch [] = refl
perm-length ch (x :: xs)
  rewrite insert-inc-length (lchoice ch) x (perm (rchoice ch) xs)
        | perm-length (rchoice ch) xs
  = refl

----------------------------------------------------------------------
