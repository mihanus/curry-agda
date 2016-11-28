module perm-keep-length where

open import nat
open import list
open import nondet
open import bool
open import bool-thms
open import eq
open import nat-thms
open import nondet-thms

-- Non-deterministic insert:
ndinsert : {a : Set} → a → 𝕃 a  → ND (𝕃 a)
ndinsert x []        = Val (x :: [])
ndinsert x (y :: ys) = Val (x :: y :: ys)
                    ?? (_::_ y) $* (ndinsert x ys)
                    
-- Permutation:
perm : {a : Set} → 𝕃 a  → ND (𝕃 a)
perm []        = Val []
perm (x :: xs) = ndinsert x *$* (perm xs)


----------------------------------------------------------------------

-- Non-deterministic insertion increases the list length by one:
insert-inc-length : {a : Set} (x : a) → (xs : 𝕃 a)
      → (ndinsert x xs) satisfy (λ ys → length ys =ℕ suc (length xs)) ≡ tt
insert-inc-length x [] = refl
insert-inc-length x (y :: ys)
 rewrite =ℕ-refl (length ys)
       | satisfy-$* (_::_ y) (ndinsert x ys)
                    (λ zs → length zs =ℕ suc (suc (length ys)))
       | insert-inc-length x ys = refl

-- If the length of the input list is n, ndinsert increases it to (suc n):
insert-suc-length : {a : Set} → (n : ℕ) (x : a) (xs : 𝕃 a)
       → length xs =ℕ n ≡ tt
       → ndinsert x xs satisfy (λ ys → length ys =ℕ suc n) ≡ tt
insert-suc-length n x [] p = p 
insert-suc-length n x (y :: ys) p
 rewrite =ℕ-to-≡ {suc (length ys)} {n} p | =ℕ-refl n |
         satisfy-$* (_::_ y) (ndinsert x ys) (λ zs → length zs =ℕ suc n)
       | sym (=ℕ-to-≡ {suc (length ys)} {n} p)
       | insert-inc-length x ys
 = refl

-- The previous lemma is also valid on non-deterministic lists:
ins-suc-nondet : {a : Set} → (n : ℕ) → (x : a) → (t : ND (𝕃 a))
       → t satisfy (λ xs → length xs =ℕ n) ≡ tt
       → (ndinsert x *$* t) satisfy (λ xs → length xs =ℕ suc n) ≡ tt
ins-suc-nondet n x (Val xs) p = insert-suc-length n x xs p
ins-suc-nondet n x (t1 ?? t2) p
 rewrite ins-suc-nondet n x t1 (&&-fst p) 
       | ins-suc-nondet n x t2 (&&-snd {t1 satisfy (λ xs → length xs =ℕ n)} p)
 = refl

-- The length of a permuted list is identical to the length of the list:
perm-length : {a : Set} → (xs : 𝕃 a)
       → (perm xs) satisfy (λ ys → length ys =ℕ length xs) ≡ tt
perm-length [] = refl
perm-length (x :: xs) = ins-suc-nondet (length xs) x (perm xs) (perm-length xs)
