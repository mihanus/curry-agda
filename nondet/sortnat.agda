-- Proof: insertion sort computes a permutation of the input list

module sortnat where

open import bool
open import eq
open import nat
open import list
open import nondet
open import nondet-thms

-- non-deterministic insert.
--This takes a nondeterministic list because I need to be able to call it with the result of perm
--
--implementation in curry:
-- ndinsert x [] = []
-- ndinsert x (y:ys) = (x : y : xs) ? (y : insert x ys)
ndinsert : {A : Set} → A → 𝕃 A → ND (𝕃 A)
ndinsert x []        = Val ( x :: [])
ndinsert x (y :: ys) = (Val ( x :: y :: ys ))
                    ?? ((_::_ y) $* (ndinsert x ys))

--non-deterministic permutation
--this is identical to the curry code (except for the Val constructor)
perm : {A : Set} → (𝕃 A) → ND (𝕃 A)
perm []        = Val []
perm (x :: xs) = (ndinsert x) *$* (perm xs)

--insert a value into a sorted list.
--this is identical to curry or haskell code.
--
--note that the structure here is identical to ndinsert
insert : ℕ → 𝕃 ℕ → 𝕃 ℕ
insert x []        = x :: []
insert x (y :: ys) = if x < y then (x :: y :: ys)
                              else (y :: insert x ys)

--simple insertion sort
--again this is identical to curry or haskell
--also, note that the structure is identical to perm
sort : 𝕃 ℕ → 𝕃 ℕ
sort []     = []
sort (x :: xs) = insert x (sort xs)


--If introduction rule for non-deterministic values.
--if x and y are both possible values in z then
--∀ c. if c then x else y will give us either x or y, so it must be a possible value of z.
--
ifIntro : {A : Set} → (x : A) → (y : A) → (nx : ND A)
       → x ∈ nx → y ∈ nx → (c : 𝔹) → (if c then x else y) ∈ nx
ifIntro x y nx p q tt = p
ifIntro x y nx p q ff = q

---------------------------------------------------------------------------
--
-- this should prove that if xs ∈ nxs then, insert x xs ∈ ndinsert x nxs
-- parameters:
-- x         : the value we are inserting into the list
-- xs        : the list
--
--returns: insert x xs ∈ ndinsert x xs
--  a proof that inserting a value in a list is ok with non-deterministic lists

insert=ndinsert : (y : ℕ) → (xs : 𝕃 ℕ) → (insert y xs) ∈ (ndinsert y xs)

-- the first case is simple: inserting into an empty list is trivial
insert=ndinsert y [] = ndrefl

--The recursive case is the interesting one.
--The list to insert an element has the form (x :: xs)
--At this point we have two possible cases.
--Either y is smaller then every element in (x :: xs), in which case it's inserted at the front,
--or y is larger than x, in which case it's inserted somewhere in xs.
--Since both of these cases are covered by ndinsert we can invoke the ifIntro lemma, to say that we don't care which case it is.
--
--variables:
-- step    : one step of insert
-- l       : the left hand side of insert y xs (the then branch)
-- r       : the right hand side of insert y xs (the else branch)
-- nr      : a non-deterministic r
-- (Val l) : a non-deterministic l (but since ndinsert only has a deterministic value on the left it's not very interesting)
-- rec     : The recursive call.  If y isn't inserted into the front, then we need to find it.
-- l∈step : a proof that l is a possible value for step
-- r∈step : a proof that r is a possible value for step
insert=ndinsert y (x :: xs) = ifIntro l r step l∈step r∈step (y < x)
  where step   = ndinsert y (x :: xs)
        l      = (y :: x :: xs)
        r      = x :: insert y xs
        nl     = Val l
        nr     = (_::_ x) $* (ndinsert y xs)
        rec    = ∈-$* (_::_ x) (insert y xs) (ndinsert y xs)
                      (insert=ndinsert y xs)
        l∈step = left  nl nr ndrefl
        r∈step = right nl nr rec

---------------------------------------------------------------------------

-- Main theorem: Sorting a list preserves permutations
-- all of the work is really done by insert=ndinsert
sortPerm : (xs : 𝕃 ℕ) → sort xs ∈ perm xs
sortPerm []        = ndrefl
sortPerm (x :: xs) = ∈-*$* (sort xs) (perm xs) (insert x) (ndinsert x)
                           (sortPerm xs) (insert=ndinsert x (sort xs))

