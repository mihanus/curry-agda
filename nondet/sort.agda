module sort where

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
ndinsert : {A : Set} -> A -> ND (list A) -> ND (list A)
ndinsert x (Val [] )       = Val ( x :: [])
ndinsert x (Val (y :: ys)) = (Val ( x :: y :: ys )) ?? ((_::_ y) $* (ndinsert x (Val ys)))
ndinsert x (l ?? r)        = (ndinsert x l) ?? (ndinsert x r)

--non-deterministic permutation
--this is identical to the curry code (except for the Val constructor)
perm : {A : Set} -> (list A) -> ND (list A)
perm []        = Val []
perm (x :: xs) = ndinsert x (perm xs)

--insert a value into a sorted list.
--this is identical to curry or haskell code.
--
--note that the structure here is identical to ndinsert
insert : {A : Set} -> (A -> A -> 𝔹) -> A -> list A -> list A
insert _   x []        = x :: []
insert _<_ x (y :: ys) = if x < y
                         then (x :: y :: ys)
                         else (y :: insert _<_ x ys)

--simple insertion sort
--again this is identical to curry or haskell
--also, note that the structure is identical to perm
sort : {A : Set} -> (A -> A -> 𝔹) -> list A -> list A
sort _ []     = []
sort p (x :: xs) = insert p x (sort p xs)


-- Proof:  if xs ∈ nxs then x::xs ∈ ndinsert x nxs
insId : {A : Set} -> (x : A) -> (xs : list A) -> (x :: xs) ∈ (ndinsert x (Val xs))
insId x [] = ndrefl
insId x (y :: xs) = left (Val (x :: y :: xs)) ((_::_ y) $* (ndinsert x (Val xs))) ndrefl

--If introduction rule for non-deterministic values.
--if x and y are both possible values in z then
--∀ c. if c then x else y will give us either x or y, so it must be a possible value of z.
--
ifIntro : {A : Set} -> (x : A) -> (y : A) -> (z : ND A) -> (p : x ∈ z) -> (q : y ∈ z) -> (c : 𝔹) -> (if c then x else y) ∈ z
ifIntro x y z p q tt = p
ifIntro x y z p q ff = q

---------------------------------------------------------------------------
--
-- this should prove that if xs ∈ nxs then, insert x xs ∈ ndinsert x nxs
-- parameters:
-- c         : a comparison operator that is needed for insert
-- x         : the value we are inserting into the list
-- xs        : the list
-- nxs       : a non-deterministic list, we know that xs is a possible value for nxs
-- xs ∈ nxs : the proof that xs is somewhere in nxs
--
--retruns: insert c x xs ∈ ndinsert x nxs
--  a proof that inserting a value in a list is ok with non-deterministic lists
insert=ndinsert : {A : Set} -> (c : A -> A -> 𝔹) -> (x : A) -> (xs : list A) -> (nxs : ND (list A)) -> xs ∈ nxs -> (insert c x xs) ∈ (ndinsert x nxs)

--the first two cases are simple, either we are inserting into an empty list, in which case it's trivial
--or, the list doesn't match the non-deterministic case.  This is an imposible case
insert=ndinsert _ x [] (Val [])       _  = ndrefl
insert=ndinsert _ x [] (Val (_ :: _)) ()

--the next two cases are just structural recursion on the non-deterministic tree.
insert=ndinsert c x ys (l ?? r) (left  .l .r p) = left  (ndinsert x l) (ndinsert x r) (insert=ndinsert c x ys l p)
insert=ndinsert c x ys (l ?? r) (right .l .r p) = right (ndinsert x l) (ndinsert x r) (insert=ndinsert c x ys r p)

--The final case is the interesting one.
--We reached a leaf in the non-deterministic tree, so we have a deterministic value.
--by definition this is equal to the deterministic list (y :: ys)
--At this point we have two possible cases.
--Either x is smaller then every element in (y :: ys), in which case it's inserted at the front,
--or x is larger than y, in which case it's inserted somewhere in ys.
--Since both of these cases are covered by ndinsert we can invoke the ifIntro lemma, to say that we don't care which case it is.
--
--variables:
-- step    : one step of insert
-- l       : the left hand side of insert c x xs (the then branch)
-- r       : the right hand side of insert c x xs (the else branch)
-- nr      : a non-deterministic r
-- (Val l) : a non-deterministic l (but since ndinsert only has a deterministic value on the left it's not very interesting)
-- rec     : The recursive call.  If x isn't inserted into the front, then we need to find it.
-- l∈step : a proof that l is a possible value for step
-- r∈step : a proof that r is a possible value for step
insert=ndinsert _<_ x (y :: ys) (Val (.y :: .ys)) ndrefl = ifIntro l r step l∈step r∈step (x < y)
  where step   = ndinsert x (Val (y :: ys))
        l      = ( x :: y :: ys)
        r      = y :: insert _<_ x ys
        nr     = (_::_ y) $* (ndinsert x (Val ys))
        rec    = ∈-$* (_::_ y) (insert _<_ x ys) (ndinsert x (Val ys)) (insert=ndinsert _<_ x ys (Val ys) ndrefl)
        r∈step = right (Val l) nr rec
        l∈step = left  (Val l) nr ndrefl

---------------------------------------------------------------------------

-- main theorem.  Sorting a list preserves permutations
--all of the work is really done by insert=ndinsert
sortPerm : {A : Set} -> (c : A -> A -> 𝔹) -> (xs : list A) -> sort c xs ∈ perm xs
sortPerm _<_ []        = ndrefl
sortPerm _<_ (x :: xs) = insert=ndinsert _<_ x (sort _<_ xs) (perm xs) (sortPerm _<_ xs)

