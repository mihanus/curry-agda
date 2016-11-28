-- Proof: if we non-deterministically select an element
-- which is less-than-or-equal than all other elements,
-- such a result is the minimum of the list.
-- This holds for any non-deterministically selected element.

-- Basically, this is the translation of the Curry rule:
--
--   min-nd xs@(_++[x]++_) | all (x<=) xs = x
--

open import bool

module minlist-is-correct
  (Choice : Set)
  (choose : Choice → 𝔹)
  (lchoice : Choice → Choice)
  (rchoice : Choice → Choice)
 where

open import eq
open import bool-thms
open import bool-thms2
open import nat
open import nat-thms
open import list
open import maybe
open import inspect

----------------------------------------------------------------------
-- Some auxiliaries:

-- We define our own less-or-equal since the standard definition with
-- if-then-else produces too many branches:

_<=_ : ℕ → ℕ → 𝔹
0 <= y = tt
(suc x) <= 0 = ff
(suc x) <= (suc y) = x <= y

-- Some properties about less-or-equal:

<=-refl : ∀ (x : ℕ) → x <= x ≡ tt
<=-refl 0 = refl
<=-refl (suc x) = <=-refl x

<=-trans : ∀ (x y z : ℕ) → x <= y ≡ tt → y <= z ≡ tt → x <= z ≡ tt
<=-trans zero y z p1 p2 = refl
<=-trans (suc x) zero z p1 p2 = 𝔹-contra p1
<=-trans (suc x) (suc y) zero p1 p2 = 𝔹-contra p2
<=-trans (suc x) (suc y) (suc z) p1 p2 = <=-trans x y z p1 p2

<=-< : ∀ (x y : ℕ) → x <= y ≡ ff → y < x ≡ tt
<=-< zero x ()
<=-< (suc x) zero p = refl
<=-< (suc x) (suc y) p = <=-< x y p

<-<= : ∀ (x y : ℕ) → x < y ≡ tt → y <= x ≡ ff
<-<= x zero p rewrite <-0 x = 𝔹-contra p
<-<= zero (suc y) p = refl
<-<= (suc x) (suc y) p = <-<= x y p

<-<=-ff : ∀ (x y : ℕ) → x < y ≡ ff → y <= x ≡ tt
<-<=-ff zero zero p = refl
<-<=-ff zero (suc y) p = 𝔹-contra (sym p)
<-<=-ff (suc x) zero p = refl
<-<=-ff (suc x) (suc y) p = <-<=-ff x y p

<-<=-trans : ∀ (x y z : ℕ) → x < y ≡ tt → y <= z ≡ tt → x < z ≡ tt
<-<=-trans zero zero z p1 p2 = 𝔹-contra p1
<-<=-trans zero (suc y) zero p1 p2 = 𝔹-contra p2
<-<=-trans zero (suc y) (suc z) p1 p2 = refl
<-<=-trans (suc x) zero z p1 p2 = 𝔹-contra p1
<-<=-trans (suc x) (suc y) zero p1 p2 = 𝔹-contra p2
<-<=-trans (suc x) (suc y) (suc z) p1 p2 = <-<=-trans x y z p1 p2


----------------------------------------------------------------------
-- More lemmas about ordering relations:


leq-if : ∀ (x y z : ℕ)
      → y <= x && y <= z ≡ (if x <= z then y <= x else y <= z)
leq-if x y z with inspect (y <= x)
leq-if x y z | it tt p1 with inspect (x <= z)
... | it tt p2 rewrite p1 | p2 | <=-trans y x z p1 p2 = refl
... | it ff p2 rewrite p1 | p2 = refl
leq-if x y z | it ff p1 with inspect (x <= z)
... | it tt p2 rewrite p1 | p2 = refl
... | it ff p2 rewrite p1 | p2
           | <-<= z y (<-trans {z} {x} {y} (<=-< x z p2) (<=-< y x p1)) = refl

le-if : ∀ (x y z : ℕ)
     → y < x && y < z ≡ (if x <= z then y < x else y < z)
le-if x y z with inspect (y < x)
le-if x y z | it tt p1 with inspect (x <= z)
... | it tt p2 rewrite p1 | p2 | <-<=-trans y x z p1 p2 = refl
... | it ff p2 rewrite p1 | p2 = refl
le-if x y z | it ff p1 with inspect (x <= z)
... | it tt p2 rewrite p1 | p2 = refl
... | it ff p2 rewrite p1 | p2
         | <-asym {z} {y} (<-<=-trans z x y (<=-< x z p2) (<-<=-ff y x p1))
  = refl

----------------------------------------------------------------------
-- A lemma relating equality and orderings:

=ℕ-not-le : ∀ (m n : ℕ) → m =ℕ n  ≡ ~ (m < n) && m <= n
=ℕ-not-le zero zero = refl
=ℕ-not-le zero (suc m) = refl
=ℕ-not-le (suc n) zero = refl
=ℕ-not-le (suc n) (suc m) = =ℕ-not-le n m

----------------------------------------------------------------------
-- This is the translation of the Curry program:

-- Check whether all elements of a list satisfy a given predicate:
all : {A : Set} → (A → 𝔹) → 𝕃 A → 𝔹
all _ [] = tt
all p (x :: xs) = p x && all p xs

-- Deterministic min-d:
min-d : (l : 𝕃 ℕ) → is-empty l ≡ ff → ℕ
min-d []        ()
min-d (x :: []) _ = x
min-d (x :: y :: xs) _ =
  --if x <= min-d (y :: xs) refl then x else min-d (y :: xs) refl
  let z = min-d (y :: xs) refl
   in if x <= z then x else z

-- Select some element from a list:
select : {A : Set} → Choice → 𝕃 A -> maybe A
select _  []        = nothing
select ch (x :: xs) = if choose ch then just x
                                   else select (lchoice ch) xs

-- Select elements with a property from a list:
select-with : {A : Set} → Choice → (A → 𝔹) → 𝕃 A  → maybe A
select-with _  p [] = nothing
select-with ch p (x :: xs) =
  if choose ch then (if p x then just x else nothing)
               else select-with (lchoice ch) p xs

{-
-- more or less original definition:
min-nd : Choice → 𝕃 ℕ -> maybe ℕ
min-nd ch xs = (select ch xs) ≫=maybe
               (λ y → if all (_<=_ y) xs then just y else nothing)
-}

min-nd : Choice → (xs : 𝕃 ℕ) → maybe ℕ
min-nd ch xs = select-with ch (λ x → all (_<=_ x) xs) xs

----------------------------------------------------------------------

-- Proof of the correctness of the operation select-with:
select-with-correct : ∀ {A : Set}
                   → (ch : Choice) (p : A → 𝔹) (xs : 𝕃 A) (z : A)
                   → select-with ch p xs ≡ just z → p z ≡ tt
select-with-correct ch p [] z ()
select-with-correct ch p (x :: xs) z u with choose ch
select-with-correct ch p (x :: xs) z u | tt with inspect (p x)
select-with-correct ch p (x :: xs) z u | tt | it tt v rewrite v | u | down-≡ u
 = v
select-with-correct ch p (x :: xs) z u | tt | it ff v rewrite v with u
select-with-correct ch p (x :: xs) z u | tt | it ff v | ()
select-with-correct ch p (x :: xs) z u | ff =
  select-with-correct (lchoice ch) p xs z u 

----------------------------------------------------------------------
-- First step: if y smaller than all elements, y is smaller than the minimum:
all-leq-min : ∀ (y x : ℕ) (xs : 𝕃 ℕ)
           → all (_<=_ y) (x :: xs) ≡ y <= min-d (x :: xs) refl
all-leq-min y x [] = &&-tt (y <= x)
all-leq-min y x (z :: zs)
  rewrite all-leq-min y z zs
    | ite-arg (_<=_ y) (x <= min-d (z :: zs) refl) x (min-d (z :: zs) refl)
 = leq-if x y (min-d (z :: zs) refl)

-- Now we can prove:
-- if min-nd selects an element, it is smaller or equal than the minimum:
min-nd-select-min-d : ∀ (ch : Choice) (x : ℕ) (xs : 𝕃 ℕ) (z : ℕ)
      → min-nd ch (x :: xs) ≡ just z → z <= min-d (x :: xs) refl ≡ tt
min-nd-select-min-d ch x xs z u
 rewrite sym (all-leq-min z x xs)
       | select-with-correct ch (λ y → all (_<=_ y) (x :: xs)) (x :: xs) z u
 = refl

----------------------------------------------------------------------
-- Next step: if y smaller than all elements, y is smaller than the minimum:
all-less-min : ∀ (y x : ℕ) (xs : 𝕃 ℕ)
           → all (_<_ y) (x :: xs) ≡ y < min-d (x :: xs) refl
all-less-min y x [] rewrite &&-tt (y < x) = refl
all-less-min y x (z :: zs)
  rewrite all-less-min y z zs
    | ite-arg (_<_ y) (x <= min-d (z :: zs) refl) x (min-d (z :: zs) refl)
 = le-if x y (min-d (z :: zs) refl)

-- Next want to prove that the element selected by min-nd cannot be smaller
-- than the minimum.

-- For this purpose, we prove an auxiliary lemma:
-- If an element is selected from a list, it cannot be smaller than all elements
select-with-all<-ff : ∀ (ch : Choice) (p : ℕ → 𝔹) (xs : 𝕃 ℕ) (z : ℕ)
                   → select-with ch p xs ≡ just z → all (_<_ z) xs ≡ ff
select-with-all<-ff ch _ [] z ()
select-with-all<-ff ch p (x :: xs) z u with (choose ch)
select-with-all<-ff ch p (x :: xs) z u | tt with (p x)
select-with-all<-ff ch p (x :: xs) z u | tt | tt rewrite down-≡ u | <-irrefl z
  = refl
select-with-all<-ff ch p (x :: xs) z () | tt | ff
select-with-all<-ff ch p (x :: xs) z u | ff
  rewrite select-with-all<-ff (lchoice ch) p xs z u | &&-ff (z < x) = refl

-- Now we can prove: if min-nd selects an element, it cannot be smaller
-- than all other elements:
min-nd-select-all<-ff : ∀ (ch : Choice) (xs : 𝕃 ℕ) (z : ℕ)
      → min-nd ch xs ≡ just z → all (_<_ z) xs ≡ ff
min-nd-select-all<-ff ch xs z u
 rewrite select-with-all<-ff ch (λ y → all (_<=_ y) xs) xs z u  = refl

----------------------------------------------------------------------

-- This is the main theorem:
min-nd-theorem : ∀ (ch : Choice) (x : ℕ) (xs : 𝕃 ℕ) (z : ℕ)
           → min-nd ch (x :: xs) ≡ just z → z =ℕ min-d (x :: xs) refl ≡ tt
min-nd-theorem ch x xs z u
 rewrite
   =ℕ-not-le z (min-d (x :: xs) refl)   -- split equality into no less and leq
 | min-nd-select-min-d ch x xs z u       -- min-nd selects leq min. elements
 | sym (all-less-min z x xs)             -- less-than min. elements satisfy all<
 | min-nd-select-all<-ff ch (x :: xs) z u -- min-nd can't select any all< element
 = refl

----------------------------------------------------------------------
