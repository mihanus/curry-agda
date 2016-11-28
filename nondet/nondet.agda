-- Some basic structures and operations for dealing
-- with non-deterministic values.
--
-- @author Sergio Antoy, Michael Hanus, Steven Libby

module nondet where

open import bool
open import nat
open import list

infixr 8 _??_

----------------------------------------------------------------------
-- A tree datatype to represent a non-deterministic value of some type.
-- It is either a value or a choice between non-deterministic values.
----------------------------------------------------------------------

data ND (A : Set) : Set where
  Val  : A → ND A
  _??_ : ND A → ND A → ND A

----------------------------------------------------------------------
-- Some operations to define functions working this the ND datatype:

-- Apply a (deterministic) function to a non-deterministic argument.
-- This corresponds to a functor on the ND structure.
_$*_ : {A B : Set} → (A → B) → ND A → ND B
f $* (Val xs) = Val (f xs)
f $* (t1 ?? t2) = f $* t1 ?? f $* t2

-- Apply a non-deterministic function to a non-deterministic argument.
-- If ND would be an instance of the monad class, this is a monadic bind
-- with swapped arguments.
_*$*_ : {A B : Set} → (A → ND B) → ND A → ND B
f *$* (Val x)    = f x
f *$* (t1 ?? t2) = f *$* t1 ?? f *$* t2

-- Apply a binary non-deterministic function to non-deterministic arguments.
apply-nd2 : {A B C : Set} → (A → B → ND C) → ND A → ND B → ND C
apply-nd2 f a b = (λ x -> (λ y -> f x y) *$* b) *$* a

-- Apply a ternary non-deterministic function to non-deterministic arguments.
apply-nd3 : {A B C D : Set} → (A → B → C → ND D) → ND A → ND B → ND C → ND D
apply-nd3 f a b c = (λ x -> (λ y -> (λ z → f x y z) *$* c) *$* b) *$* a

-- Extend a deterministic function to one with non-deterministic result:
toND : {A B : Set} → (A → B) → A → ND B
toND f x = Val (f x)

----------------------------------------------------------------------
-- Some operations to define properties of non-deterministic values:

-- Count the number of values:
#vals : {A : Set} → ND A → ℕ
#vals (Val _) = 1
#vals (t1 ?? t2) = #vals t1 + #vals t2

-- Extract the list of all values:
vals-of : {A : Set} → ND A → 𝕃 A
vals-of (Val v)    = v :: []
vals-of (t1 ?? t2) = vals-of t1 ++ vals-of t2

-- All values in a Boolean tree are true:
always : ND 𝔹 → 𝔹
always (Val b)    = b
always (t1 ?? t2) = always t1 && always t2

-- There exists some true value in a Boolean tree:
eventually : ND 𝔹 → 𝔹
eventually (Val b)    = b
eventually (t1 ?? t2) = eventually t1 || eventually t2

-- All non-deterministic values satisfy a given predicate:
_satisfy_ : {A : Set} → ND A → (A → 𝔹) → 𝔹
(Val n)    satisfy p = p n
(t1 ?? t2) satisfy p = t1 satisfy p && t2 satisfy p

-- Every value in a tree is equal to the second argument w.r.t. a
-- comparison function provided as the first argument:
every : {A : Set} → (eq : A → A → 𝔹) → A → ND A → 𝔹
every eq x xs = xs satisfy (eq x)

----------------------------------------------------------------------
