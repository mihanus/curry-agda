-- Some theorems about operations on non-deterministic values

module nondet-thms where

open import bool
open import bool-thms
open import nat
open import eq
open import nat-thms
open import functions
open import nondet

----------------------------------------------------------------------
-- Theorems about values contained in non-deterministic values:

-- A proof that x is value of the non-deterministic tree y:
-- either it is equal to a deterministic value (ndrefl)
-- or it is somewhere in the tree.
-- If it is in the tree then we need to construct both branches of the tree,
-- and a proof that x is in one of the branches
-- A consequence of this is that any proof that x ∈ y contains the path
-- to x in the tree.
--
-- Example:
-- hInCoin : H ∈ coin
-- hInCoin = left (Val H) (Val T) ndrefl
--
-- Since H is on the left side of coin, we use the left constructor
-- The branches of the tree are (Val H) and (Val T),
-- and since H is identically equal to H this completes the proof.
data _∈_ {A : Set} (x : A) : (y : ND A) → Set where
  ndrefl : x ∈ (Val x)
  left   : (l : ND A) → (r : ND A) → x ∈ l → x ∈ (l ?? r)
  right  : (l : ND A) → (r : ND A) → x ∈ r → x ∈ (l ?? r)

-- A basic inductive lemma that shows that ∈ is closed under function
-- application. That is, if x ∈ nx, then f x ∈ f $* nx 
--
-- Example:
-- ndCons : ... → xs ∈ nxs → (x :: xs) ∈ (_::_ x) $* nxs
∈-$* : {A B : Set} → (f : A → B) → (x : A) → (nx : ND A)
        → x ∈ nx → (f x) ∈ (f $* nx)
∈-$* f x (Val .x) ndrefl = ndrefl
∈-$* f x (l ?? r) (left  .l .r k) =
  left  (f $* l) (f $* r) (∈-$* f x l k)
∈-$* f x (l ?? r) (right .l .r k) =
  right (f $* l) (f $* r) (∈-$* f x r k)

-- This is a similar result as ∈-$* but for non-deterministic application:
∈-*$* : {A B : Set} → (x : A) → (nx : ND A) → (f : A → B)
        → (nf : A → ND B) → x ∈ nx → f x ∈ nf x → f x ∈ (nf *$* nx)
∈-*$* x (Val .x) f nf ndrefl pf = pf
∈-*$* x (l ?? r) f nf (left  .l .r p) pf =
  left (nf *$* l) (nf *$* r) (∈-*$* x l f nf p pf)
∈-*$* x (l ?? r) f nf (right .l .r p) pf = 
  right (nf *$* l) (nf *$* r) (∈-*$* x r f nf p pf)

----------------------------------------------------------------------
-- Theorems about '$*':

-- Combine two $* applications into one:
$*-$* : ∀ {A B C : Set} → (f : B → C) (g : A → B) (xs : ND A)
            → f $* (g $* xs) ≡ (f ∘ g) $* xs
$*-$* f g (Val x) = refl
$*-$* f g (t1 ?? t2) rewrite $*-$* f g t1 | $*-$* f g t2 = refl

----------------------------------------------------------------------
-- Theorems about 'always':

-- Extend validity of a function with a deterministic argument to validity of
-- the corresponding non-deterministic function:
always-$* : ∀ {A : Set} → (p : A → 𝔹) (xs : ND A)
          → ((y : A) → p y ≡ tt)
          → always (p $* xs) ≡ tt
always-$* _ (Val y) prf = prf y
always-$* p (t1 ?? t2) prf
  rewrite always-$* p t1 prf
        | always-$* p t2 prf = refl

-- Extend validity of a function with a deterministic argument to validity of
-- the corresponding non-deterministic function:
always-*$* : ∀ {A : Set} → (p : A → ND 𝔹) (xs : ND A)
               → ((y : A) → always (p y) ≡ tt)
               → always (p *$* xs) ≡ tt
always-*$* _ (Val y) prf = prf y
always-*$* p (t1 ?? t2) prf
  rewrite always-*$* p t1 prf
        | always-*$* p t2 prf = refl

-- Extend validity of a deterministic function to validity of
-- corresponding function with non-deterministic result:
always-toND : ∀ {A : Set} → (p : A → 𝔹) (x : A)
          → (p x) ≡ tt → always (toND p x) ≡ tt
always-toND _ _ p = p

----------------------------------------------------------------------
-- Theorems about 'satisfy':

-- A theorem like filter-map in functional programming:
satisfy-$* : ∀ {A B : Set} → (f : A → B) (xs : ND A) (p : B → 𝔹)
             → (f $* xs) satisfy p ≡ xs satisfy (p ∘ f)
satisfy-$* _ (Val x) _ = refl
satisfy-$* f (t1 ?? t2) p
 rewrite satisfy-$* f t1 p
       | satisfy-$* f t2 p = refl

-- Extend validity of function with deterministic argument to validity of
-- non-deterministic function:
satisfy-*$* : ∀ {A B : Set} → (p : B → 𝔹) (f : A → ND B) (xs : ND A)
               → ((y : A) → (f y) satisfy p ≡ tt)
               → (f *$* xs) satisfy p ≡ tt
satisfy-*$* _ _ (Val y) prf = prf y
satisfy-*$* p f (t1 ?? t2) prf
  rewrite satisfy-*$* p f t1 prf
        | satisfy-*$* p f t2 prf = refl

----------------------------------------------------------------------
-- Theorems about 'every':

every-$* : ∀ (f : ℕ → ℕ) (v : ℕ) (x : ND ℕ) →
         every _=ℕ_ v x ≡ tt → every _=ℕ_ (f v) (f $* x) ≡ tt
every-$* f v (Val x) u rewrite =ℕ-to-≡ {v} {x} u | =ℕ-refl (f x) = refl
every-$* f v (t1 ?? t2) u
  rewrite every-$* f v t1 (&&-fst u)
        | every-$* f v t2 (&&-snd {every _=ℕ_ v t1} {every _=ℕ_ v t2} u) = refl

----------------------------------------------------------------------
-- This theorms allows to weaken a predicate which is always satisfied:
weak-always-predicate : ∀ {A : Set} → (p p1 : A → 𝔹) (xs : ND A)
                → xs satisfy p ≡ tt
                → xs satisfy (λ x → p1 x || p x) ≡ tt
weak-always-predicate p p1 (Val x) u rewrite u | ||-tt (p1 x) = refl
weak-always-predicate p p1 (t1 ?? t2) u
  rewrite weak-always-predicate p p1 t1 (&&-fst u)
        | weak-always-predicate p p1 t2 (&&-snd {t1 satisfy p} {t2 satisfy p} u)
  = refl

----------------------------------------------------------------------
