module inspect where

open import eq

-- From Norell's tutorial:

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x ≡ y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

