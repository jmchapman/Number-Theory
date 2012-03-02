{-# OPTIONS --type-in-type #-}

module sqrt2 where

rel : Set → Set
rel A = A → A → Set

pred : Set → Set
pred A = A → Set

data exists (A : Set)(B : A → Set) : Set where
  Witness : (u : A)(v : B u) → exists A B

existsElim : ∀{A B C} → exists A B → ((x : A) → B x → C) → C
existsElim (Witness u v) f = f u v

data _∧_ (A B : Set) : Set where
  pair : A → B → A ∧ B

andElimLeft : ∀{A B} → A ∧ B → A
andElimLeft (pair a b) = a

andElimRight : ∀{A B} → A ∧ B → B
andElimRight (pair a b) = b

data _∨_ (A B : Set) : Set where
  Inl : A → A ∨ B
  Inr : B → A ∨ B

orElim : ∀{A B C} → (A → C) → (B → C) → A ∨ B → C
orElim f g (Inl a) = f a
orElim f g (Inr b) = g b

noether : ∀ A → rel A → Set
noether A R = (P : A → Set) → 
  (∀ x → (∀ y → R y x → P y) → P x) → ∀ x → P x

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

infiniteDescent : (A : Set)(R : rel A)(P : pred A) → noether A R → 
  (∀ x → P x → exists A λ x1 → R x1 x ∧ P x1) → ∀ x → ¬ (P x)
infiniteDescent A R P = λ h1 h2 x → 
  h1 (λ y → ¬ (P y)) 
     (λ z h3 h4 → existsElim (h2 z h4) 
                             (λ y h5 → h3 y 
                                          (andElimLeft h5) 
                                          (andElimRight h5)))
     x

record AbMonoid (A : Set)(_≡_ : rel A) : Set where
  field ref   : ∀ {x} → x ≡ x
        sym   : ∀ {x y} → x ≡ y → y ≡ x
        trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
        _•_    : A → A → A
        cong  : ∀ {x1 x2 y1 y2} → x1 ≡ x2 → y1 ≡ y2 → 
                (x1 • y1) ≡ (x2 • y2)
        assoc : ∀ {x y z} → (x • (y • z)) ≡ ((x • y) • z)
        comm  : ∀ {x y} → (x • y) ≡ (y • x)

module ThAbMonoid (A : Set)(_≡_ : rel A)(m : AbMonoid A _≡_) where

  open AbMonoid m

  square : A → A
  square x = x • x

  multiple : A → rel A
  multiple p = λ x y → (p • x) ≡ y

  congLeft : ∀ {x y z} → y ≡ z → (y • x) ≡ (z • x)
  congLeft = λ h → cong h ref

  congRight : ∀ {x y z} → y ≡ z → (x • y) ≡ (x • z)
  congRight = λ h → cong ref h

  lemma0 : ∀ {x y z} → x ≡ z → y ≡ z → x ≡ y
  lemma0 = λ h h' → trans h (sym h')

  lemma2 : ∀ {x y} → x ≡ y → (square x) ≡ (square y)
  lemma2 = λ h → cong h h

  lemma3 : ∀ {x y z} → (x • (y • z)) ≡ (y • (x • z))
  lemma3 = lemma0 assoc (trans assoc (congLeft comm))

  lemma4 : ∀ {x y} → (x • (x • (square y))) ≡ (square (x • y))
  lemma4 = trans (congRight lemma3) assoc

  lemma5 : ∀ {p y y1} → (p • y1) ≡ y → 
           (p • (p • (square y1))) ≡ (square y)
  lemma5 = λ h → trans lemma4 (lemma2 h)

isCancel : (A : Set)(_≡_ : rel A)(m : AbMonoid A _≡_) → Set
isCancel A _≡_ m = ∀ {x y z} → (z • x) ≡ (z • y) → x ≡ y 
  where open AbMonoid m

module square (A : Set)(_≡_ : rel A)
              (m : AbMonoid A _≡_)(cancel : isCancel A _≡_ m) where
  open AbMonoid m
  open ThAbMonoid A _≡_ m

  slemma1 : ∀ {p u v w} → (p • u) ≡ w → (p • v) ≡ w → u ≡ v
  slemma1 = λ h2 h3 → cancel (lemma0 h2 h3)

  slemma2 : ∀ {p x y y1} → (p • (square x)) ≡ (square y) → 
                           (p • y1) ≡ y → (p • (square y1)) ≡ (square x)
  slemma2 = λ h1 h2 → slemma1 (lemma5 h2) h1

  exA : pred A → Set
  exA = exists A
  
  divides : rel A
  divides = λ x y → exA λ z → (x • z) ≡ y

  prime : pred A 
  prime = λ p → ∀ x y → divides p (x • y) → divides p x ∨ divides p y
  
  slemma3 : ∀ {p x} → prime p → divides p (square x) → divides p x
  slemma3 = λ h1 h2 → orElim (λ h → h) (λ h → h) (h1 _ _ h2)

  slemma4 : ∀ {p x y} → prime p → (p • (square x)) ≡ (square y) → 
            exA λ y1 → ((p • y1) ≡ y) ∧ ((p • (square y1)) ≡ (square x))
  slemma4 = λ h1 h2 → let rem = slemma3 h1 (Witness (square _) h2)
                      in  existsElim rem (λ y1 h3 →
                                     Witness y1 (pair h3 (slemma2 h2 h3)))

  Square : rel A 
  Square = λ p x → exA λ y → (p • square x) ≡ square y

  slemma5 : (p : A)(h2 : prime p)(x : A)(h3 : Square p x) →
           exA (λ x1 → ((p • x1) ≡ x) ∧ Square p x1)
  slemma5 p h2 x h3 = existsElim h3 λ y h4 → existsElim 
    (slemma4 h2 h4) 
    λ y1 h5 → let rem1 = andElimLeft h5; rem2 = (andElimRight h5) 
         in existsElim 
               (slemma4 h2 rem2)
               (λ x1 h6 → let rem3 = andElimLeft h6; rem4 = andElimRight h6 
                  in Witness x1 (pair rem3 (Witness y1 rem4)))
  
  isNotSquare : pred A
  isNotSquare = λ p → ∀ x y → ¬ ((p • square x) ≡ (square y))

  theorem : ∀ p → prime p → noether A (multiple p) → isNotSquare p
  theorem p = λ h1 h2 → 
    let rem = infiniteDescent A (multiple p) (Square p) h2 (slemma5 p h1)
    in  λ x y h3 → rem x (Witness y h3)

  {- This is the main result; it applies to the case where A is
      N* and p is 2, but it shows as well that any prime cannot
      be a square of a rational 
  -}
