module boolean where

Some algebraic preliminaries.
```
data _≈_ {A : Set} (x : A) : A → Set where
    refl : x ≈ x
infix 4 _≈_

pattern erefl x = refl {x = x}

trans : ∀ {A : Set} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
trans refl refl = refl

module ≈-Reasoning {A : Set} where

    _∎ : ∀ (x : A) → x ≈ x
    x ∎ = erefl x

    _≈⟨_⟩_ : ∀(x : A) {y z : A} → x ≈ y → y ≈ z → x ≈ z
    x ≈⟨ x≈y ⟩ y≈z = trans x≈y y≈z


Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

open import Data.Product using (_×_; _,_)

Involutive : {A : Set} → Op₁ A → Set
Involutive f = ∀ x → f(f x) ≈ x

SelfInverse : {A : Set} → Op₁ A → Set
SelfInverse f = ∀ {x y} → f x ≈ y → x ≈ f y

Idempotent : {A : Set} → Op₂ A → Set
Idempotent _·_ = ∀ x → (x · x) ≈ x

LeftIdentity : {A : Set} → A → Op₂ A → Set
LeftIdentity e _·_ = ∀ x → (e · x) ≈ x

RightIdentity : {A : Set} → A → Op₂ A → Set
RightIdentity e _·_ = ∀ x → (x · e) ≈ x

Identity : {A : Set} → A → Op₂ A → Set
Identity e · = (LeftIdentity e ·) × (RightIdentity e ·)

LeftZero : {A : Set} → A → Op₂ A → Set _
LeftZero z _·_ = ∀ x → (z · x) ≈ z

RightZero : {A : Set} → A → Op₂ A → Set _
RightZero z _·_ = ∀ x → (x · z) ≈ z



Symmetric : {A : Set} → Op₂ A → Set _
Symmetric _·_ = ∀ x y → (x · y) ≈ (y · x)

Associative : {A : Set} → Op₂ A → Set _
Associative _·_ = ∀ x y z → ((x · y) · z) ≈ (x · (y · z))
```

A boolean is a value of type 𝔹. There are only two such values: `true` and `false`.
```
data 𝔹 : Set where
    true  : 𝔹
    false : 𝔹
```

We will be working with the following boolean operators.
```
¬ : Op₁ 𝔹
¬ true = false
¬ false = true

_≡_ : Op₂ 𝔹
true ≡ true = true
true ≡ false = false
false ≡ true = false
false ≡ false = true

_≢_ : Op₂ 𝔹
true ≢ true = false
true ≢ false = true
false ≢ true = true
false ≢ false = false

_⇒_ : Op₂ 𝔹
true ⇒ true = true
true ⇒ false = false
false ⇒ true = true
false ⇒ false = true

_⇐_ : Op₂ 𝔹
true ⇐ true = true
true ⇐ false = true
false ⇐ true = false
false ⇐ false = true

_∨_ : Op₂ 𝔹
true ∨ true = true
true ∨ false = true
false ∨ true = true
false ∨ false = false

_∧_ : Op₂ 𝔹
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false
```

Left first investigate the properties of ¬ .
```
¬-involutive : Involutive ¬
¬-involutive true = refl
¬-involutive false = refl


¬-self-inverse : SelfInverse ¬
¬-self-inverse {true} {true} = λ ()
¬-self-inverse {true} {false} = λ _ → refl
¬-self-inverse {false} {true} = λ _ → refl
¬-self-inverse {false} {false} = λ ()
```

Next, let us investigate the properties of _≡_.
```
≡-left-identity : LeftIdentity true _≡_ 
≡-left-identity true = refl
≡-left-identity false = refl

≡-right-identity : RightIdentity true _≡_
≡-right-identity true = refl
≡-right-identity false = refl

≡-identity : Identity true _≡_
≡-identity = (≡-left-identity , ≡-right-identity)

≡-symmetric : Symmetric _≡_
≡-symmetric true true = refl
≡-symmetric true false = refl
≡-symmetric false true = refl
≡-symmetric false false = refl

≡-associative : Associative _≡_
≡-associative true true true = refl
≡-associative true true false = refl
≡-associative true false true = refl
≡-associative true false false = refl
≡-associative false true true = refl
≡-associative false true false = refl
≡-associative false false true = refl
≡-associative false false false = refl
```

The properties of _≢_ match those of ≡ .
```
≢-left-identity : LeftIdentity false _≢_ 
≢-left-identity true = refl
≢-left-identity false = refl

≢-right-identity : RightIdentity false _≢_
≢-right-identity true = refl
≢-right-identity false = refl

≢-identity : Identity false _≢_
≢-identity = (≢-left-identity , ≢-right-identity)

≢-symmetric : Symmetric _≢_
≢-symmetric true true = refl
≢-symmetric true false = refl
≢-symmetric false true = refl
≢-symmetric false false = refl

≢-associative : Associative _≢_
≢-associative true true true = refl
≢-associative true true false = refl
≢-associative true false true = refl
≢-associative true false false = refl
≢-associative false true true = refl
≢-associative false true false = refl
≢-associative false false true = refl
≢-associative false false false = refl
```

Next, let's prove some properties of ⇒ and ⇐ .
```
⇒-left-identity : LeftIdentity true _⇒_
⇒-left-identity true = refl
⇒-left-identity false = refl

⇒-right-zero : RightZero true _⇒_
⇒-right-zero true = refl
⇒-right-zero false = refl

⇐-right-identity : RightIdentity true _⇐_
⇐-right-identity true = refl
⇐-right-identity false = refl

⇐-left-zero : LeftZero true _⇐_
⇐-left-zero true = refl
⇐-left-zero false = refl
```

Finally for now, let us prove some properties of ∨ and ∧ .
```
--idempotence

∨-idempotence : Idempotent _∨_
∨-idempotence true = refl
∨-idempotence false = refl

∧-idempotent : Idempotent _∧_
∧-idempotent true = refl
∧-idempotent false = refl

∨-symmetric : Symmetric _∨_
∨-symmetric true true = refl
∨-symmetric true false = refl
∨-symmetric false true = refl
∨-symmetric false false = refl

∧-symmetric : Symmetric _∧_
∧-symmetric true true = refl
∧-symmetric true false = refl
∧-symmetric false true = refl
∧-symmetric false false = refl

∨-left-identity : LeftIdentity false _∨_
∨-left-identity true = refl
∨-left-identity false = refl

∨-right-identity : RightIdentity false _∨_
∨-right-identity true = refl
∨-right-identity false = refl

∨-identity : Identity false _∨_
∨-identity = (∨-left-identity , ∨-right-identity)

∧-left-identity : LeftIdentity true _∧_
∧-left-identity true = refl 
∧-left-identity false = refl

∧-right-identity : RightIdentity true _∧_
∧-right-identity true = refl
∧-right-identity false = refl

∧-identity : Identity true _∧_
∧-identity = (∧-left-identity , ∧-right-identity)

∨-associative : Associative _∨_
∨-associative true true true = refl
∨-associative true true false = refl
∨-associative true false true = refl
∨-associative true false false = refl
∨-associative false true true = refl
∨-associative false true false = refl
∨-associative false false true = refl
∨-associative false false false = refl

∧-associative : Associative _∧_
∧-associative true true true = refl
∧-associative true true false = refl
∧-associative true false true = refl
∧-associative true false false = refl
∧-associative false true true = refl
∧-associative false true false = refl
∧-associative false false true = refl
∧-associative false false false = refl

