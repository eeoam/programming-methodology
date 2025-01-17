
[Algebraic preliminaries](#some-algebraic-preliminaries)

[Equivalences from equalities](#equivalences-from-equalities)

[Implications from functions](#implications-from-functions)

# Some algebraic preliminaries.
```agda
module boolean where

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
```agda
data 𝔹 : Set where
    true  : 𝔹
    false : 𝔹
```

We will be working with the following boolean operators.
```agda
infix 6 _⇒_
infix 6 _⇐_
infix 5 _≡_
infix 5 _≢_
infix 7 _∧_
infix 7 _∨_

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

Let us first investigate the properties of ¬ .
```agda
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
```agda
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
```agda
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
```agda
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
```agda

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
```
# Equivalences from equalities
First a bit of notation.
```agda
⌈_⌋ : 𝔹 → Set
⌈ a ⌋ = a ≈ true
```

We can obtain boolean equivalences from boolean equalities on account of:
```agda
≈→≡ : ∀(a b : 𝔹) → a ≈ b → ⌈ a ≡ b ⌋
≈→≡ true true a≈b = refl
≈→≡ true false = λ ()
≈→≡ false false a≈b = refl
```

Let's see some of the new theorems `≈→≡` gives us.
```agda
¬-involutive' : ∀ (a : 𝔹) → ⌈ ¬ (¬ a) ≡ a ⌋
¬-involutive' a = ≈→≡ (¬(¬ a)) a (¬-involutive a)

¬-galois : ∀ (a b : 𝔹) → (¬ a ≡ b) ≈ (a ≡ ¬ b)
¬-galois true true = refl
¬-galois true false = refl
¬-galois false true = refl
¬-galois false false = refl

¬-galois' : ∀ (a b : 𝔹) → ⌈ (¬ a ≡ b) ≡ (a ≡ ¬ b) ⌋
¬-galois' a b = ≈→≡ (¬ a ≡ b) (a ≡ ¬ b) (¬-galois a b)
```

```agda
⇒-reflexive : ∀ (a : 𝔹) → a ⇒ a ≈ true
⇒-reflexive true = refl
⇒-reflexive false = refl

⇒-reflexive' : ∀ (a : 𝔹) → ⌈ a ⇒ a ≡ true ⌋
⇒-reflexive' a =  ≈→≡ (a ⇒ a) true (⇒-reflexive a)

⇒-left-identity' : ∀ (a : 𝔹) → ⌈ true ⇒ a ≡ a ⌋
⇒-left-identity' a = ≈→≡ (true ⇒ a) a (⇒-left-identity a)

⇒-right-zero' : ∀ (a : 𝔹) → ⌈ a ⇒ true ≡ true ⌋
⇒-right-zero' a = ≈→≡ (a ⇒ true) true (⇒-right-zero a)
```

```agda
⇐-reflexive : ∀ (a : 𝔹) → a ⇐ a ≈ true
⇐-reflexive true = refl
⇐-reflexive false = refl

⇐-reflexive' : ∀ (a : 𝔹) → ⌈ a ⇐ a ≡ true ⌋
⇐-reflexive' a = ≈→≡ (a ⇐ a) true (⇐-reflexive a)

⇐-right-identity' : ∀ (a : 𝔹) → ⌈ a ⇐ true ≡ a ⌋
⇐-right-identity' a = ≈→≡ (a ⇐ true) a (⇐-right-identity a)

⇐-left-zero' : ∀ (a : 𝔹) → ⌈ true ⇐ a ≡ true ⌋
⇐-left-zero' a = ≈→≡ (true ⇐ a) true (⇐-left-zero a)
```

```agda
≡-reflexive' : ∀ (a : 𝔹) → a ≡ a ≈ true
≡-reflexive' a = ≈→≡ a a refl

≡-left-identity' : ∀ (a : 𝔹) → (true ≡ a) ≡ a ≈ true
≡-left-identity' a = ≈→≡ (true ≡ a) a (≡-left-identity a)

≡-right-identity' : ∀ (a : 𝔹) → (a ≡ true) ≡ a ≈ true
≡-right-identity' a = ≈→≡ (a ≡ true) a (≡-right-identity a)

≡-identity' : ∀ (a : 𝔹) → ((true ≡ a) ≡ a ≈ true) × ((a ≡ true) ≡ a ≈ true)
≡-identity' a = (≡-left-identity' a , ≡-right-identity' a)

≡-symmetric' : ∀ (a b : 𝔹) → (a ≡ b) ≡ (b ≡ a) ≈ true
≡-symmetric' a b = ≈→≡ (a ≡ b) (b ≡ a) (≡-symmetric a b)

≡-associative' : ∀ (a b c : 𝔹) → ((a ≡ b) ≡ c) ≡ (a ≡ (b ≡ c)) ≈ true
≡-associative' a b c = ≈→≡ ((a ≡ b) ≡ c) (a ≡ (b ≡ c)) (≡-associative a b c)
```

```agda 
≢-irreflexive : ∀ (a : 𝔹) → a ≢ a ≈ false
≢-irreflexive true = refl
≢-irreflexive false = refl

≢-left-identity' : ∀ (a : 𝔹) → (false ≢ a) ≡ a ≈ true
≢-left-identity' a = ≈→≡ (false ≢ a) a (≢-left-identity a)

≢-right-identity' : ∀ (a : 𝔹) → (a ≢ false) ≡ a ≈ true
≢-right-identity' a = ≈→≡ (a ≢ false) a (≢-right-identity a)

≢-identity' : ∀ (a : 𝔹) → ((false ≢ a) ≡ a ≈ true) × ((a ≢ false) ≡ a ≈ true)
≢-identity' a = (≢-left-identity' a , ≢-right-identity' a)

≢-symmetric' : ∀ (a b : 𝔹) → (a ≢ b) ≡ (b ≢ a) ≈ true
≢-symmetric' a b = ≈→≡ (a ≢ b) (b ≢ a) (≢-symmetric a b)

≢-associative' : ∀ (a b c : 𝔹) → ((a ≢ b) ≢ c) ≡ (a ≢ (b ≢ c)) ≈ true
≢-associative' a b c = ≈→≡ ((a ≢ b) ≢ c) (a ≢ (b ≢ c)) (≢-associative a b c)
```

```agda
∨-idempotent' : ∀ (a : 𝔹) → ⌈ a ∨ a ≡ a ⌋
∨-idempotent' a = ≈→≡ (a ∨ a) a (∨-idempotence a)

∨-left-identity' : ∀ (a : 𝔹) → ⌈ false ∨ a ≡ a ⌋
∨-left-identity' a = ≈→≡ (false ∨ a) a (∨-left-identity a)

∨-right-identity' : ∀ (a : 𝔹) → ⌈ a ∨ false ≡ a ⌋
∨-right-identity' a = ≈→≡ (a ∨ false) a (∨-right-identity a)

∨-identity' : ∀ (a : 𝔹) → ⌈ false ∨ a ≡ a ⌋ × ⌈ a ∨ false ≡ a ⌋
∨-identity' a = (∨-left-identity' a , ∨-right-identity' a)

∨-symmetric' : ∀ (a b : 𝔹) → ⌈ a ∨ b ≡ b ∨ a ⌋
∨-symmetric' a b = ≈→≡ (a ∨ b) (b ∨ a) (∨-symmetric a b)

∨-associative' : ∀ (a b c : 𝔹) → ⌈ (a ∨ b) ∨ c ≡ a ∨ (b ∨ c) ⌋
∨-associative' a b c = ≈→≡ ((a ∨ b) ∨ c ) (a ∨ (b ∨ c)) (∨-associative a b c)
```

```agda
∧-idempotent' : ∀ (a : 𝔹) → ⌈ a ∨ a ≡ a ⌋
∧-idempotent' a = ≈→≡ (a ∨ a) a (∨-idempotence a)

∧-left-identity' : ∀ (a : 𝔹) → ⌈ true ∧ a ≡ a ⌋
∧-left-identity' a = ≈→≡ (true ∧ a) a (∧-left-identity a)

∧-right-identity' : ∀ (a : 𝔹) → ⌈ a ∧ true ≡ a ⌋
∧-right-identity' a = ≈→≡ (a ∧ true) a (∧-right-identity a)

∧-identity' : ∀ (a : 𝔹) → ⌈ true ∧ a ≡ a ⌋ × ⌈ a ∧ true ≡ a ⌋
∧-identity' a = (∧-left-identity' a , ∧-right-identity' a)

∧-symmetric' : ∀ (a b : 𝔹) → ⌈ a ∧ b ≡ b ∧ a ⌋
∧-symmetric' a b = ≈→≡ (a ∧ b) (b ∧ a) (∧-symmetric a b)

∧-associative' : ∀ (a b c : 𝔹) → ⌈ (a ∧ b) ∧ c ≡ a ∧ (b ∧ c) ⌋
∧-associative' a b c = ≈→≡ ((a ∧ b) ∧ c) (a ∧ (b ∧ c)) (∧-associative a b c)
```

# Implications from functions
```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)

→-refl : ∀ {A : Set} → A → A
→-refl = λ x → x 

→-le : ∀ {A : Set} → ⊥ → A
→-le = λ ()

→-ge : ∀{A : Set} → A → ⊤
→-ge = λ _ → tt

→-modus-ponens : ∀ {A B : Set} → (A → B) → A → B
→-modus-ponens f a = f a

→-trans : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
→-trans A→B B→C = B→C ∘ A→B

infix 3 _□
_□ : ∀ (A : Set) → A → A
A □ = →-refl

infixr 2 _→⟨⟩_
_→⟨⟩_ : ∀ (A : Set){B : Set} → (A → B) → (A → B)
A →⟨⟩ A→B = A→B

infixr 2 _→⟨_⟩_
_→⟨_⟩_ : ∀(A : Set){B C : Set} → (A → B) → (B → C) → (A → C)
A →⟨ A→B ⟩ B→C = →-trans A→B B→C

→-⇒ : ∀ (a b : 𝔹) → (⌈ a ⌋ → ⌈ b ⌋) → ⌈ a ⇒ b ⌋
→-⇒ true true f = refl
→-⇒ true false f = f refl
→-⇒ false true f = refl
→-⇒ false false f = refl

⇒-refl : ∀ (a : 𝔹) → ⌈ a ⇒ a ⌋
⇒-refl a = →-⇒ a a (λ z → z)

⇒-le : ∀ (a : 𝔹) → ⌈ false ⇒ a ⌋
⇒-le a = →-⇒ false a (λ ())

⇒-ge : ∀ (a : 𝔹) → ⌈ a ⇒ true ⌋
⇒-ge a = →-⇒ a true (λ _ → refl)

⇒-modus-ponens : ∀ (a b : 𝔹) → ⌈ a ⇒ b ⌋ → ⌈ a ⌋ → ⌈ b ⌋
⇒-modus-ponens true true a⇒b a≈true = refl

⇒-trans : ∀ (a b c : 𝔹) → ⌈ a ⇒ b ⌋ → ⌈ b ⇒ c ⌋ → ⌈ a ⇒ c ⌋
⇒-trans a b c a⇒b b⇒c = →-⇒ a c (g ∘ f)
    where
        f : ⌈ a ⌋ → ⌈ b ⌋
        f = ⇒-modus-ponens a b a⇒b

        g : ⌈ b ⌋ → ⌈ c ⌋
        g = ⇒-modus-ponens b c b⇒c
```

→        (\r)


←        (\l)

λ U+03BB (\Gl)

∘ U+2218 (\o)

□ U+25A1