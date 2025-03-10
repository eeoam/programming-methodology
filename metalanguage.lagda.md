# Functions
```agda
module metalanguage where
    
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
```

```agda
_←_ : ∀ (A B : Set) → Set
A ← B = B → A

←-refl : ∀ {A : Set} → (A ← A)
←-refl = →-refl

←-le : ∀ {A : Set} → (⊤ ← A)
←-le = →-ge

←-ge : ∀ {A : Set} → (A ← ⊥)
←-ge = →-le

←-modus-ponens : ∀ {A B : Set} → (A ← B) → B → A
←-modus-ponens = →-modus-ponens

←-trans : ∀ {A B C : Set} → (A ← B) → (B ← C) → (A ← C)
←-trans A←B B←C = A←B ∘ B←C 
```

# Equality
```agda
data _≈_ {A : Set} (x : A) : A → Set where
    refl : x ≈ x
infix 4 _≈_

pattern erefl x = refl {x = x}

trans : ∀ {A : Set} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
trans refl refl = refl

module ≈-Reasoning {A : Set} where
    infixr 2 _≈⟨_⟩_
    infix 3 _∎

    _∎ : ∀ (x : A) → x ≈ x
    x ∎ = erefl x

    _≈⟨_⟩_ : ∀(x : A) {y z : A} → x ≈ y → y ≈ z → x ≈ z
    x ≈⟨ x≈y ⟩ y≈z = trans x≈y y≈z

open ≈-Reasoning

leibniz : ∀ {A B : Set} (f : A → B) {x y : A} → x ≈ y → f x ≈ f y
leibniz f refl = refl
```

# Isomorphism
```agda
infix 0 _≃_
record _≃_ (A B : Set) : Set where
    field
        to : A → B
        from : B → A
        from∘to : ∀ (x : A) → from (to x) ≈ x
        to∘from : ∀ (y : B) → to (from y) ≈ y
open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl = 
    record { to = λ z → z
           ; from = λ z → z
           ; from∘to = λ x → refl
           ; to∘from = λ y → refl 
           }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
    record
        { to = from A≃B
        ; from = to A≃B
        ; from∘to = to∘from A≃B
        ; to∘from = from∘to A≃B
        }

≃-trans-from∘to : ∀ {A B C : Set} → (A≃B : A ≃ B) → (B≃C : B ≃ C) → (x : A) → from A≃B (from B≃C (to B≃C (to A≃B x))) ≈ x
≃-trans-from∘to A≃B B≃C x = 
    from A≃B (from B≃C (to B≃C (to A≃B x)))
    ≈⟨ leibniz (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
    from A≃B (to A≃B x)
    ≈⟨ from∘to A≃B x ⟩
    x ∎

≃-trans-to∘from : ∀ {A B C : Set} → (A≃B : A ≃ B) → (B≃C : B ≃ C) → (y : C) → to B≃C (to A≃B (from A≃B (from B≃C y))) ≈ y
≃-trans-to∘from A≃B B≃C y =
    to B≃C (to A≃B (from A≃B (from B≃C y)) )
    ≈⟨ leibniz (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
    to B≃C (from B≃C y)
    ≈⟨ to∘from B≃C y ⟩
    y ∎

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
    record
        { to = λ z → to B≃C (to A≃B z)
        ; from = λ z → from A≃B (from B≃C z)
        ; from∘to = ≃-trans-from∘to A≃B B≃C
        ; to∘from  = ≃-trans-to∘from A≃B B≃C
        }
```