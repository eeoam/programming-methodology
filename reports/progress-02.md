# Progress report 2
The following is a progress report on learning compositionally correct software design using Agda.
Writing computer programs in a scientifically principled manner is
an exciting endeavour and I am looking forward to acquiring
new skills and producing high quality work.

Having examined the connection between boolean equality and boolean equivalence,
it seemed natural to turn my attention to the relationship between
boolean implication and the function type. 
Hence the following definitions:
```agda
→-⇒ : ∀ (a b : 𝔹) → (⌈ a ⌋ → ⌈ b ⌋) → ⌈ a ⇒ b ⌋
→-⇒ true true f = refl
→-⇒ true false f = f refl
→-⇒ false true f = refl
→-⇒ false false f = refl

⇒-modus-ponens : ∀ (a b : 𝔹) → ⌈ a ⇒ b ⌋ → (⌈ a ⌋ → ⌈ b ⌋)
⇒-modus-ponens true true a⇒b a≈true = refl
```

It turned out to be a useful (and fun!) exercises to first prove the following theorems concerning → :
```agda
→-refl : ∀ {A : Set} → A → A

→-le : ∀ {A : Set} → ⊥ → A

→-ge : ∀{A : Set} → A → ⊤

→-modus-ponens : ∀ {A B : Set} → (A → B) → A → B

→-trans : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
```

Then I proved the corresponding ⇒ theorems:
```agda
⇒-refl : ∀ (a : 𝔹) → ⌈ a ⇒ a ⌋

⇒-le : ∀ (a : 𝔹) → ⌈ false ⇒ a ⌋

⇒-ge : ∀ (a : 𝔹) → ⌈ a ⇒ true ⌋

⇒-modus-ponens : ∀ (a b : 𝔹) → ⌈ a ⇒ b ⌋ → ⌈ a ⌋ → ⌈ b ⌋

⇒-trans : ∀ (a b c : 𝔹) → ⌈ a ⇒ b ⌋ → ⌈ b ⇒ c ⌋ → ⌈ a ⇒ c ⌋
```

I had thought I could prove all the above theorems with →-⇒, 
but I had to prove ⇒-modus-ponens from first principles. (Perhaps there is a way.)

The full code can be found [here](https://github.com/eeoam/programming-methodology/blob/master/boolean.lagda.md#implications-from-functions).


