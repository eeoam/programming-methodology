# Progress report 3
The following is a progress report on learning compositionally correct software design using Agda.
Writing computer programs in a scientifically principled manner is
an exciting endeavour and I am looking forward to acquiring
new skills and producing high quality work.

I have decided to split the development into two modules - in addition to the existing module `boolean`,
there is now a module `metalanguage`. The latter module contains the language
I am using to reason about the booleans: theorems for →, ≈ (equality) and now ≃ (isomorphism).
I also proved that ≃ is an equivalence relation. 
While the proofs of reflexivity and symmetry were pretty automatic,
the proofs for transivity required me to add the following law
for equality proofs:

```agda
leibniz : ∀ {A B : Set} (f : A → B) {x y : A} → x ≈ y → f x ≈ f y
leibniz f refl = refl
```

It also proved helpful to define the following lemmas :


```agda
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
```

Back to the booleans - I showed the antisymmetry of implication and
proved the mutual inequality theorem.
```agda
⇒-antisym : ∀ (a b : 𝔹) → ⌈ a ⇒ b ⌋ → ⌈ b ⇒ a ⌋ → a ≈ b
⇒-antisym true true a⇒b b⇒a = refl
⇒-antisym false false a⇒b b⇒a = refl

mutual-inequality : ∀ (a b : 𝔹) → ⌈ a ≡ b ⌋ ≃ ⌈ a ⇒ b ⌋ × ⌈ b ⇒ a ⌋
mutual-inequality a b =
    record
        { to = mutual-inequalityr a b
        ; from = mutual-inequalityl a b
        ; from∘to = mutual-inequalitylr a b
        ; to∘from = mutual-inequalityrl a b
        }

mutual-inequalityl : ∀ (a b : 𝔹) → ⌈ a ⇒ b ⌋ × ⌈ b ⇒ a ⌋ → ⌈ a ≡ b ⌋
mutual-inequalityl true true (a⇒b , b⇒a) = refl
mutual-inequalityl false false (a⇒b , b⇒a) = refl

mutual-inequalityr : ∀ (a b : 𝔹) → ⌈ a ≡ b ⌋ → ⌈ a ⇒ b ⌋ × ⌈ b ⇒ a ⌋
mutual-inequalityr true true a≡b = refl , refl
mutual-inequalityr false false a≡b = refl , refl

mutual-inequalitylr : ∀ (a b : 𝔹) → (x : ⌈ a ≡ b ⌋) → mutual-inequalityl a b (mutual-inequalityr a b x) ≈ x
mutual-inequalitylr true true refl = refl
mutual-inequalitylr false false refl = refl

mutual-inequalityrl : ∀ (a b : 𝔹) → (y : ⌈ a ⇒ b ⌋ × ⌈ b ⇒ a ⌋) → mutual-inequalityr a b (mutual-inequalityl a b y) ≈ y
mutual-inequalityrl true true (refl , refl) = refl
mutual-inequalityrl false false (refl , refl) = refl
```

What I am finding using Agda is that simply being able state what the problem is at least half the battle.
Often it seems that in my head I know what the problem is but being forced to write down a formal
specification of the problem in Agda is a humbling way to recognise that this is not in fact the case.
Once the formal specification is obtained, arriving at a solution has tended to be straightforward.
With a proof assistant like Agda, programming really feels like a scientific activity,
an occupation where one is guided by sound principles!

The full code can be found [here](https://github.com/eeoam/programming-methodology).


