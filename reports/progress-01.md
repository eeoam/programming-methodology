# Progress report 1
The following is a progress report on learning compositionally correct software design using Agda.
Writing computer programs in a scientifically principled manner is
an exciting endeavour and I am looking forward to acquiring
new skills and producing high quality work.

I have been exploring the connection between boolean equality and boolean equivalence, 
viz. that $$a = b\text{\quad if and only if}\quad (a\equiv b)\ = \textbf{true}$$

This has led me to the definition of the following operator on Agda:
```agda
≈→≡ : ∀(a b : 𝔹) → a ≈ b → ⌈ a ≡ b ⌋
≈→≡ true true a≈b = refl
≈→≡ true false = λ ()
≈→≡ false false a≈b = refl
```

Armed with `≈→≡` I have restated many of the equalities for negation, implication, conjunction etc.
as equivalences. The corresponding Agda proofs can be found [here](https://github.com/eeoam/programming-methodology/blob/b729eff7eb668e5fbaa6d78e93787c705189aee2/boolean.lagda.md?plain=1#L283). 

In the process of proving equivalences, I found it necessary to add some new equality theorems viz.
```agda
¬-galois : ∀ (a b : 𝔹) → (¬ a ≡ b) ≈ (a ≡ ¬ b)

⇒-reflexive : ∀ (a : 𝔹) → a ⇒ a ≈ true

⇐-reflexive : ∀ (a : 𝔹) → a ⇐ a ≈ true

≢-irreflexive : ∀ (a : 𝔹) → a ≢ a ≈ false
```

Interestingly, unlike with the equality proofs, I found it easier to write the equivalence proofs "non-interactively"
i.e. I would write the full function definition and then just hit C-c C-l to ensure that everything was ok.


The full code can be found [here](https://github.com/eeoam/programming-methodology/blob/master/boolean.lagda.md).

I wish you a Merry Christmas and a Happy New Year!


Eric Macaulay
23 December 2024