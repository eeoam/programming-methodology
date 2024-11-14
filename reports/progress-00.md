# Progress report 0
The following is a progress report on learning compositionally correct software design using Agda.
Writing computer programs in a scientifically principled manner is
an exciting endeavour and I am looking forward to acquiring
new skills and producing high quality work.

I was looking at the `Data.Bool.*` modules that are part of the standard library,
and I noticed that there are a number of key boolean operators missing:
viz. implication, consequence, equivalence, inequivalence. (Actually the inequivalence
is in the standard library, but under the name xor.) 
I decided that a nice exercise would be to define the operators an
prove their properties.

Accordingly I have defined the following boolean operators:

- equivalence
- inequivalence
- implication
- consequence
- disjunction
- conjunction

Moreover, I have proved (interactively) in Agda the following:

- negation is involutive and its own inverse
- true and false are the identity elements of equivalence and inequivalence, respectively
- symmetry of equivalence and inequivalence
- associativity of equivalence and inequivalence
- true is left identity of implication
- true is right identity of consequence
- true is the right zero of implication
- true is the left zero of consequence
- idempotence of disjunction and conjunction
- symmetry of disjunction and conjunction

The code can be found [here](https://github.com/eeoam/programming-methodology/blob/master/boolean.lagda.md).

So far, all these proofs are by case analysis - 
I'd like to see how many of these proofs I can redo using equational reasoning.

Eric Macaulay
14 November 2024