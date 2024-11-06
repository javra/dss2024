# Lean tutorial

This is the accompanying code for the invited lean tutorial held at DeFi Security Summit 2024 by Jakob von Raumer.

It an abridged version of a Lean introductory talk at VSTT 2024 held by Joachim Breitner and Sebastian Ullrich, the material of which can be found [here](https://github.com/leanprover/vstte2024).

## Synopsis

* `Syntax.lean` defines the syntax of a small imperative language and embeds it into Lean.
* `Eval.lean` defines an evaluation of the expressions of that language.
* `Optimize.lean` provides a very simple optimization on these expressions and proves that it is consistent with the evaluation.
* `BigStep.lean` defines a big step semantics for the language and proves some simple facts about it.

## Ideas for Exercises

* Add more expressiveness to the language: More operations, unary operations.
* Improve `optimize` to simplify `0 + x` to `x`, for example.
* Prove that `optimize` is idempotent: `e.optimize.optimize = e`.
* Add nice input syntax for `Env.get σ "x"` and `Env.set`, e.g. `σ[[x]]` and `σ[[x := e]]` and update some of the proof statements.
* Write an optimizer for `Stmt` which optimizes every expression.
* Verify more complex programs! 
Hint:

Rephrase statements so that the three arguments to `BigStep` are variables, so that `induction` works. You can do that using a helper theorem that you finally apply, or explore the `generalize` tactic.

