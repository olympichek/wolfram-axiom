# A single NAND axiom for Boolean algebra

[![Lean CI](https://github.com/olympichek/wolfram-axiom/actions/workflows/lean.yml/badge.svg)](https://github.com/olympichek/wolfram-axiom/actions/workflows/lean.yml)

This repository contains a proof, checked in Lean, that the single equation

```text
((a ⋆ b) ⋆ c) ⋆ (a ⋆ ((a ⋆ c) ⋆ a)) = c
```

suffices to recover Boolean algebra. We start with an arbitrary binary operation `⋆` and derive the Boolean laws from this equation alone.

[**Read the exposition (PDF)**](proof/proof.pdf) for the mathematical argument.

## Origin

The proof presented here was found by **GPT-6 Astra Pro** and formalized in Lean by **GPT-6 Astra / Codex**.

An earlier proof was found using automated theorem proving software. Stephen Wolfram discusses it and the challenge of understanding it in [“Who Can Understand the Proof? A Window on Formalized Mathematics”](https://writings.stephenwolfram.com/2025/01/who-can-understand-the-proof-a-window-on-formalized-mathematics/). The proof presented here might be easier to follow.

## What is proved

- [Boolean algebra characterization](lean/BooleanAxiom.lean#L295): a binary operation on a nonempty set satisfies the equation if and only if it is NAND—negated AND—for a Boolean algebra structure on that set.
- [Completeness](lean/Completeness.lean#L94): an identity in the NAND language holds in every Boolean algebra if and only if it can be derived from the single equation by equational reasoning.

The familiar Boolean operations are recovered as follows:

```text
¬x    = x ⋆ x
x ∧ y = (x ⋆ y) ⋆ (x ⋆ y)
x ∨ y = (x ⋆ x) ⋆ (y ⋆ y)
⊤     = x ⋆ (x ⋆ x)
⊥     = ⊤ ⋆ ⊤
```

The expression defining `⊤` has the same value for every `x`. The theorem assumes a nonempty set and includes the one-element Boolean algebra.

## Proof files

- [NandEquations.lean](lean/NandEquations.lean) derives double negation, commutativity, and the auxiliary identities by substitution and rewriting.
- [BooleanAxiom.lean](lean/BooleanAxiom.lean) constructs the Boolean algebra using an order-theoretic argument and proves the converse.
- [Completeness.lean](lean/Completeness.lean) proves equational completeness using the algebra of terms modulo derivability.
- [Verification.lean](lean/Verification.lean) checks examples and reports which foundational axioms the proofs use.

## Build

The project uses Lean and mathlib **v4.29.1**. From the repository root:

```sh
cd lean
lake exe cache get Mathlib.Order.BooleanAlgebra.Basic
lake build
```

The proof is fully checked in Lean, with no unfinished proofs or axioms beyond Lean's standard foundations.
