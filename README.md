# A single NAND axiom for Boolean algebra

[![Lean CI](https://github.com/olympichek/wolfram-axiom/actions/workflows/lean.yml/badge.svg)](https://github.com/olympichek/wolfram-axiom/actions/workflows/lean.yml)

A Lean 4 formalization of the theorem that

```text
((a ⋆ b) ⋆ c) ⋆ (a ⋆ ((a ⋆ c) ⋆ a)) = c
```

is a complete equational axiom system for Boolean algebra in the NAND language. The construction produces mathlib's standard [BooleanAlgebra](https://github.com/leanprover-community/mathlib4/blob/v4.29.1/Mathlib/Order/BooleanAlgebra/Defs.lean#L103), and the converse uses that same typeclass.

## Origin and exposition

The proof presented here was found by **GPT-6 Astra Pro**. It was then formalized in Lean by **GPT-6 Astra / Codex**.

The theorem already had a proof found using automated theorem proving software. Stephen Wolfram discusses that proof and the challenge of understanding it in [“Who Can Understand the Proof? A Window on Formalized Mathematics”](https://writings.stephenwolfram.com/2025/01/who-can-understand-the-proof-a-window-on-formalized-mathematics/). That proof derives the standard Sheffer axioms and already identifies commutativity as a pivotal intermediate result. The exposition here gives explicit substitutions for the algebraic lemmas and a self-contained order-theoretic construction of the Boolean lattice, and might be easier to follow.

[**Read the exposition (PDF)**](proof.pdf) for a human-readable presentation of the algebraic lemma, the Boolean algebra construction, and equational completeness.

## Main results

- [SingleNand.axiom_iff_booleanAlgebra](BooleanAxiom.lean#L295): on any nonempty type, an operation satisfies the single axiom if and only if it is NAND for a mathlib Boolean algebra structure on that type.
- [SingleNand.booleanAlgebra](BooleanAxiom.lean#L246): constructs that structure from the axiom and a chosen element of the carrier.
- [SingleNand.booleanAlgebra_nand](BooleanAxiom.lean#L260): the constructed structure's NAND is the original operation.
- [SingleNand.Term.derives_iff_valid](Completeness.lean#L94): a NAND identity is derivable from the axiom if and only if it holds in every Boolean algebra.

The reconstructed operations are

```text
¬x    = x ⋆ x
x ∧ y = (x ⋆ y) ⋆ (x ⋆ y)
x ∨ y = (x ⋆ x) ⋆ (y ⋆ y)
⊤     = x ⋆ (x ⋆ x)
⊥     = ⊤ ⋆ ⊤
```

[top_independent](BooleanAxiom.lean#L48) proves that the expression for `⊤` is independent of `x`. The model characterization is universe-polymorphic. The equational-completeness statement uses terms with natural-number variables and quantifies over Boolean algebras in `Type`; the [soundness lemma](Completeness.lean#L30) also applies in arbitrary universes.

Nonemptiness is necessary: the equation holds vacuously on the empty type, which cannot have Boolean constants. The one-element Boolean algebra is included; no assumption that `⊥ ≠ ⊤` is made.

## Proof organization

[NandEquations.lean](NandEquations.lean) derives double negation, commutativity, and the three auxiliary identities from the single axiom by explicit equality rewrites. It imports only Lean.

[BooleanAxiom.lean](BooleanAxiom.lean) follows the order construction in the proof: define `x ≤ y` by `x ⋆ y = x ⋆ x`, prove the universal properties of meet and join, and derive distributivity from the splitting identity. The proof constructs mathlib's [Lattice](https://github.com/leanprover-community/mathlib4/blob/v4.29.1/Mathlib/Order/Lattice.lean#L342) directly, adds bounds, and proves the distributivity and complement laws to obtain [BooleanAlgebra](https://github.com/leanprover-community/mathlib4/blob/v4.29.1/Mathlib/Order/BooleanAlgebra/Defs.lean#L103). The file also proves the converse.

[Completeness.lean](Completeness.lean) defines NAND terms and an inductive relation of equational derivability. Its rules are reflexivity, symmetry, transitivity, congruence, and all substitution instances of the single axiom. General substitution is proved admissible. The quotient of terms by derivability satisfies the axiom, so the Boolean algebra construction applies to it. Evaluating an identity in this quotient proves the completeness direction. Thus equational completeness is itself formalized, rather than assumed as a metatheorem.

[Verification.lean](Verification.lean) prints the axiom dependencies of the main results, checks the two-element and one-element models, and demonstrates deriving commutativity through the completeness theorem.

## Build

[GitHub Actions](.github/workflows/lean.yml) compiles all four Lean files, including the verification examples and axiom dependency output, on pushes and pull requests to `main`. The build treats warnings as errors.

The project pins Lean and mathlib to **v4.29.1**, with exact dependency revisions recorded in [lake-manifest.json](lake-manifest.json).

From this directory:

```sh
lake exe cache get Mathlib/Order/BooleanAlgebra/Basic.lean
lake build
```

The build includes all four Lean files and the dependency audit. There are no `sorry`, `admit`, or additional axiom declarations. Double negation and commutativity have no axiom dependencies. The final characterization and completeness theorems use only Lean's standard [propext](https://github.com/leanprover/lean4/blob/v4.29.1/src/Init/Core.lean#L1591), [Classical.choice](https://github.com/leanprover/lean4/blob/v4.29.1/src/Init/Prelude.lean#L795), and [Quot.sound](https://github.com/leanprover/lean4/blob/v4.29.1/src/Init/Core.lean#L1787).

To use the construction in another file:

```lean
import Completeness

example {α : Type} (op : α → α → α)
    (h : SingleNand.Axiom op) (seed x y : α) :
    letI := SingleNand.booleanAlgebra op h seed
    (x ⊓ y)ᶜ = op x y :=
  SingleNand.booleanAlgebra_nand op h seed x y
```
