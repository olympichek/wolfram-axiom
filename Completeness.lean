import BooleanAxiom

/-! Equational completeness is proved by the quotient term algebra. -/
namespace SingleNand

/-- NAND terms with variables indexed by natural numbers. -/
inductive Term where
  | var : Nat → Term
  | nand : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Interpret a term in an arbitrary algebra. -/
def eval {α : Type u} (op : α → α → α) (env : Nat → α) : Term → α
  | var i => env i
  | nand s t => op (eval op env s) (eval op env t)

/-- Equational derivability from all substitution instances of the single
axiom, using only reflexivity, symmetry, transitivity, and congruence. -/
inductive Derives : Term → Term → Prop where
  | refl (t) : Derives t t
  | symm {s t} : Derives s t → Derives t s
  | trans {s t r} : Derives s t → Derives t r → Derives s r
  | congr {s t r q} : Derives s t → Derives r q → Derives (nand s r) (nand t q)
  | single (a b c) : Derives
      (nand (nand (nand a b) c) (nand a (nand (nand a c) a))) c

/-- Every equational derivation is valid in every model of the axiom. -/
theorem sound {α : Type u} (op : α → α → α) (W : Axiom op)
    (env : Nat → α) {s t : Term} (h : Derives s t) : eval op env s = eval op env t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ ih₁ ih₂ => exact congrArg₂ op ih₁ ih₂
  | single a b c => exact W (eval op env a) (eval op env b) (eval op env c)

/-- Substitution is admissible in this presentation of equational logic. -/
def subst (σ : Nat → Term) : Term → Term
  | var i => σ i
  | nand s t => nand (subst σ s) (subst σ t)

theorem Derives.subst {s t : Term} (h : Derives s t) (σ : Nat → Term) :
    Derives (s.subst σ) (t.subst σ) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr _ _ ih₁ ih₂ => exact .congr ih₁ ih₂
  | single a b c => exact .single (a.subst σ) (b.subst σ) (c.subst σ)

private def termSetoid : Setoid Term where
  r := Derives
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

private abbrev Free := Quotient termSetoid

private def freeOp : Free → Free → Free :=
  Quotient.map₂ nand (fun _ _ h _ _ k => Derives.congr h k)

private theorem freeAxiom : Axiom freeOp := by
  intro a b c
  induction a, b, c using Quotient.inductionOn₃ with
  | h a b c => exact Quotient.sound (Derives.single a b c)

private theorem eval_free (t : Term) :
    eval freeOp (fun i => Quotient.mk termSetoid (var i)) t = Quotient.mk termSetoid t := by
  induction t with
  | var i => rfl
  | nand s t ih₁ ih₂ =>
    change freeOp (eval freeOp _ s) (eval freeOp _ t) = _
    rw [ih₁, ih₂]
    rfl

/-- Validity in every Boolean algebra (including the one-element algebra). -/
def Valid (s t : Term) : Prop :=
  ∀ (α : Type) [BooleanAlgebra α] (env : Nat → α),
    eval (fun x y => (x ⊓ y)ᶜ) env s = eval (fun x y => (x ⊓ y)ᶜ) env t

/-- Every NAND identity valid in Boolean algebras has an equational proof
from the single axiom. -/
theorem complete {s t : Term} (h : Valid s t) : Derives s t := by
  let seed : Free := Quotient.mk termSetoid (var 0)
  letI : BooleanAlgebra Free := booleanAlgebra freeOp freeAxiom seed
  have hn : (fun x y : Free => (x ⊓ y)ᶜ) = freeOp := by
    funext x y
    exact booleanAlgebra_nand freeOp freeAxiom seed x y
  have he := h Free (fun i => Quotient.mk termSetoid (var i))
  rw [hn, eval_free, eval_free] at he
  exact Quotient.exact he

/-- The proposed equation is a complete axiom system for Boolean NAND. -/
theorem derives_iff_valid (s t : Term) : Derives s t ↔ Valid s t := by
  constructor
  · intro h α B env
    exact sound _ (boolean_nand_axiom (α := α)) env h
  · exact complete

end Term
end SingleNand
