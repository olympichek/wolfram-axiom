import Completeness

/-! Check the final theorem's dependencies and its use on concrete carriers. -/
#print axioms SingleNand.double_neg
#print axioms SingleNand.comm
#print axioms SingleNand.axiom_iff_booleanAlgebra
#print axioms SingleNand.Term.complete
#print axioms SingleNand.Term.derives_iff_valid

example : SingleNand.Axiom (fun x y : Bool => (x ⊓ y)ᶜ) :=
  SingleNand.boolean_nand_axiom

example : SingleNand.Axiom (fun x y : PUnit => (x ⊓ y)ᶜ) :=
  SingleNand.boolean_nand_axiom

open SingleNand.Term in
example : Derives (nand (var 0) (var 1)) (nand (var 1) (var 0)) := by
  apply complete
  intro α B env
  simp only [eval, inf_comm]
