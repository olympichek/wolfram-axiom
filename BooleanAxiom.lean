import NandEquations
import Mathlib.Order.BooleanAlgebra.Basic

namespace SingleNand

universe u

section Recovery
variable {α : Type u} (op : α → α → α) (W : Axiom op)
local infixl:70 " ⋆ " => op
local notation "n" => fun x => x ⋆ x
include W

private theorem nn (x : α) : n (n x) = x := double_neg op W x

private theorem B (x y : α) : x ⋆ (x ⋆ y) = x ⋆ n y := by
  have aux (a b : α) : a ⋆ (b ⋆ (a ⋆ b)) = n a := by
    have h := J op W a (a ⋆ b) b
    have hs := S op W b a (a ⋆ b)
    rw [comm op W b a] at hs
    rw [comm op W (a ⋆ b) b] at h
    rw [hs] at h
    exact h.symm
  have h := J op W x y x
  rw [aux y x] at h
  rw [comm op W y x] at h
  exact h.symm

private theorem I' (x y : α) : x ⋆ (n x ⋆ y) = n x := by
  simpa only [nn op W] using I op W (n x) y

private theorem A (x y : α) : x ⋆ n (x ⋆ y) = x ⋆ y := by
  have h := I op W (x ⋆ y) (n x)
  rw [comm op W (x ⋆ y) (n x), I op W] at h
  rwa [comm op W] at h

private theorem e_product (x y : α) : x ⋆ n x = (x ⋆ y) ⋆ n (x ⋆ y) := by
  calc
    x ⋆ n x = n x ⋆ x := comm op W _ _
    _ = n x ⋆ (n x ⋆ (x ⋆ y)) := congrArg (op (n x)) (I op W x y).symm
    _ = n x ⋆ n (x ⋆ y) := B op W _ _
    _ = n (x ⋆ y) ⋆ (n (x ⋆ y) ⋆ x) := by
      rw [B op W, comm op W]
    _ = n (x ⋆ y) ⋆ (x ⋆ y) := by rw [comm op W (n (x ⋆ y)) x, A op W]
    _ = (x ⋆ y) ⋆ n (x ⋆ y) := comm op W _ _

/-- The expression defining the greatest element is independent of its argument. -/
theorem top_independent (x y : α) : x ⋆ (x ⋆ x) = y ⋆ (y ⋆ y) := by
  rw [e_product op W x y, e_product op W y x, comm op W y x]

variable (seed : α)
private def one := seed ⋆ (seed ⋆ seed)
private def zero := one op seed ⋆ one op seed

private theorem e_one (x : α) : x ⋆ n x = one op seed := top_independent op W x seed

private theorem mul_one (x : α) : x ⋆ one op seed = n x := by
  rw [← e_one op W seed x, B op W, nn op W]

private theorem one_mul (x : α) : one op seed ⋆ x = n x := by
  rw [comm op W, mul_one op W]

private theorem zero_mul (x : α) : zero op seed ⋆ x = one op seed := by
  have h := I op W (one op seed) (n x)
  rw [one_mul op W seed (n x), nn op W] at h
  exact h

private def order (x y : α) : Prop := x ⋆ y = n x

omit W in
private theorem order_refl (x : α) : order op x x := rfl

private theorem neg_inj {x y : α} (h : n x = n y) : x = y := by
  have h' := congrArg n h
  simpa only [nn op W] using h'

private theorem order_antisymm {x y : α} (h : order op x y) (k : order op y x) : x = y := by
  apply neg_inj op W
  exact h.symm.trans ((comm op W x y).trans k)

private theorem order_iff (x y : α) : order op x y ↔ x ⋆ n y = one op seed := by
  constructor
  · intro h
    rw [← B op W, h, e_one op W seed]
  · intro h
    have h' := B op W x (n y)
    rw [nn op W, h, mul_one op W] at h'
    exact h'.symm

private theorem order_trans (seed : α) {x y z : α} (h : order op x y) (k : order op y z) :
    order op x z := by
  have h₁ : y ⋆ x = n x := (comm op W y x).trans h
  have h₂ := (order_iff op W seed y z).mp k
  have h₃ := S op W y (n z) x
  rw [h₂, h₁, one_mul op W] at h₃
  have h₄ : n x ⋆ n z = z := by
    apply neg_inj op W
    rwa [comm op W (n x) (n z)]
  have h₅ := I' op W x (n z)
  rwa [h₄] at h₅

private theorem order_neg {x y : α} (h : order op x y) : order op (n y) (n x) := by
  change n y ⋆ n x = n (n y)
  rw [nn op W, ← h, comm op W x y, I op W]

private theorem meet_lower (x y : α) : order op (n (x ⋆ y)) x := by
  change n (x ⋆ y) ⋆ x = n (n (x ⋆ y))
  rw [nn op W, comm op W, A op W]

private theorem meet_greatest {z a b : α} (ha : order op z a) (hb : order op z b) :
    order op z (n (a ⋆ b)) := by
  let k := n z
  let p := a ⋆ b
  let h := k ⋆ p
  have ha' : a ⋆ z = k := (comm op W a z).trans ha
  have hb' : b ⋆ z = k := (comm op W b z).trans hb
  have fa (t : α) : (t ⋆ a) ⋆ (t ⋆ k) = t := by
    have ht := S op W a t z
    rwa [ha', comm op W a t] at ht
  have fb (t : α) : (t ⋆ b) ⋆ (t ⋆ k) = t := by
    have ht := S op W b t z
    rwa [hb', comm op W b t] at ht
  have hp : p ⋆ (a ⋆ k) = a := fb a
  have hh : h ⋆ a = p := by
    have ht := S op W k p a
    rw [comm op W k a, hp] at ht
    exact ht
  have hn : h = n p := by
    calc
      h = (h ⋆ a) ⋆ (h ⋆ k) := (fa h).symm
      _ = p ⋆ (k ⋆ (k ⋆ p)) := by rw [hh, comm op W h k]
      _ = p ⋆ (k ⋆ n p) := by rw [B op W]
      _ = p ⋆ (n p ⋆ k) := by rw [comm op W k (n p)]
      _ = n p := I' op W p k
  have hi := I op W k p
  change n (n z) ⋆ h = n z at hi
  rw [nn op W, hn] at hi
  exact hi

/-- The derived meet and join form a lattice in mathlib's hierarchy. -/
@[implicit_reducible]
private def lattice : Lattice α where
  le := order op
  inf x y := n (x ⋆ y)
  sup x y := n x ⋆ n y
  le_refl := order_refl op
  le_trans _ _ _ := order_trans op W seed
  le_antisymm _ _ := order_antisymm op W
  inf_le_left := meet_lower op W
  inf_le_right x y := by rw [comm op W x y]; exact meet_lower op W y x
  le_inf _ _ _ := meet_greatest op W
  le_sup_left x y := by
    have h := order_neg op W (meet_lower op W (n x) (n y))
    simpa only [nn op W] using h
  le_sup_right x y := by
    have h := order_neg op W (meet_lower op W (n y) (n x))
    simpa only [nn op W, comm op W (n y) (n x)] using h
  sup_le := by
    intro a b c ha hb
    have h := order_neg op W (meet_greatest op W (order_neg op W ha) (order_neg op W hb))
    simpa only [nn op W] using h

@[implicit_reducible]
private def boundedOrder : letI := lattice op W seed; BoundedOrder α := by
  letI := lattice op W seed
  exact
    { bot := zero op seed
      top := one op seed
      bot_le := fun x => by
        change zero op seed ⋆ x = n (n (one op seed))
        rw [zero_mul op W, nn op W]
      le_top := mul_one op W seed }

private theorem meet_compl (x : α) :
    letI := lattice op W seed
    x ⊓ n x = zero op seed := by
  change n (x ⋆ n x) = n (one op seed)
  rw [e_one op W seed]

private theorem join_compl (x : α) :
    letI := lattice op W seed
    x ⊔ n x = one op seed := by
  change n x ⋆ n (n x) = one op seed
  rw [nn op W, comm op W, e_one op W seed]

private theorem split (c a : α) :
    letI := lattice op W seed
    (c ⊓ a) ⊔ (c ⊓ n a) = c := by
  change n (n (c ⋆ a)) ⋆ n (n (c ⋆ n a)) = c
  rw [nn op W, nn op W, comm op W c a]
  exact S op W a c a

private theorem orthogonal_iff (x y : α) :
    letI := lattice op W seed
    x ≤ y ↔ x ⊓ n y = zero op seed := by
  letI := lattice op W seed
  letI := boundedOrder op W seed
  constructor
  · intro h
    apply bot_unique
    have hm := inf_le_inf h (le_refl (n y))
    rwa [meet_compl op W seed] at hm
  · intro h
    have hs := split op W seed x y
    change x ⊓ n y = ⊥ at h
    rw [h, sup_bot_eq] at hs
    rw [← hs]
    exact inf_le_right

private theorem distributive (x y z : α) :
    letI := lattice op W seed
    x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  letI := lattice op W seed
  letI := boundedOrder op W seed
  let t := x ⊓ (y ⊔ z)
  let d := (x ⊓ y) ⊔ (x ⊓ z)
  let r := t ⊓ n d
  have rx : r ≤ x := le_trans inf_le_left inf_le_left
  have rd : r ≤ n d := inf_le_right
  have rn (v : α) (hv : x ⊓ v ≤ d) : r ≤ n v := by
    have h₁ : r ≤ n (x ⊓ v) := le_trans rd (order_neg op W hv)
    have h₂ : r ⊓ v ≤ x ⊓ v := inf_le_inf rx (le_refl v)
    have h₃ : r ⊓ v ≤ n (x ⊓ v) := le_trans inf_le_left h₁
    have h₄ : r ⊓ v = ⊥ := by
      apply bot_unique
      have h := le_inf h₂ h₃
      rwa [meet_compl op W seed] at h
    apply (orthogonal_iff op W seed r (n v)).mpr
    simpa only [nn op W] using h₄
  have ry := rn y le_sup_left
  have rz := rn z le_sup_right
  have hneg : r ≤ n (y ⊔ z) := le_inf ry rz
  have hpos : r ≤ y ⊔ z := le_trans inf_le_left inf_le_right
  have rzero : r = ⊥ := by
    apply bot_unique
    have h := le_inf hpos hneg
    rwa [meet_compl op W seed] at h
  apply le_antisymm
  · exact (orthogonal_iff op W seed t d).mpr rzero
  · exact sup_le (inf_le_inf_left x le_sup_left) (inf_le_inf_left x le_sup_right)

end Recovery

/-- The recovered operations packaged as mathlib's standard Boolean algebra. -/
@[implicit_reducible]
def booleanAlgebra {α : Type u} (op : α → α → α) (W : Axiom op) (seed : α) :
    BooleanAlgebra α := by
  letI := lattice op W seed
  letI := boundedOrder op W seed
  letI : DistribLattice α := DistribLattice.ofInfSupLe fun a b c =>
    le_of_eq (distributive op W seed a b c)
  exact
    { compl := fun x => op x x
      inf_compl_le_bot := fun a => le_of_eq (meet_compl op W seed a)
      top_le_sup_compl := fun a => le_of_eq (join_compl op W seed a).symm
      le_top := fun _ => le_top
      bot_le := fun _ => bot_le }

/-- NAND in the mathlib structure is the operation we started with. -/
theorem booleanAlgebra_nand {α : Type u} (op : α → α → α) (W : Axiom op)
    (seed x y : α) :
    letI := booleanAlgebra op W seed
    (x ⊓ y)ᶜ = op x y :=
  double_neg op W (op x y)

/-- The complement and lattice operations are the advertised NAND terms. -/
theorem booleanAlgebra_operations {α : Type u} (op : α → α → α) (W : Axiom op)
    (seed x y : α) :
    letI := booleanAlgebra op W seed
    xᶜ = op x x ∧ x ⊓ y = op (op x y) (op x y) ∧
      x ⊔ y = op (op x x) (op y y) := ⟨rfl, rfl, rfl⟩

/-- The greatest element can be expressed using any element of the carrier. -/
theorem booleanAlgebra_top {α : Type u} (op : α → α → α) (W : Axiom op)
    (seed x : α) :
    letI := booleanAlgebra op W seed
    (⊤ : α) = op x (op x x) := top_independent op W seed x

/-- The least element is the NAND square of the greatest element. -/
theorem booleanAlgebra_bot {α : Type u} (op : α → α → α) (W : Axiom op)
    (seed : α) :
    letI := booleanAlgebra op W seed
    (⊥ : α) = op ⊤ ⊤ := rfl

/-- Every Boolean algebra satisfies the single identity with NAND as its operation. -/
theorem boolean_nand_axiom {α : Type u} [BooleanAlgebra α] :
    Axiom (fun x y : α => (x ⊓ y)ᶜ) := by
  intro a b c
  simp only [compl_inf, compl_sup, compl_compl]
  simp [inf_sup_left, inf_comm]
  rw [sup_right_comm, inf_comm a c, ← inf_sup_left,
    compl_sup_eq_top, inf_top_eq, sup_inf_self]

/-- Model-theoretic characterization on any nonempty carrier. -/
theorem axiom_iff_booleanAlgebra {α : Type u} [Nonempty α] (op : α → α → α) :
    Axiom op ↔ ∃ B : BooleanAlgebra α,
      letI := B
      ∀ x y, (x ⊓ y)ᶜ = op x y := by
  constructor
  · intro W
    obtain ⟨seed⟩ := ‹Nonempty α›
    exact ⟨booleanAlgebra op W seed, booleanAlgebra_nand op W seed⟩
  · rintro ⟨B, h⟩
    letI := B
    have hn : (fun x y : α => (x ⊓ y)ᶜ) = op := funext fun x => funext (h x)
    rw [← hn]
    exact boolean_nand_axiom

end SingleNand
