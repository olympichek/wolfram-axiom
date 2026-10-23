import Lean

/-!
The single NAND axiom characterizes Boolean algebras on nonempty carriers.
Elementary identities are derived using substitution and equality rewriting.
-/

namespace SingleNand

universe u

/-- The proposed identity, with no other assumptions on the operation. -/
def Axiom {α : Type u} (op : α → α → α) : Prop :=
  ∀ x y z, op (op (op x y) z) (op x (op (op x z) x)) = z

section Equations
variable {α : Type u} (op : α → α → α) (W : Axiom op)
local infixl:70 " ⋆ " => op

private def q (x y : α) := x ⋆ ((x ⋆ y) ⋆ x)
private def m (x : α) := q op x x

include W

private theorem R (x y : α) : (q op x y ⋆ y) ⋆ q op x y = y :=
  W x ((x ⋆ y) ⋆ x) y

private theorem R' (x y : α) : q op (q op x y) y = q op x y ⋆ y := by
  change q op x y ⋆ ((q op x y ⋆ y) ⋆ q op x y) = q op x y ⋆ y
  rw [R op W]

private theorem C₀ (x y z : α) : (x ⋆ y) ⋆ q op (z ⋆ x) y = y := by
  have h (v w : α) : (x ⋆ y) ⋆ q op ((v ⋆ w) ⋆ x) y = y := by
    have h := W ((v ⋆ w) ⋆ x) (q op v x) y
    change (((v ⋆ w) ⋆ x) ⋆ q op v x) ⋆ y ⋆ q op ((v ⋆ w) ⋆ x) y = y at h
    rw [show ((v ⋆ w) ⋆ x) ⋆ q op v x = x from W v w x] at h
    exact h
  have hz : ((z ⋆ z) ⋆ z) ⋆ m op z = z := W z z z
  simpa only [hz] using h ((z ⋆ z) ⋆ z) (m op z)

private theorem D₀ (a b c : α) : (q op a b ⋆ c) ⋆ q op b c = c := by
  have h := C₀ op W (q op a b) c ((a ⋆ a) ⋆ b)
  rw [show ((a ⋆ a) ⋆ b) ⋆ q op a b = b from W a a b] at h
  exact h

private theorem J₀ (x y z : α) :
    (q op x (q op y z) ⋆ z) ⋆ (q op y z ⋆ z) = z := by
  simpa only [R' op W] using D₀ op W x (q op y z) z

private theorem U₁ (a : α) : (a ⋆ m op a) ⋆ a = m op a := by
  have h := C₀ op W a (m op a) (a ⋆ a)
  have h₁ : ((a ⋆ a) ⋆ a) ⋆ m op a = a := W a a a
  have h₂ : q op ((a ⋆ a) ⋆ a) (m op a) = a := by
    unfold q
    rw [h₁]
    exact h₁
  rwa [h₂] at h

private theorem U₂ (a : α) : m op a ⋆ m op a = a := by
  have h := W a (m op a) a
  change ((a ⋆ m op a) ⋆ a) ⋆ m op a = a at h
  rwa [U₁ op W] at h

private theorem U₃ (a : α) : m op a ⋆ (m op a ⋆ a) = a := by
  have h := J₀ op W a a a
  have hq : q op a (m op a) = a ⋆ m op a := by
    unfold q
    rw [U₁ op W]
  change (q op a (m op a) ⋆ a) ⋆ (m op a ⋆ a) = a at h
  rwa [hq, U₁ op W] at h

private theorem U₄ (a : α) : a ⋆ (m op a ⋆ (a ⋆ m op a)) = m op a := by
  have h := C₀ op W ((a ⋆ a) ⋆ a) (m op a) a
  have ha : ((a ⋆ a) ⋆ a) ⋆ m op a = a := W a a a
  change (((a ⋆ a) ⋆ a) ⋆ m op a) ⋆ q op (m op a) (m op a) = m op a at h
  rw [ha] at h
  simpa only [q, U₂ op W] using h

private theorem V₀ (d b : α) :
    (d ⋆ d) ⋆ (q op (b ⋆ (d ⋆ d)) d ⋆ d) = d := by
  let v := (d ⋆ d) ⋆ d
  let r := q op (b ⋆ (d ⋆ d)) d
  have h₁ : v ⋆ r = d := C₀ op W (d ⋆ d) d b
  have h₂ : q op v r = d := by
    change v ⋆ ((v ⋆ r) ⋆ v) = d
    rw [h₁]
    exact W d d d
  have h := J₀ op W v (b ⋆ (d ⋆ d)) d
  change (q op v r ⋆ d) ⋆ (r ⋆ d) = d at h
  rwa [h₂] at h

private theorem V (a b : α) :
    a ⋆ (q op (b ⋆ a) (m op a) ⋆ m op a) = m op a := by
  simpa only [U₂ op W] using V₀ op W (m op a) b

private theorem m_eq (a : α) : m op a = a ⋆ a := by
  let u := m op a
  let t := (a ⋆ a) ⋆ a
  let w := u ⋆ (a ⋆ u)
  have h₁ : u ⋆ u = a := U₂ op W a
  have h₂ : u ⋆ (u ⋆ a) = a := U₃ op W a
  have h₃ : a ⋆ w = u := U₄ op W a
  have h₄ : t ⋆ u = a := W a a a
  have h₅ : m op u = w := by
    change u ⋆ ((u ⋆ u) ⋆ u) = w
    rw [h₁]
  have h₆ : (a ⋆ (u ⋆ a)) ⋆ w = u ⋆ a := by
    have h := W u u (u ⋆ a)
    rw [h₁, h₂] at h
    exact h
  have h₇ := V op W u t
  rw [h₄, h₅] at h₇
  have hq : q op a w = a ⋆ (u ⋆ a) := by
    unfold q
    rw [h₃]
  rw [hq, h₆, h₂] at h₇
  change u = a ⋆ a
  rw [← h₇] at h₃
  exact h₃.symm

/-- Double negation follows from the single axiom. -/
theorem double_neg (a : α) : (a ⋆ a) ⋆ (a ⋆ a) = a := by
  simpa only [m_eq op W] using U₂ op W a

private theorem H (a : α) : (a ⋆ a) ⋆ (a ⋆ (a ⋆ a)) = a := by
  have h := m_eq op W (a ⋆ a)
  change (a ⋆ a) ⋆ (((a ⋆ a) ⋆ (a ⋆ a)) ⋆ (a ⋆ a)) = (a ⋆ a) ⋆ (a ⋆ a) at h
  simpa only [double_neg op W] using h

private theorem L (a b : α) : ((a ⋆ b) ⋆ a) ⋆ (a ⋆ a) = a := by
  have h := W a b a
  change ((a ⋆ b) ⋆ a) ⋆ m op a = a at h
  rwa [m_eq op W] at h

private theorem P₀ (a b c : α) :
    ((q op a b ⋆ c) ⋆ b) ⋆ (q op a b ⋆ b) = b := by
  have h := W (q op a b) c b
  change ((q op a b ⋆ c) ⋆ b) ⋆ q op (q op a b) b = b at h
  rwa [R' op W] at h

private theorem E₀ (a b c : α) :
    ((q op a b ⋆ b) ⋆ c) ⋆ q op b c = c := by
  have h := C₀ op W (q op a b ⋆ b) c ((q op a b ⋆ b) ⋆ b)
  rwa [P₀ op W] at h

private theorem K₀ (a b : α) : a ⋆ q op a (q op b a) = q op b a := by
  have h := E₀ op W b a (q op b a)
  rwa [R op W] at h

private theorem B₀ (a b c : α) : a ⋆ q op (b ⋆ c) (q op b a) = q op b a := by
  have h := W (b ⋆ c) a (q op b a)
  change (((b ⋆ c) ⋆ a) ⋆ q op b a) ⋆ q op (b ⋆ c) (q op b a) = q op b a at h
  rwa [show ((b ⋆ c) ⋆ a) ⋆ q op b a = a from W b c a] at h

private theorem I₀ (a b c : α) : a ⋆ q op b (q op (c ⋆ b) a) = q op (c ⋆ b) a := by
  have h := W b a (q op (c ⋆ b) a)
  change ((b ⋆ a) ⋆ q op (c ⋆ b) a) ⋆ q op b (q op (c ⋆ b) a) = q op (c ⋆ b) a at h
  rwa [C₀ op W] at h

private theorem N₀ (x y : α) : q op (x ⋆ y) y ⋆ (y ⋆ y) = y := by
  let r := q op (x ⋆ y) y
  have h₁ : (y ⋆ y) ⋆ r = y := C₀ op W y y x
  have h₂ : q op (y ⋆ y) r = y := by
    unfold q
    rw [h₁]
    exact H op W y
  have h := I₀ op W r y y
  rw [h₂] at h
  change r ⋆ m op y = y at h
  rwa [m_eq op W] at h

private theorem O₀ (a b : α) : a ⋆ q op (b ⋆ a) (a ⋆ a) = a ⋆ a := by
  have h := W (b ⋆ a) (((b ⋆ a) ⋆ a) ⋆ (b ⋆ a)) (a ⋆ a)
  change (q op (b ⋆ a) a ⋆ (a ⋆ a)) ⋆ q op (b ⋆ a) (a ⋆ a) = a ⋆ a at h
  rwa [N₀ op W] at h

private theorem T₀ (a b : α) : q op (b ⋆ a) (a ⋆ a) = a := by
  let r := q op (b ⋆ a) (a ⋆ a)
  have h₁ : a ⋆ r = a ⋆ a := O₀ op W a b
  have h₂ : q op a r = a ⋆ a := by
    unfold q
    rw [h₁]
    exact m_eq op W a
  have h := I₀ op W (a ⋆ a) a b
  change (a ⋆ a) ⋆ q op a r = r at h
  rw [h₂, double_neg op W] at h
  exact h.symm

private theorem balance₁ (a b : α) : ((a ⋆ b) ⋆ a) ⋆ q op a b = a := by
  have h := T₀ op W a (a ⋆ b)
  unfold q at h
  rw [L op W] at h
  exact h

private theorem balance₂ (a b : α) : q op a b ⋆ a = (a ⋆ b) ⋆ a := by
  have h := balance₁ op W ((a ⋆ b) ⋆ a) (a ⋆ a)
  rwa [L op W, T₀ op W] at h

private theorem balance₃ (a b : α) : ((a ⋆ b) ⋆ a) ⋆ a = q op a b := by
  let t := (a ⋆ b) ⋆ a
  let r := q op a b
  have h₁ : t ⋆ r = a := balance₁ op W a b
  have h₂ : r ⋆ a = t := balance₂ op W a b
  have h₃ : q op a t = r := by
    change a ⋆ (r ⋆ a) = r
    rw [h₂]
    rfl
  have h₄ : q op t r = a := by
    change t ⋆ ((t ⋆ r) ⋆ t) = a
    rw [h₁]
    exact h₁
  have h := K₀ op W t a
  rwa [h₃, h₄] at h

private theorem W₁ (a b : α) : (a ⋆ a) ⋆ q op a b = a := by
  have h (c : α) : (a ⋆ a) ⋆ (q op (c ⋆ a) a ⋆ a) = a := by
    have h₁ : (a ⋆ a) ⋆ q op (c ⋆ a) a = a := C₀ op W a a c
    have h₂ : q op (a ⋆ a) (q op (c ⋆ a) a) = a := by
      change (a ⋆ a) ⋆ (((a ⋆ a) ⋆ q op (c ⋆ a) a) ⋆ (a ⋆ a)) = a
      rw [h₁]
      exact H op W a
    have h₃ := J₀ op W (a ⋆ a) (c ⋆ a) a
    rwa [h₂] at h₃
  have hq : q op (q op a b) a = (a ⋆ b) ⋆ a := by
    change q op a b ⋆ ((q op a b ⋆ a) ⋆ q op a b) = (a ⋆ b) ⋆ a
    rw [balance₂ op W, balance₁ op W, balance₂ op W]
  have h' := h ((a ⋆ b) ⋆ a)
  rwa [balance₃ op W, hq, balance₃ op W] at h'

private theorem Q₁ (a b : α) : q op b a = a ⋆ b := by
  have h := B₀ op W a b b
  have hq : q op (b ⋆ b) (q op b a) = b := by
    change (b ⋆ b) ⋆ (((b ⋆ b) ⋆ q op b a) ⋆ (b ⋆ b)) = b
    rw [W₁ op W]
    exact H op W b
  rw [hq] at h
  exact h.symm

/-- Commutativity is derived, not assumed. -/
theorem comm (a b : α) : a ⋆ b = b ⋆ a := by
  have h := K₀ op W a b
  rw [Q₁ op W a b, Q₁ op W (a ⋆ b) a] at h
  change q op a b = a ⋆ b at h
  simpa only [Q₁ op W] using h.symm

/-- The first of the three identities used to recover the lattice. -/
theorem I (x y : α) : (x ⋆ x) ⋆ (x ⋆ y) = x := by
  simpa only [Q₁ op W, comm op W y x] using W₁ op W x y

/-- A splitting identity. -/
theorem S (x y z : α) : (x ⋆ y) ⋆ (y ⋆ (x ⋆ z)) = y := by
  have h := W x z y
  change ((x ⋆ z) ⋆ y) ⋆ q op x y = y at h
  rw [Q₁ op W] at h
  simpa only [comm op W (x ⋆ z) y, comm op W y x,
    comm op W (y ⋆ (x ⋆ z)) (x ⋆ y)] using h

/-- The nested absorption identity. -/
theorem J (x y z : α) : x ⋆ (y ⋆ (x ⋆ (y ⋆ z))) = x ⋆ (y ⋆ z) := by
  have h := I₀ op W x y z
  simp only [Q₁ op W] at h
  simpa only [comm op W z y, comm op W (x ⋆ (y ⋆ z)) y] using h

end Equations

end SingleNand
