import Mathlib.analysis.normed_space.inner_product
import Mathlib.algebra.quadratic_discriminant
import Mathlib.analysis.normed_space.add_torsor
import Mathlib.data.matrix.notation
import Mathlib.linear_algebra.affine_space.finite_dimensional
import Mathlib.tactic.fin_cases
import Mathlib.data.real.basic

namespace Mathlib

-- TODO: how to port locales?
notation:max "π" => real.pi

namespace inner_product_geometry

universes u
variable {V : Type u} [inner_product_space ℝ V]

noncomputable def angle (x y : V) : ℝ :=
  real.arccos (inner x y / (norm x * norm y))

@[simp] theorem angle.def (x y : V) : angle x y = real.arccos (inner x y / (norm x * norm y)) :=
  sorry

theorem cos_angle (x y : V) : real.cos (angle x y) = inner x y / (norm x * norm y) :=
  sorry

theorem angle_comm (x y : V) : angle x y = angle y x := by
  -- TODO: unfold tactic, or more controlled `simp`
  rw [angle.def, angle.def, real_inner_comm]
  -- TODO: this fails because Mul vs HMul (need to normalize somewhere)
  -- (many other similar failures throughout)
  -- rw [mul_comm]
  exact sorry

theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y := by
  rw [angle.def, angle.def]
  rw [inner_neg_neg, norm_neg, norm_neg]

theorem angle_nonneg (x y : V) : 0 ≤ angle x y :=
  real.arccos_nonneg _

theorem angle_le_pi (x y : V) : angle x y ≤ π :=
  real.arccos_le_pi _

theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y := by
  rw [angle.def, angle.def]
  -- TODO: why does this fail?
  -- rw [←real.arccos_neg, norm_neg, inner_neg_right, neg_div]
  exact sorry

theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [←angle_neg_neg, neg_neg, angle_neg_right]

theorem angle_zero_left (x : V) : angle 0 x = π / 2 :=
  sorry

end inner_product_geometry
end Mathlib
