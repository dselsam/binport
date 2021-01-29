import Mathlib.topology.opens
import Mathlib.category_theory.sites.grothendieck
import Mathlib.category_theory.sites.pretopology
import Mathlib.category_theory.limits.lattice

namespace Mathlib

universe u

namespace opens

variable (T : Type u) [topological_space T]

open category_theory topological_space category_theory.limits

noncomputable def grothendieck_topology : @grothendieck_topology (opens T) (preorder.small_category _) := {
  sieves := λ (X : topological_space.opens T) (S : category_theory.sieve X) =>
      (x : T) → x ∈ X → ∃ (U : topological_space.opens T), ∃ (f : U ⟶ X),
        -- TODO: this is a recurring issue and we must solve it, one way or another
        @coe_fn _ sieve.has_coe_to_fun S U f ∧ x ∈ U,

  top_mem' := λ (X : topological_space.opens T) (x : T) (hx : x ∈ X) =>
    Exists.intro X (Exists.intro (category_theory.category_struct.id X) { left := trivial, right := hx }),

  pullback_stable' := sorry,
  transitive' := sorry
}

-- TODO: the type of the following definition triggers the error of Meta/SynthInstance.lean:L193
-- because `category_theory.limits.has_finite_wide_pullbacks` is not reducible.
-- In Lean3, it would presumably be unfolded until reaching a class, but it is not currently in Lean4.

#exit
noncomputable def pretopology : @pretopology (opens T) (preorder.small_category _) sorry := {
  coverings := λ (X : topological_space.opens T) (R : category_theory.presieve X) =>
      (x : T) → x ∈ X → Exists λ (U : topological_space.opens T) => Exists λ (f : U ⟶ X) => R f ∧ x ∈ U,
  has_isos := sorry,
  pullbacks := sorry,
  transitive := sorry
}

end opens
end Mathlib
