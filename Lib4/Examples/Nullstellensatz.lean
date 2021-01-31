import Mathlib.ring_theory.jacobson
import Mathlib.field_theory.algebraic_closure
import Mathlib.field_theory.mv_polynomial
import Mathlib.algebraic_geometry.prime_spectrum

set_option synthInstance.maxHeartbeats 50000

namespace Mathlib

syntax "{ " ident (" : " term)? " | " term " }" : term

macro_rules
  | `({ $x : $type | $p }) => `(Mathlib.set_of fun ($x:ident : $type) => $p)
  | `({ $x | $p })         => `(Mathlib.set_of fun ($x:ident : _) => $p)

universes u v w

open ideal

namespace mv_polynomial

variable {k : Type u} [field k]
variable {σ : Type v}

noncomputable def zero_locus (I : ideal (mv_polynomial σ k)) : set (σ → k) :=
  { x : σ → k | ∀ (p : mv_polynomial σ k), p ∈ I →
     coe_fn (_inst_1 := ring_hom.has_coe_to_fun) (eval x) p = 0 }

#exit
theorem mv_polynomial.mem_zero_locus_iff {I : ideal (mv_polynomial σ k)} {x : σ → k} :
    x ∈ zero_locus I ↔ (p : mv_polynomial σ k) → p ∈ I → coe_fn (_inst_1 := Mathlib.ring_hom.has_coe_to_fun) (eval x) p = has_zero.zero :=
  sorry

theorem zero_locus_anti_mono {I J : ideal (mv_polynomial σ k)} (h : I ≤ J) : zero_locus J ≤ zero_locus I :=
  sorry

theorem zero_locus_bot : zero_locus (⊥ : ideal (mv_polynomial σ k)) = ⊤ :=
  sorry

theorem zero_locus_top : zero_locus (⊤ : ideal (mv_polynomial σ k)) = ⊥ :=
  sorry

end mv_polynomial
end Mathlib
