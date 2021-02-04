import Mathlib.analysis.normed_space.basic
import Mathlib.topology.local_homeomorph

namespace Mathlib

open filter
open set

namespace asymptotics

macro "∀ᶠ " xs:Lean.explicitBinders " in " l:term "," b:term : term => do
  `($(← Lean.expandExplicitBinders `filter.eventually xs b) $l)

macro "∥ " x:term " ∥" : term => `(norm $x)

-- TODO: Type* syntax
variable {α : Type} {β : Type} {E : Type} {F : Type} {G : Type}
  {E' : Type} {F' : Type} {G' : Type} {R : Type} {R' : Type}

variable [has_norm E] [has_norm F] [has_norm G] [normed_group E'] [normed_group F']
  [normed_group G'] [normed_ring R] [normed_ring R']
  {c c' : ℝ} {f : α → E} {g : α → F} {k : α → G} {f' : α → E'} {g' : α → F'} {k' : α → G'}
  {l l' : filter α}

section defs

def is_O_with (c : ℝ) (f : α → E) (g : α → F) (l : filter α) : Prop :=
  ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥

theorem is_O_with_iff {c : real} {f : α → E} {g : α → F} {l : filter α} :
    is_O_with c f g l ↔ ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  iff.rfl

theorem is_O_with.of_bound {c : real} {f : α → E} {g : α → F} {l : filter α}
  (h : ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥) : is_O_with c f g l :=
  h

def is_O (f : α → E) (g : α → F) (l : filter α) : Prop :=
  ∃ c : ℝ, is_O_with c f g l

theorem is_O_iff_is_O_with {f : α → E} {g : α → F} {l : filter α} :
    is_O f g l ↔ ∃ c : ℝ, is_O_with c f g l :=
  iff.rfl

theorem is_O_iff {f : α → E} {g : α → F} {l : filter α} :
    is_O f g l ↔ ∃ c : ℝ, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  iff.rfl

theorem is_O.of_bound (c : ℝ) {f : α → E} {g : α → F} {l : filter α}
    (h : ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥) : is_O f g l :=
  ⟨c, h⟩

def is_o (f : α → E) (g : α → F) (l : filter α) : Prop :=
  ∀ (c : ℝ), 0 < c → is_O_with c f g l

theorem is_o_iff_forall_is_O_with {f : α → E} {g : α → F} {l : filter α} :
    is_o f g l ↔ ∀ (c : ℝ), 0 < c → is_O_with c f g l :=
  iff.rfl

theorem is_o_iff {f : α → E} {g : α → F} {l : filter α} :
    is_o f g l ↔ ∀ (c : ℝ), 0 < c → ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥
  := iff.rfl

theorem is_o.def {f : α → E} {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  h _ hc

theorem is_o.def' {f : α → E} {g : α → F} {l : filter α} (h : is_o f g l) {c : ℝ} (hc : 0 < c) :
    is_O_with c f g l :=
  h _ hc

end defs

theorem is_O_with.is_O (h : is_O_with c f g l) : is_O f g l := ⟨c, h⟩

theorem is_o.is_O_with (hgf : is_o f g l) : is_O_with 1 f g l := hgf _ zero_lt_one

theorem is_o.is_O (hgf : is_o f g l) : is_O f g l := hgf.is_O_with.is_O

end asymptotics
end Mathlib
