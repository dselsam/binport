import Mathlib.topology.algebra.open_subgroup
import Mathlib.topology.algebra.continuous_functions
import Mathlib.algebraic_geometry.locally_ringed_space
import PostPort.Coe

open Mathlib

section coe

open Mathlib.topological_space
open Mathlib.open_subgroup
open Mathlib.function
open Mathlib.topological_space

variable {G : Type} [group G] [topological_space G]
variable {U V : open_subgroup G} {g : G}

#check (U : Mathlib.set G)

end coe

section coe_to_fun

variable {α : Type} {β : Type} [topological_space α] [topological_space β]
variable {f g : {f : α → β // continuous f }}

variable (x : α)

-- Currently, the original instance will not be found because `noindex!` is missing.
noncomputable instance has_coe_continuous_noindex : has_coe_to_fun (noindex! {f : α → β // continuous f}) :=  ⟨_, subtype.val⟩

#check f x

end coe_to_fun

section coe_to_sort

open Mathlib.algebraic_geometry
open Mathlib.algebraic_geometry.LocallyRingedSpace

variable (X : LocallyRingedSpace)

#check ∀ (x : X), true

end coe_to_sort
