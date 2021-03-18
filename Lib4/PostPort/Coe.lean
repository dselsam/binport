import Lean3Lib.init.coe

universes u v
variable {α : Sort u} {β : Sort v}

noncomputable instance hasCoe [inst : Mathlib.has_coe α β] : Coe α β := {
  coe := @Mathlib.has_coe.coe _ _ inst
}

-- TODO: why does mathlib declare these instances directly?
-- topology/algebra/open_subgroup.lean:42:instance has_coe_set : has_coe_t (open_subgroup G) (set G) := ⟨λ U, U.1⟩
noncomputable instance hasCoeT [inst : Mathlib.has_coe_t α β] : CoeTC α β := {
  coe := @Mathlib.has_coe_t.coe _ _ inst
}

noncomputable instance hasCoeToFun [inst : Mathlib.has_coe_to_fun α] : CoeFun α (no_index (@Mathlib.has_coe_to_fun.F _ inst)) := {
  coe := @Mathlib.has_coe_to_fun.coe _ inst
}

noncomputable instance hasCoeToSort [inst : Mathlib.has_coe_to_sort α] : CoeSort α (no_index (@Mathlib.has_coe_to_sort.S _ inst)) := {
  coe := @Mathlib.has_coe_to_sort.coe _ inst
}
