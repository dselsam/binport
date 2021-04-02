/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean3Lib.init.core

namespace Mathlib

universes u v
variable {α : Type u} {β : Type v}

noncomputable instance [has_pow α β] : HPow α β α := ⟨pow⟩
noncomputable instance [has_pow α α] : Pow α      := ⟨pow⟩

end Mathlib
