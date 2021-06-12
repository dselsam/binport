/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Util
import MathPort.Path
import Lean
import Std.Data.HashSet
import Std.Data.HashMap

namespace MathPort

open Lean

inductive MixfixKind
| «prefix»
| «infixl»
| «infixr»
| «postfix»
| «singleton»

def MixfixKind.toAttr : MixfixKind → Name
| MixfixKind.prefix     => `Lean.Parser.Command.prefix
| MixfixKind.postfix    => `Lean.Parser.Command.postfix
| MixfixKind.infixl     => `Lean.Parser.Command.infixl
| MixfixKind.infixr     => `Lean.Parser.Command.infixr
| MixfixKind.singleton  => `Lean.Parser.Command.notation

instance : ToString MixfixKind :=
  ⟨λ
    | MixfixKind.prefix    => "prefix"
    | MixfixKind.postfix   => "postfix"
    | MixfixKind.infixl    => "infixl"
    | MixfixKind.infixr    => "infixr"
    | MixfixKind.singleton => "notation"⟩

instance : BEq ReducibilityStatus :=
  ⟨λ
    | ReducibilityStatus.reducible,     ReducibilityStatus.reducible     => true
    | ReducibilityStatus.semireducible, ReducibilityStatus.semireducible => true
    | ReducibilityStatus.irreducible,   ReducibilityStatus.irreducible   => true
    | _, _                                                               => false⟩

structure ExportDecl : Type where
  currNs : Name
  ns   : Name
  nsAs : Name
  hadExplicit : Bool
  renames : Array (Name × Name)
  exceptNames : Array Name

structure ProjectionInfo : Type where
  -- pr_i A.. (mk A f_1 ... f_n) ==> f_i
  projName  : Name -- pr_i
  ctorName  : Name -- mk
  nParams   : Nat  -- |A..|
  index     : Nat  -- i
  fromClass : Bool
  deriving Repr

inductive ActionItem : Type
| decl           : Declaration → ActionItem
| «class»        : (c : Name) → ActionItem
| «instance»     : (c i : Name) → (prio : Nat) → ActionItem
| simp           : (name : Name) → (prio : Nat) → ActionItem
| «private»      : (pretty real : Name) → ActionItem
| «protected»    : (name : Name) → ActionItem
| «reducibility» : (name : Name) → ReducibilityStatus → ActionItem
| «mixfix»       : MixfixKind → Name → Nat → String → ActionItem
| «export»       : ExportDecl → ActionItem
| «projection»   : ProjectionInfo → ActionItem
| «position»     : (name : Name) → (line col : Nat) → ActionItem

def ActionItem.toDecl : ActionItem → Name
  | ActionItem.decl d =>
    match d.names with
    | []   => `nodecl
    | n::_ => n
  | ActionItem.class c            => c
  | ActionItem.instance _ i _     => i
  | ActionItem.simp n _           => n
  | ActionItem.private _ real     => real
  | ActionItem.protected n        => n
  | ActionItem.reducibility n _   => n
  | ActionItem.mixfix _ n _ _     => n
  | ActionItem.export _           => `inExport
  | ActionItem.projection p       => p.projName
  | ActionItem.position n _ _     => n

end MathPort
