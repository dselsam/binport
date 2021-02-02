/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Util
import MathPort.Basic
import MathPort.ActionItem
import MathPort.OldRecursor
import MathPort.Number
import Lean

namespace MathPort
open Lean

-- TODO: put somewhere else or don't call it State
partial def translateName (s : State) (env : Environment) (n : Name) : Name := do
  match s.newNames.find? n with
  | some new => new
  | none     =>
    if n.isStr && n.getString! == "rec" && not n.getPrefix.isAnonymous then
      let newIndName := translateName s env n.getPrefix
      match env.find? newIndName with
      | none => dflt n
      | some cInfo =>
        match cInfo with
        | ConstantInfo.inductInfo _ =>
          if env.contains (mkOldRecName newIndName) then mkOldRecName newIndName
          else newIndName ++ "rec"
        | _ => dflt n
    else dflt n

  where
    dflt n := `Mathlib ++ n

def isRegularNat (s : State) (env : Environment) : Number.NumInfo → MetaM Bool
  | ⟨n, level, type, hasZero?, hasOne?, hasAdd?⟩ =>
    let natType := mkConst $ tn `nat
    let natZero := mkConst $ tn `nat.has_zero
    let natOne  := mkConst $ tn `nat.has_one
    let natAdd  := mkConst $ tn `nat.has_add
    Meta.isDefEq type natType
    <&&> Meta.isDefEq (hasZero?.getD natZero) natZero
    <&&> Meta.isDefEq (hasOne?.getD natOne) natOne
    <&&> Meta.isDefEq (hasAdd?.getD natAdd) natAdd

  where
    tn n := translateName s env n

def translate (e : Expr) : PortM Expr := do
  let s ← get
  let e := e.replaceConstNames (translateName s (← getEnv))
  let e ← liftMetaM $ Meta.transform e (pre := translateNumbers s)
  e

  where
    translateNames s e : MetaM TransformStep := do
      match e with
      | Expr.const n ls _ => TransformStep.done $ mkConst (translateName s (← getEnv) n) ls
      | e                 => TransformStep.done e

    translateNumbers s e : MetaM TransformStep :=
      match Number.toNumInfo e with
      | none   => TransformStep.visit e
      | some info@⟨n, level, type, hasZero?, hasOne?, hasAdd?⟩ => do
        if ← isRegularNat s (← getEnv) info then
          check e $ mkNatLit n
        else
          let ofNatType := mkAppN (mkConst `OfNat [level]) #[type, mkNatLit n]
          let ofNatInst :=
            if n == 0 then
              -- def Mathlib.PrePort.instZero2Nat.{u} : {α : Type u} → [inst : HasZero α] → OfNat α 0
              mkAppN (mkConst `Mathlib.PrePort.instZero2Nat [level]) #[type, hasZero?.get!]
            else if n == 1 then
              -- def Mathlib.PrePort.instOne2Nat.{u} : {α : Type u} → [inst : HasOne α] → OfNat α 1
              mkAppN (mkConst `Mathlib.PrePort.instOne2Nat [level]) #[type, hasOne?.get!]
            else
              -- def Mathlib.PrePort.instBits2Nat.{u} : {α : Type u} → [inst : HasOne α] → [inst : Add α] → (n : Nat) → OfNat α (n + 1) :=
              mkAppN (mkConst `Mathlib.PrePort.instBits2Nat [level]) #[type, hasOne?.get!, hasAdd?.get!, mkNatLit (n-1)]
          check e $ mkAppN (mkConst `OfNat.ofNat [level]) #[type, mkNatLit n, ofNatInst]

    check e e' : MetaM TransformStep := do
      if (← Meta.isDefEq e e') then TransformStep.done e'
      else throwError! "[translateNumber] broke def-eq, \n{e}\n\n!=\n\n{e'}"


end MathPort
