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
    else if n.isStr && (n.getString! == "below" || n.getString! == "ibelow") then
      let newName := Name.mkStr (dflt n.getPrefix) ("old_" ++ n.getString!)
      --dbgTrace! "[tbelow] {n} ==> {newName}"
      newName
    else dflt n

  where
    dflt n := `Mathlib ++ n

def translate (e : Expr) : PortM Expr := do
  println! "[translate] START"
  let s ← get
  let e := e.replaceConstNames (translateName s (← getEnv))
  let e ← liftMetaM $ Meta.transform e (pre := translateNumbers s)
  let e ← liftMetaM $ Meta.transform e (pre := translateStrings s)
  println! "[translate] END  "
  e

  where
    translateNames s e : MetaM TransformStep := do
      match e with
      | Expr.const n ls _ => TransformStep.done $ mkConst (translateName s (← getEnv) n) ls
      | e                 => TransformStep.done e

    translateNumbers s e : MetaM TransformStep :=
      match isConcreteNat? e with
      | some n => TransformStep.done $ mkNatLit n
      | none   =>
        match isNumber? e with
        | none => TransformStep.visit e
        | some info@⟨n, level, type, hasZero?, hasOne?, hasAdd?⟩ => do
          let ofNatType := mkAppN (mkConst `OfNat [level]) #[type, mkNatLit n]
          if n == 0 then
            let ofNatInst := mkAppN (mkConst `Mathlib.PrePort.instZero2Nat [level]) #[type, hasZero?.get!]
            check e $ mkAppN (mkConst `OfNat.ofNat [level]) #[type, mkNatLit n, ofNatInst]
          else if n == 1 then
            let ofNatInst := mkAppN (mkConst `Mathlib.PrePort.instOne2Nat [level]) #[type, hasOne?.get!]
            check e $ mkAppN (mkConst `OfNat.ofNat [level]) #[type, mkNatLit n, ofNatInst]
          else
            -- TODO: too slow currently
            TransformStep.done e
            -- mkAppN (mkConst `Mathlib.PrePort.instBits2Nat [level]) #[type, hasOne?.get!, hasAdd?.get!, mkNatLit (n-1)]


    translateStrings s e : MetaM TransformStep := do
      if not (e.isAppOfArity `Mathlib.string.str 2) then TransformStep.visit e else
        let str : Expr := mkAppN (mkConst `Mathlib.PrePort.fromString3) #[e]
        let str ← Meta.reduce str
        -- the equality only holds by `rfl` for literals
        if str.isStringLit then
          check e $ mkAppN (mkConst `Mathlib.PrePort.toString3) #[str]
        else TransformStep.done e

    check e e' : MetaM TransformStep := do
      TransformStep.done e'
      -- Sadly, the following check is very slow
      -- if (← Meta.isDefEq e e') then TransformStep.done e'
      -- else throwError! "[translateNumber] broke def-eq, \n{e}\n\n!=\n\n{e'}"

end MathPort
