/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import Port34.Util
import Port34.Basic
import Port34.ActionItem
import Port34.Rules
import Port34.OldRecursor
import Lean

namespace Port34

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def addDeclLoud (n : Name) (d : Declaration) : PortM Unit := do
  let path := (← read).path
  println! "[addDecl] START {path.mrpath.path} {n}"
  addDecl d
  println! "[addDecl] END   {path.mrpath.path} {n}"

def setAttr (attr : Attribute) (declName : Name) : PortM Unit := do
  let env ← getEnv
  match getAttributeImpl env attr.name with
  | Except.error errMsg => throwError errMsg
  | Except.ok attrImpl  => liftMetaM $ attrImpl.add declName attr.stx attr.kind

def processMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : PortM Unit := do
  let path := (← read).path

  -- For now, we avoid the `=` `=` clash by making all Mathlib notations
  -- lower priority than the Lean4 ones.
  let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

  let stxPrec  : Option Syntax := Syntax.mkNumLit (toString prec)
  let stxPrec2 : Option Syntax := stxPrec
  let stxName  : Option Syntax := none
  let stxPrio  : Option Syntax := quote prio
  let stxOp    : Syntax := Syntax.mkStrLit tok
  let stxFun   : Syntax := Syntax.ident SourceInfo.none n.toString.toSubstring n []

  let stx ←
    match kind with
    | MixfixKind.infixl =>
      `(infixl $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.infixr =>
      `(infixr $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.prefix =>
      `(prefix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.postfix =>
      `(postfix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.singleton =>
      `(notation $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)

  println! s!"syntax:\n\n{Lean.Elab.Frontend.showSyntax stx}"
  elabCommand stx

def maybeRegisterEquation (n : Name) : PortM Unit := do
  -- example: list.nth.equations._eqn_1
  -- def insertWith (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
  let n₁ : Name := n.getPrefix
  if n₁.isStr && n₁.getString! == "equations" then
    modify λ s => { s with name2equations := s.name2equations.insertWith (· ++ ·) n₁.getPrefix [n] }

def tryAddSimpLemma (n : Name) (prio : Nat) : PortM Unit :=
  try
    liftMetaM $ addSimpLemma n False AttributeKind.global prio
    println! "[simp] {n} {prio}"
  catch ex => warn ex

def processActionItem (actionItem : ActionItem) : PortM Unit := do
  modify λ s => { s with decl := actionItem.toDecl }
  let s ← get
  let f n := newName s n
  let r (e : Expr) := e.replaceConstNames f

  match actionItem with
  | ActionItem.export d => do
    println! "[export] {d.currNs} {d.ns} {d.nsAs} {d.hadExplicit}, renames={d.renames}, excepts={d.exceptNames}"
    -- we use the variable names of elabExport
    if not d.exceptNames.isEmpty then
      warnStr s!"export of {d.ns} with exceptions is ignored"
    else if d.nsAs != Name.anonymous then
      warnStr s!"export of {d.ns} with 'nsAs' is ignored"
    else if ¬ d.hadExplicit then
      warnStr s!"export of {d.ns} with no explicits is ignored"
    else
      let mut env ← getEnv
      for (n1, n2) in d.renames do
        println! "[alias] {f n1} short for {f n2}"
        env := addAlias env (f n1) (f n2)
      setEnv env

  | ActionItem.mixfix kind n prec tok =>
    println! "[mixfix] {kind} {tok} {prec} {n}"
    processMixfix kind (f n) prec tok

  | ActionItem.simp n prio => do
    tryAddSimpLemma (f n) prio
    for eqn in (← get).name2equations.findD n [] do
      tryAddSimpLemma (f eqn) prio

  | ActionItem.reducibility n kind => do
    -- (note: this will fail if the attribute is in a new module)
    if kind == ReducibilityStatus.reducible then
      println! "reducible {n}"
      try setAttr { name := `reducible } (f n)
      catch ex => warn ex

  | ActionItem.class n => do
    let env ← getEnv
    if s.ignored.contains n then return ()
    -- for meta classes, Lean4 won't know about the decl
    match addClass env (f n) with
    | Except.error msg => warnStr msg
    | Except.ok env    => setEnv env

  | ActionItem.instance nc ni prio => do
    -- for meta instances, Lean4 won't know about the decl
    -- note: we use `prio.pred` so that the Lean4 builtin instances get priority
    -- this is currently needed because Decidable instances aren't getting compiled!
    match (← get).noInsts.find? ni with
    | some _ => println! "[skipInstance] {ni}"
    | none   => try liftMetaM $ addInstance (f ni) AttributeKind.global prio
                catch ex => warn ex

  | ActionItem.private _ _ => pure ()
  | ActionItem.protected n =>
    -- TODO: have the semantics changed here?
    -- When we mark `nat.has_one` as `Protected`, the kernel
    -- fails to find it when typechecking definitions (but not theorems)
    -- setEnv $ addProtected (← getEnv) (f n)
    pure ()

  | ActionItem.decl d => do
    match d with
    | Declaration.axiomDecl ax => do
      let name := f ax.name
      let type := r ax.type

      if s.ignored.contains ax.name then return ()
      maybeRegisterEquation ax.name

      addDeclLoud ax.name $ Declaration.axiomDecl {
        ax with
          name := name,
          type := type
      }

    | Declaration.thmDecl thm => do
      let name  := f thm.name
      let type  := r thm.type

      if s.ignored.contains thm.name then return ()
      maybeRegisterEquation thm.name

      if s.sorries.contains thm.name ∨ ¬ (← read).proofs then
        addDeclLoud name $ Declaration.axiomDecl {
          thm with
            name     := name,
            type     := type,
            isUnsafe := false -- TODO: what to put here?
        }
      else
        let value := r thm.value
        addDeclLoud name $ Declaration.thmDecl {
          thm with
            name  := name,
            type  := type,
            value := value
        }

    | Declaration.defnDecl defn => do
      let name  := f defn.name
      let type  := r defn.type

      if s.ignored.contains defn.name then return ()

      let value := r defn.value
      let env ← getEnv
      addDeclLoud defn.name $ Declaration.defnDecl {
        defn with
          name  := name,
          type  := type,
          value := value,
          hints := defn.hints
      }

    | Declaration.inductDecl lps nps [ind] iu => do
      let name := f ind.name
      let type := r ind.type
      if not (s.ignored.contains ind.name) then
        addDeclLoud ind.name $ Declaration.inductDecl lps nps
          [{ ind with
              name := name,
              type := type,
              ctors := ind.ctors.map (fun ctor => { ctor with name := f ctor.name, type := r ctor.type })
          }]
          iu

      -- TODO: for now we *always* create `<ind>._oldrec` even if the recursor is unchanged
      -- This is more expedient since now name substitution is cheap even without
      -- task-global state.
      let oldRecName := mkOldRecName (f ind.name)
      let oldRec ← liftMetaM $ mkOldRecursor (f ind.name) oldRecName
      match oldRec with
      | some oldRec => do
        addDeclLoud oldRecName oldRec
        setAttr { name := `reducible } oldRecName
      | none        => do
        let env ← getEnv
        match env.find? $ name ++ "rec" with
        | none => throwError s!"rec for {f ind.name} not found!"
        | some cinfo => do
          addDeclLoud oldRecName $ Declaration.defnDecl {
               name        := oldRecName,
               levelParams := cinfo.lparams,
               type        := cinfo.type,
               value       := mkConst cinfo.name $ cinfo.lparams.map mkLevelParam,
               safety      := DefinitionSafety.safe,
               hints       := ReducibilityHints.abbrev,
          }
          setAttr { name := `reducible } oldRecName

    | _ => throwError $ toString d.names

end Port34
