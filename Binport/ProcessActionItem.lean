/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import Binport.Util
import Binport.Basic
import Binport.ActionItem
import Binport.Rules
import Binport.Translate
import Binport.OldRecursor
import Lean

namespace Binport

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def shouldGenCodeFor (d : Declaration) : Bool :=
  -- TODO: sadly, noncomputable comes after the definition
  -- (so if this isn't good enough, we will need to refactor)
  match d with
  | Declaration.defnDecl _ => true
  | _                      => false

def addDeclLoud (n : Name) (d : Declaration) : PortM Unit := do
  let path := (← read).path
  printlnf! "[addDecl] START {path.mrpath.path} {n}"
  addDecl d
  printlnf! "[addDecl] END   {path.mrpath.path} {n}"
  if shouldGenCodeFor d then
    match (← getEnv).compileDecl {} d with
    | Except.ok env    => println! "[compile] {n} SUCCESS!"
                          setEnv env
    | Except.error err => let msg ← err.toMessageData (← getOptions)
                          let msg ← msg.toString
                          println! "[compile] {n} {msg}"

def setAttr (attr : Attribute) (declName : Name) : PortM Unit := do
  let env ← getEnv
  match getAttributeImpl env attr.name with
  | Except.error errMsg => throwError errMsg
  | Except.ok attrImpl  => liftMetaM $ attrImpl.add declName attr.stx attr.kind

def processMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : PortM Unit := do
  -- For now, we avoid the `=` `=` clash by making all Mathlib notations
  -- lower priority than the Lean4 ones.
  let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

  let stxPrec  : Syntax := Syntax.mkNumLit (toString prec)
  let stxName  : Option Syntax := none
  let stxPrio  : Option Syntax := quote prio
  let stxOp    : Syntax := Syntax.mkStrLit tok
  let stxFun   : Syntax := Syntax.ident SourceInfo.none n.toString.toSubstring n []

  let stx ←
    match kind with
    | MixfixKind.infixl =>
      `(infixl:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.infixr =>
      `(infixr:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.prefix =>
      `(prefix:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.postfix =>
      `(postfix:$stxPrec $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.singleton =>
      let correctPrec : Option Syntax := Syntax.mkNumLit (toString Parser.maxPrec)
      `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)

  let nextIdx : Nat ← (← get).nNotations
  modify λ s => { s with nNotations := nextIdx + 1 }
  let ns : Syntax := mkIdent $ s!"{"__".intercalate (← read).path.mrpath.path.components}_{nextIdx}"
  let stx ← `(namespace $ns:ident $stx end $ns:ident)
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

def isBadSUnfold (n : Name) : PortM Bool := do
  if !n.isStr then return false
  if n.getString! != "_sunfold" then return false
  match (← getEnv).find? (n.getPrefix ++ `_main) with
  | some cinfo =>
    match cinfo.value? with
    -- bad means the original function isn't actually recursive
    | some v => Option.isNone $ v.find? fun e => e.isConst && e.constName!.isStr && e.constName!.getString! == "brec_on"
    | _ => throwError "should have value"
  | _ => return false /- this can happen when e.g. `nat.add._main -> Nat.add` (which may be needed due to eqn lemmas) -/

def processActionItem (actionItem : ActionItem) : PortM Unit := do
  modify λ s => { s with decl := actionItem.toDecl }
  let s ← get
  let env ← getEnv
  let f : Name → PortM Name :=
    fun n => do translateName s (← getEnv) n

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
        println! "[alias] {← f n1} short for {← f n2}"
        env := addAlias env (← f n1) (← f n2)
      setEnv env

  | ActionItem.mixfix kind n prec tok =>
    println! "[mixfix] {kind} {tok} {prec} {n}"
    processMixfix kind (← f n) prec tok

  | ActionItem.simp n prio => do
    tryAddSimpLemma (← f n) prio
    for eqn in (← get).name2equations.findD n [] do
      tryAddSimpLemma (← f eqn) prio

  | ActionItem.reducibility n kind => do
    -- (note: this will fail if it declares reducible in a new module)
    println! "reducibility {n} {repr kind}"
    try setAttr { name := reducibilityToName kind } (← f n)
    catch ex => warn ex

  | ActionItem.projection proj => do
    println! "[projection] {reprStr proj}"
    setEnv $ addProjectionFnInfo (← getEnv) (← f proj.projName) (← f proj.ctorName) proj.nParams proj.index proj.fromClass

  | ActionItem.class n => do
    let env ← getEnv
    if s.ignored.contains n then return ()
    -- for meta classes, Lean4 won't know about the decl
    match addClass env (← f n) with
    | Except.error msg => warnStr msg
    | Except.ok env    => setEnv env

  | ActionItem.instance nc ni prio => do
    -- for meta instances, Lean4 won't know about the decl
    -- note: we use `prio.pred` so that the Lean4 builtin instances get priority
    -- this is currently needed because Decidable instances aren't getting compiled!
    match (← get).noInsts.find? ni with
    | some _ => println! "[skipInstance] {ni}"
    | none   => try liftMetaM $ addInstance (← f ni) AttributeKind.global prio
                    setAttr { name := `inferTCGoalsRL } (← f ni)
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
      let name ← f ax.name
      let type ← translate ax.type

      if s.ignored.contains ax.name then return ()
      maybeRegisterEquation ax.name

      addDeclLoud ax.name $ Declaration.axiomDecl {
        ax with
          name := name,
          type := type
      }

    | Declaration.thmDecl thm => do
      let name ← f thm.name
      let type ← translate thm.type

      if s.ignored.contains thm.name then return ()
      maybeRegisterEquation thm.name

      if s.sorries.contains thm.name ∨ (¬ (← read).proofs ∧ ¬ s.neverSorries.contains thm.name) then
        printlnf! "sorry skipping: {thm.name}"
        addDeclLoud thm.name $ Declaration.axiomDecl {
          thm with
            name     := name,
            type     := type,
            isUnsafe := false -- TODO: what to put here?
        }
      else
        let value ← translate thm.value
        addDeclLoud thm.name $ Declaration.thmDecl {
          thm with
            name  := name,
            type  := type,
            value := value
        }

    | Declaration.defnDecl defn => do
      let name ← f defn.name
      let type ← translate defn.type

      if s.ignored.contains defn.name then return ()
      if ← isBadSUnfold name then return ()

      let mut value ← translate defn.value

      addDeclLoud defn.name $ Declaration.defnDecl {
        defn with
          name  := name,
          type  := type,
          value := value,
          hints := defn.hints
      }

    | Declaration.inductDecl lps nps [ind] iu => do
      let name ← f ind.name
      let type ← translate ind.type (reduce := false)

      if not (s.ignored.contains ind.name) then
        -- TODO: why do I need this nested do? Because of the scope?
        let ctors ← ind.ctors.mapM fun (ctor : Constructor) => do
          let cname ← f ctor.name
          let ctype ← translate ctor.type (reduce := false)
          pure { ctor with name := cname, type := ctype }
        addDeclLoud ind.name $ Declaration.inductDecl lps nps
          [{ ind with name := name, type := type, ctors := ctors }] iu

        try
          -- these may fail for the invalid inductive types currently being accepted
          -- by the temporary patch https://github.com/dselsam/lean4/commit/1bef1cb3498cf81f93095bda16ed8bc65af42535
          mkRecOn name
          mkCasesOn name
          mkNoConfusion name
          mkBelow name -- already there
          mkIBelow name
          mkBRecOn name
          mkBInductionOn name
        catch _ => pure ()

      let oldRecName := mkOldRecName (← f ind.name)
      let oldRec ← liftMetaM $ mkOldRecursor (← f ind.name) oldRecName
      match oldRec with
      | some oldRec => do
        addDeclLoud oldRecName oldRec
        setAttr { name := `reducible } oldRecName
      | none => pure ()

    | _ => throwError (toString d.names)

end Binport
