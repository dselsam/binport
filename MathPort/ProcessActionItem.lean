/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import MathPort.Util
import MathPort.Basic
import MathPort.ActionItem
import MathPort.Rules
import MathPort.Translate
import MathPort.OldRecursor
import Lean

namespace MathPort

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

def shouldGenCodeFor (d : Declaration) : Bool :=
  -- TODO: sadly, noncomputable comes after the definition
  -- (so if this isn't good enough, we will need to refactor)
  match d with
  | Declaration.defnDecl _ => true
  | _                      => false

def addDeclLoud (n : Name) (d : Declaration) : PortM Unit := do
  let path := (← read).path
  println! "[addDecl] START {path.mrpath.path} {n}"
  if n == `module.End.eigenvectors_linear_independent then
    match d with
    | Declaration.thmDecl d => println! "[fail] {d.type} \n\n\n\n{d.value}"
    | _ => pure ()
  addDecl d
  println! "[addDecl] END   {path.mrpath.path} {n}"
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

  let stxPrec  : Option Syntax := Syntax.mkNumLit (toString prec)
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
      let correctPrec : Option Syntax := Syntax.mkNumLit (toString Parser.maxPrec)
      `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)

  let nextIdx : Nat ← (← get).nNotations
  modify λ s => { s with nNotations := nextIdx + 1 }
  let ns : Syntax := mkIdent $ s!"{(← read).path.mrpath.toUnderscorePath}_{nextIdx}"
  let stx ← `(namespace $ns:ident $stx end $ns:ident)
  elabCommand stx

def maybeRegisterEquation (n : Name) : PortM Unit := do
  match (← get).eqnLemmas.find? n with
  | some pfix => modify λ s => { s with name2eqns := s.name2eqns.insertWith (· ++ ·) pfix [n] }
  | none => pure ()

def tryAddSimpLemma (n : Name) (prio : Nat) : PortM Unit :=
  try
    liftMetaM $ addSimpLemma n False AttributeKind.global prio
    println! "[simp] {n} {prio}"
  catch ex => warn ex

structure NameTypeValue : Type where
  name  : Name
  type  : Expr
  value : Expr
  deriving Inhabited

def extractNameTypeValue (decl : Declaration) : NameTypeValue :=
  match decl with
  | Declaration.defnDecl d => ⟨d.name, d.type, d.value⟩
  | Declaration.thmDecl  d => ⟨d.name, d.type, d.value⟩
  | _ => panic! "shouldn't happen"

def updateNameTypeValue (decl : Declaration) (ntv : NameTypeValue) : Declaration :=
  match decl with
  | Declaration.defnDecl d => Declaration.defnDecl { d with name := ntv.name, type := ntv.type, value := ntv.value }
  | Declaration.thmDecl  d => Declaration.thmDecl  { d with name := ntv.name, type := ntv.type, value := ntv.value }
  | _ => panic! "shouldn't be possible"

def mkNary (op : Name) (xs : Array Expr) : Expr := do
  let mut e := xs[0]
  for i in [1:xs.size] do
    e := mkAppN (mkConst op) #[e, xs[i]]
  pure e

def extractNary (op : Name) (e₀ : Expr) : Array Expr := do
  let mut  e := e₀
  let mut xs := #[]
  while (e.isAppOfArity op 2) do
    xs := xs.push (e.getArg! 2)
    e  := e.getArg! 1
  pure xs.reverse

def processOpaque (od : OpaqueDeclaration) : PortM Unit := do
  let s ← get
  let f n := translateName s (← getEnv) n

  match od.decl with
  | Declaration.defnDecl d =>
    let targetName : Name := f d.name

    let dname : Name := targetName ++ `_original
    let dtype : Expr ← translate d.type
    let dval  : Expr ← translate d.value

    addDeclLoud dname $ Declaration.defnDecl { d with
      name        := dname,
      type        := dtype,
      value       := dval
    }

    let targetLemNames : Array Name := od.eqnLemmas.map fun eqnLemma => f eqnLemma.names.head!

    let lemmaNTVs : Array NameTypeValue ← od.eqnLemmas.mapM fun eqnLemma => do
      let ⟨lname, ltype, lval⟩ := extractNameTypeValue eqnLemma
      let lname : Name := f lname ++ `original
      let ltype : Expr := (← translate ltype).replaceConstNames fun n => if n == targetName then dname else n
      let lval  : Expr := (← translate lval).replaceConstNames fun n => if n == targetName then dname else n
      addDeclLoud lname $ updateNameTypeValue od.eqnLemmas[0] ⟨lname, ltype, lval⟩
      pure ⟨lname, ltype, lval⟩

    let allLemmaType : Expr := mkNary `And $ lemmaNTVs.map fun ⟨_, ltype, _⟩ => ltype

    let atype : Expr ← liftMetaM $ mkArrow dtype (mkSort levelZero)
    let aval  : Expr ← liftMetaM $ do
      withLocalDeclD `_f dtype fun x =>
        mkLambdaFVars #[x] $ allLemmaType.replace fun e => if e.isConstOf targetName then some x else none

    let lps : List Level := d.levelParams.map mkLevelParam

    let cname : Name := targetName ++ `_opaque
    let ctype : Expr ← liftMetaM $ mkAppM `Subtype #[aval]

    let allLemmaValue : Expr := mkNary `And.mk $ lemmaNTVs.map fun ⟨lname, _, _⟩ => mkConst lname lps

    let cval  : Expr ← liftMetaM $ mkAppOptM `Subtype.mk #[none, some aval, some (mkConst dname lps), some allLemmaValue]

      -- println! "[cval ] {cname} {cval}"
      -- println! "[cname] {cname} \n\n: {ctype} \n\n := {cval}"

    let cdecl : Declaration := Declaration.opaqueDecl {
      name        := cname,
      levelParams := d.levelParams,
      type        := ctype,
      value       := cval,
      isUnsafe    := false
    }

    addDeclLoud cname cdecl

    let cexpr : Expr := mkConst cname $ d.levelParams.map mkLevelParam

    addDeclLoud dname $ Declaration.defnDecl { d with
      name  := targetName,
      type  := dtype,
      value := (← liftMetaM $ mkAppM `Subtype.val #[mkConst cname lps]),
      hints := ReducibilityHints.opaque
    }

    -- TODO:
    throwError "current spot: iterate over the lemmas"
/-
      addDeclLoud lname $ updateNameTypeValue od.eqnLemmas[0]
          targetLemName
          ltype
          (← liftMetaM $ mkAppM `Subtype.property #[mkConst cname lps])

      println! "[opaque] Finished processing {targetName}!"
-/
    | _ => throwError s!"[opaqueDecl] {od.eqnLemmas.size}"


def processActionItem (actionItem : ActionItem) : PortM Unit := do
  modify λ s => { s with decl := actionItem.toDecl }
  let s ← get
  let f n := translateName s (← getEnv) n

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

  | ActionItem.eqnLemma n ln =>
    println! "[eqnLemma] {n} {ln}"
    println! "[eqnLemma] not yet handled"

  | ActionItem.simp n prio => do
    tryAddSimpLemma (f n) prio
    for eqn in (← get).name2eqns.findD n [] do
      tryAddSimpLemma (f eqn) prio

  | ActionItem.reducibility n kind => do
    -- (note: this will fail if the attribute is in a new module)
    if kind == ReducibilityStatus.reducible then
      println! "reducible {n}"
      try setAttr { name := `reducible } (f n)
      catch ex => warn ex

  | ActionItem.projection proj => do
    println! "[projection] {reprStr proj}"
    setEnv $ addProjectionFnInfo (← getEnv) (f proj.projName) (f proj.ctorName) proj.nParams proj.index proj.fromClass

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

  | ActionItem.opaqueDecl od => do
    -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/mathport/near/225031878
    -- Example:
    -- def foo.orig.type : Type := Nat → Nat
    -- def foo.orig.val  : foo.orig.type := fun (n : Nat) => n + 1

    -- def foo.orig.equation.type : Prop := ∀ n, foo.orig.val n = n + 1
    -- def foo.orig.equation.val : foo.orig.equation.type := λ n => rfl

    -- -- achieved by abstracting `foo.orig.val` from `foo.orig.equation.type`
    -- def foo.orig.equation.abstract (ϕ : foo.orig.type) : Prop := ∀ n, ϕ n = n + 1

    -- constant foo.impl : Subtype foo.orig.equation.abstract :=
    --   Subtype.mk foo.orig.val foo.orig.equation.val

    -- def foo.new : foo.orig.type := foo.impl.1
    -- def foo.new.equation : foo.orig.equation.abstract foo.new := foo.impl.2
    if od.eqnLemmas.size == 0 then throwError s!"opaqueDecl must have eqnLemmas"
    processOpaque od

  | ActionItem.decl d => do
    match d with
    | Declaration.axiomDecl ax => do
      let name := f ax.name
      let type ← translate ax.type

      if s.ignored.contains ax.name then return ()
      maybeRegisterEquation ax.name

      addDeclLoud ax.name $ Declaration.axiomDecl {
        ax with
          name := name,
          type := type
      }

    | Declaration.thmDecl thm => do
      let name := f thm.name
      let type ← translate thm.type

      if s.ignored.contains thm.name then return ()
      maybeRegisterEquation thm.name

      if s.sorries.contains thm.name ∨ (¬ (← read).proofs ∧ ¬ s.neverSorries.contains thm.name) then
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
      let name := f defn.name
      let type ← translate defn.type

      if s.ignored.contains defn.name then return ()

      let value ← translate defn.value
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
      let type ← translate ind.type

      if not (s.ignored.contains ind.name) then
        -- TODO: why do I need this nested do? Because of the scope?
        let ctors ← ind.ctors.mapM fun (ctor : Constructor) => do
          let cname := f ctor.name
          let ctype ← translate ctor.type
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
        catch ex => warn ex

      let oldRecName := mkOldRecName (f ind.name)
      let oldRec ← liftMetaM $ mkOldRecursor (f ind.name) oldRecName
      match oldRec with
      | some oldRec => do
        addDeclLoud oldRecName oldRec
        setAttr { name := `reducible } oldRecName
      | none => pure ()

    | _ => throwError (toString d.names)

end MathPort
