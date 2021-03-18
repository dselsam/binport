/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import MathPort.Util
import MathPort.ActionItem
import Lean
import Std.Data.HashSet
import Std.Data.HashMap

namespace MathPort
namespace Parser

open Lean
open Std (HashSet mkHashSet HashMap mkHashMap)

structure Context where

structure State where
  -- For reconstructing terms
  names  : Array Name  := #[Name.anonymous]
  levels : Array Level := #[levelZero]
  exprs  : Array Expr  := #[]

  -- For batching irreducible definitions into constants
  -- prevTopDecl : Name                  := Name.anonymous
  irreducibles : HashSet Name          := {}
  eqnLemmas    : HashSet (Name × Name) := {}

  -- Accumulated (ordered) action tems
  actionItems : Array ActionItem := #[]

abbrev ParseM := ReaderT Context $ StateRefT State IO

def ParseM.toIO (x : ParseM α) (ctx : Context := {}) (s : State := {}) : IO α :=
  (x ctx).run' s

private def nat2expr (i : Nat) : ParseM Expr := do
  let s ← get
  if i < s.exprs.size then return s.exprs[i]
  throw $ IO.userError s!"[nat2expr] {i} > {s.exprs.size}"

private def nat2level (i : Nat) : ParseM Level := do
  let s ← get
  if i < s.levels.size then return s.levels[i]
  throw $ IO.userError s!"[nat2level] {i} > {s.levels.size}"

private def nat2name (i : Nat) : ParseM Name := do
  let s ← get
  if i < s.names.size then return s.names[i]
  throw $ IO.userError s!"[nat2name] {i} > {s.names.size}"

private def parseNat (s : String) : ParseM Nat :=
  match s.toNat? with
  | some k => pure k
  | none   => throw $ IO.userError s!"String '{s}' cannot be converted to Nat"

private def parseBool (s : String) : ParseM Bool :=
  match s.toNat? with
  | some k =>
    if k == 1 then true
    else if k == 0 then false
    else throw $ IO.userError s!"String '{s}' cannot be converted to Bool"
  | none            => throw $ IO.userError s!"String '{s}' cannot be converted to Bool"

private def parseHints (s : String) : ParseM ReducibilityHints := do
  match s with
  | "A" => ReducibilityHints.abbrev
  | "O" => ReducibilityHints.opaque
  | _   =>
    let n ← parseNat s
    let k := n % UInt32.size
    ReducibilityHints.regular ⟨⟨k, sorryAx (Less k UInt32.size)⟩⟩

private def parseMixfixKind (kind : String) : ParseM MixfixKind :=
  match kind with
  | "prefix"    => pure MixfixKind.prefix
  | "postfix"   => pure MixfixKind.postfix
  | "infixl"    => pure MixfixKind.infixl
  | "infixr"    => pure MixfixKind.infixr
  | "singleton" => pure MixfixKind.singleton
  | _           => throw $ IO.userError s!"invalid mixfix kind {kind}"

private def str2expr (s : String)  : ParseM Expr := parseNat s >>= nat2expr
private def str2level (s : String) : ParseM Level := parseNat s >>= nat2level
private def str2name  (s : String) : ParseM Name  := parseNat s >>= nat2name


private def writeName (i : String) (n : Name) : ParseM Unit := do
  let i ← parseNat i
  modify $ λ s => { s with names := s.names.write i n }

private def writeLevel (i : String) (l : Level) : ParseM Unit := do
  let i ← parseNat i
  modify $ λ s => { s with levels := s.levels.write i l }

private def writeExpr (i : String) (e : Expr) : ParseM Unit := do
  let i ← parseNat i
  modify $ λ s => { s with exprs := s.exprs.write i e }

private def parseReducibilityStatus : String → ParseM ReducibilityStatus
| "Reducible"     => ReducibilityStatus.reducible
| "Semireducible" => ReducibilityStatus.semireducible
| "Irreducible"   => ReducibilityStatus.irreducible
| s               => throw $ IO.userError s!"unknown reducibility status {s}"

private def parseBinderInfo : String → ParseM BinderInfo
  | "#BD" => BinderInfo.default
  | "#BI" => BinderInfo.implicit
  | "#BS" =>
    -- Lean4 is missing support for strictImplicit, so we convert here
    BinderInfo.implicit -- BinderInfo.strictImplicit
  | "#BC" => BinderInfo.instImplicit
  | s     => throw $ IO.userError s!"[parseBinderInfo] unexpected: {s}"


def emit (item : ActionItem) : ParseM Unit :=
  modify fun s => { s with actionItems := s.actionItems.push item }

def processLine (line : String) : ParseM Unit := do
  let tokens := line.splitOn " "
  match tokens with
  | [] => throw $ IO.userError "[processLine] line has no tokens"
  | (t::_) => if t.isNat then processTerm tokens else processMisc tokens

  where
    processTerm (tokens : List String) : ParseM Unit := do
      match tokens with
      | (i :: "#NS" :: j :: rest)  => writeName  i $ (← str2name j).mkStr (" ".intercalate rest)
      | [i, "#NI", j, k]           => writeName  i $ (← str2name j).mkNum (← parseNat k)
      | [i, "#US", j]              => writeLevel i $ mkLevelSucc (← str2level j)
      | [i, "#UM", j₁, j₂]         => writeLevel i $ mkLevelMax (← str2level j₁) (← str2level j₂)
      | [i, "#UIM", j₁, j₂]        => writeLevel i $ mkLevelIMax (← str2level j₁) (← str2level j₂)
      | [i, "#UP", j]              => writeLevel i $ mkLevelParam (← str2name j)
      | [i, "#EV", j]              => writeExpr  i $ mkBVar (← parseNat j)
      | [i, "#ES", j]              => writeExpr  i $ mkSort (← str2level j)
      | (i :: "#EC" :: j :: us)    => writeExpr  i $ mkConst (← str2name j) (← us.mapM str2level)
      | [i, "#EA", j₁, j₂]         => writeExpr  i $ mkApp (← str2expr j₁) (← str2expr j₂)
      | [i, "#EL", bi, j₁, j₂, j₃] => writeExpr  i $ mkLambda (← str2name j₁) (← parseBinderInfo bi) (← str2expr j₂) (← str2expr j₃)
      | [i, "#EP", bi, j₁, j₂, j₃] => writeExpr  i $ mkForall (← str2name j₁) (← parseBinderInfo bi) (← str2expr j₂) (← str2expr j₃)
      | [i, "#EZ", j₁, j₂, j₃, j₄] => writeExpr  i $ mkLet (← str2name j₁) (← str2expr j₂) (← str2expr j₃) (← str2expr j₄)
      | _                          => throw $ IO.userError s!"[processTerm] unexpected '{tokens}'"

    processMisc (tokens : List String) : ParseM Unit := do
      match tokens with
      | ("#AX" :: n :: t :: ups) =>
        let (n, t, ups) ← ((← str2name n), (← str2expr t), (← ups.mapM str2name))
        emit $ ActionItem.decl $ Declaration.axiomDecl {
          name        := n,
          levelParams := ups,
          type        := t,
          isUnsafe    := false,
        }

      | ("#DEF" :: n :: thm :: h :: t :: v :: ups) =>
        let (n, h, t, v, ups) ← ((← str2name n), (← parseHints h), (← str2expr t), (← str2expr v), (← ups.mapM str2name))
        let thm := (← parseNat thm) > 0

        if thm then
          emit $ ActionItem.decl $ Declaration.thmDecl {
            name        := n,
            levelParams := ups,
            type        := t,
            value       := v
          }
        else
          emit $ ActionItem.decl $ Declaration.defnDecl {
            name        := n,
            levelParams := ups,
            type        := t,
            value       := v,
            safety      := DefinitionSafety.safe, -- TODO: confirm only safe things are being exported
            hints       := h,
          }

      | ("#IND" :: nps :: n :: t :: nis :: rest) =>
        let (nps, n, t, nis) ← ((← parseNat nps), (← str2name n), (← str2expr t), (← parseNat nis))
        let (is, ups) := rest.splitAt (2 * nis)
        let lparams ← ups.mapM str2name
        let ctors ← parseIntros is
        emit $ ActionItem.decl $ Declaration.inductDecl lparams nps [{
          name := n,
          type := t,
          ctors := ctors
          }] false

      | ["#QUOT"]                                => pure ()

      | ("#MIXFIX" :: kind :: n :: prec :: tok)  => emit $ ActionItem.mixfix (← parseMixfixKind kind) (← str2name n) (← parseNat prec) (" ".intercalate tok)

      | ["#PRIVATE", pretty, real]               => emit $ ActionItem.private (← str2name pretty) (← str2name real)
      | ["#PROTECTED", n]                        => emit $ ActionItem.protected (← str2name n)

      | ("#POS_INFO" :: _)                       => pure ()

      -- TODO: look at the 'deleted' bit
      | ("#ATTR" :: a :: p :: n :: _ :: rest)    => do
        let (attrName, p, n) := (← str2name a, ← parseNat p, ← str2name n)
        if attrName == "simp" then
          emit $ ActionItem.simp n p
        else if attrName == "reducibility" then
          match rest with
          | [status] => do
            let status ← parseReducibilityStatus status
            if status == ReducibilityStatus.irreducible then
              modify fun s => { s with irreducibles := s.irreducibles.insert n }
            emit $ ActionItem.reducibility n status
          | _        => throw $ IO.userError s!"[reducibility] expected name"
        else
          pure ()

      | ["#CLASS", c]                => emit $ ActionItem.class (← str2name c)
      | ["#CLASS_INSTANCE", c, i, p] => emit $ ActionItem.instance (← str2name c) (← str2name i) (← parseNat p)

      | ("#CLASS_TRACK_ATTR" :: _)               => pure ()
      | ("#AUXREC" :: _)                         => pure ()
      | ("#NEW_NAMESPACE" :: _)                  => pure ()
      | ("#NONCOMPUTABLE" :: _)                  => pure ()
      | ("#NOCONF" :: _)                         => pure ()
      | ("#TOKEN" :: _)                          => pure ()
      | ("#USER_ATTR" :: _)                      => pure ()

      | ["#EQUATION", n, ln]                     => do
        let (n, ln) := (← str2name n, ← str2name ln)
        modify fun s => { s with eqnLemmas := s.eqnLemmas.insert (n, ln) }
        emit $ ActionItem.eqnLemma n ln

      | ["#PROJECTION", proj, mk, nParams, i, ii] => do
        emit $ ActionItem.projection {
          projName     := ← str2name proj,
          ctorName     := ← str2name mk,
          nParams      := ← parseNat nParams,
          index        := ← parseNat i,
          fromClass    := ← parseBool ii
        }

      | ("#EXPORT_DECL" :: currNs :: ns :: nsAs :: hadExplicit :: nRenames :: rest) => do
        let rest := rest.toArray
        let nRenames ← parseNat nRenames
        let mut renames := #[]
        for i in [:nRenames] do
          let n1 ← str2name rest[2*i]
          let n2 ← str2name rest[2*i+1]
          renames := renames.push (n1, n2)

        let nExcepts ← parseNat rest[2*nRenames]
        let offset := (2 * nRenames + 1)
        let mut exceptNames := #[]
        for i in [:nExcepts] do
          exceptNames := exceptNames.push $ ← str2name rest[offset + i]

        let exportDecl : ExportDecl := {
          currNs := (← str2name currNs),
          ns     := (← str2name ns),
          nsAs        := (← str2name nsAs),
          hadExplicit := (← parseNat hadExplicit) > 0,
          renames     := renames,
          exceptNames := exceptNames
        }
        emit $ ActionItem.export exportDecl

      | _ =>
        println! "[processLine] unexpected case: '{line}'\n{tokens}"
        pure ()

    parseIntros : List String → ParseM (List Constructor)
      | (n :: t :: is) => do
        let rest ← parseIntros is
        pure $ { name := (← str2name n), type := ← str2expr t } :: rest

      | _              => []

def collectOpaque : ParseM (Array ActionItem) := do
  let mut newItems   : Array ActionItem := #[]
  let mut decl2index : HashMap Name Nat := {}

  for actionItem in (← get).actionItems do
    match actionItem with
    | ActionItem.decl d =>
      let name := d.names.head!
      if (← get).opaqueDecls.contains name then
        println! "[opaque] CREATE {name}"
        decl2index := decl2index.insert name newItems.size
        newItems := newItems.push $ ActionItem.opaqueDecl (OpaqueDeclaration.mk d #[])
      else
        match isEquationLemma? name with
        | some pfix =>
          match decl2index.find? pfix with
          | some i => do
            newItems := newItems.modify i fun
              | ActionItem.opaqueDecl od => ActionItem.opaqueDecl ⟨od.decl, od.eqnLemmas.push d⟩
              | _ => panic! "should not happen"
            println! "[opaque] ADD {pfix} {name}"
          | _      => newItems := newItems.push actionItem
        | _ => newItems := newItems.push actionItem
    | _ => newItems := newItems.push actionItem

  return newItems

def parseExportFile (h : IO.FS.Handle) : IO (Array ActionItem) := ParseM.toIO $ do
  -- discard imports
  let _ ← h.getLine
  -- first pass
  while (not (← h.isEof)) do
    let line := (← h.getLine).dropRightWhile λ c => c == '\n'
    if line == "" then continue
    processLine line
  -- second pass
  collectOpaque

end Parser

export Parser (parseExportFile)

end MathPort
