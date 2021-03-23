/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Daniel Selsam
-/
import Lean

partial def Array.write {α} [Inhabited α] : ∀ (arr : Array α) (i : Nat) (x : α), Array α
| arr, i, x =>
  if i = arr.size then
    arr.push x
  else if i > arr.size then
    write (arr.push arbitrary) i x
  else
    arr.set! i x

def Array.take {α} (xs : Array α) (i : Nat) : Array α :=
  (xs.toList.take i).toArray

def Array.splitAt {α} (xs : Array α) (i : Nat) : Array α × Array α :=
  ((xs.toList.take i).toArray, (xs.toList.drop i).toArray)

def List.splitAt {α} (xs : List α) (i : Nat) : List α × List α :=
  (xs.take i, xs.drop i)

def Lean.Declaration.names : Lean.Declaration → List Lean.Name
  | axiomDecl v => [v.name]
  | defnDecl v => [v.name]
  | thmDecl v => [v.name]
  | opaqueDecl v => [v.name]
  | quotDecl => []
  | mutualDefnDecl vs => vs.map (fun v => v.name)
  | inductDecl _ _ is _ => is.map (fun i => i.name)

def Lean.Expr.replaceConstNames (f : Name → Name) (e : Expr) : Expr :=
  let x := e.replace fun
    | e@(const n us _) =>
      if f n == n then none else
        some (mkConst (f n) us)
    | _ => none
  x

def parseName (n : String) : Lean.Name :=
  (n.splitOn ".").foldl Lean.Name.mkStr Lean.Name.anonymous


namespace Std.HashMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

-- TODO: faster version
def insertWith (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
  match m.find? a with
  | none => m.insert a b
  | some c => m.insert a (merge c b)

def fromList (kvs : List (α × β)) : HashMap α β := do
  let mut hm : HashMap α β := {}
  for (k, v) in kvs do
    hm := hm.insert k v
  return hm

end Std.HashMap

def createDirectoriesIfNotExists (outFilename : String) : IO Unit := do
  match System.FilePath.parent outFilename with
  | none => throw $ IO.userError "shouldn't happen"
  | some d =>
    let s := { cmd := "mkdir", args := #["-p", d] }
    let status ← IO.Process.run s
    pure ()

section Loop

structure Loop where

variable  {β : Type u} {m : Type u → Type v} [Monad m]

@[inline]
partial def Loop.forIn (loop : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance : ForIn m Loop Unit := ⟨Loop.forIn⟩

end Loop

syntax "repeat " doSeq : doElem

macro_rules
  | `(doElem| repeat $seq) => `(doElem| for _ in Loop.mk do $seq)

syntax "while " termBeforeDo " do " doSeq : doElem

macro_rules
  | `(doElem| while $cond do $seq) =>
    `(doElem| repeat if $cond then $seq else break)

namespace IO.FS

variable [Monad m] [MonadLiftT IO m]

@[inline]
def forEachLine (fileName : String) (f : String → m Unit) : m Unit :=
  IO.FS.withFile fileName IO.FS.Mode.read fun h => do
    while (not (← h.isEof)) do
      let line := (← h.getLine).dropRightWhile λ c => c == '\n'
      if line == "" then continue else f line

end IO.FS

section AutoParam
open Lean Lean.Meta

-- TODO: ToExpr instance for Syntax
def obviouslySyntax : Expr := do
  mkAppN (mkConst `Lean.Syntax.ident) #[
    mkConst `Lean.SourceInfo.none,
    mkApp (mkConst `String.toSubstring) (toExpr "obviously"),
    toExpr `Mathlib.obviously,
    toExpr ([] : List (Prod Name (List String)))
  ]

end AutoParam

section DecodeName

open Lean

-- Awkward: this section refers to names that are created during the port
-- Alternatively, could do this more principledly in PrePort

def decodeChar (e : Expr) : MetaM Char := do
  if e.isAppOfArity `Mathlib.char.mk 2 then
    match (e.getArg! 0).natLit? with
    | some n => Char.ofNat n
    | _ => throwError "[decodeChar] failed on {e}"
  else
    throwError "[decodeChar] failed on {e}"

partial def decodeStringCore (e : Expr) : MetaM String := do
  if e.isAppOfArity `List.nil 1 then
    ""
  else if e.isAppOfArity `List.cons 3 then
    let s ← decodeStringCore (e.getArg! 2)
    let c ← decodeChar (e.getArg! 1)
    pure ⟨c :: s.data⟩
  else
    throwError "[decodeStringCore] failed on {e}"

def decodeUnsigned (e : Expr) : MetaM Nat :=
  if e.isAppOfArity `Mathlib.fin.mk 2 then
    match (e.getArg! 0).natLit? with
    | some n => n
    | _ => throwError "[decodeUInt32] failed on {e}"
  else
    throwError "[decodeUInt32] failed on {e}"

def decodeString (e : Expr) : MetaM String := do
  if e.isAppOfArity `Mathlib.string_imp.mk 1 then
    decodeStringCore (e.getArg! 0)
  else throwError "[decodeString] failed on {e}"

partial def decodeName (e : Expr) : MetaM Name := do
  if e.isAppOfArity `Mathlib.name.anonymous 0 then
    Name.anonymous
  else if e.isAppOfArity `Mathlib.name.mk_string 2 then
    Name.mkStr (← decodeName (e.getArg! 1)) (← decodeString (e.getArg! 0))
  else if e.isAppOfArity `Mathlib.name.mk_numeral 2 then
    Name.mkNum (← decodeName (e.getArg! 1)) (← decodeUnsigned (e.getArg! 0))
  else
    throwError "[decodeName] failed on {e}"

end DecodeName

section Reducibility

open Lean

def reducibilityToName (status : ReducibilityStatus) : Name :=
  match status with
  | ReducibilityStatus.reducible => `reducible
  | ReducibilityStatus.semireducible => `semireducible
  | ReducibilityStatus.irreducible => `irreducible

end Reducibility
