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
  let d := System.FilePath.dirName outFilename
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
