/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
import Lean

/-!
# Library audit: axioms and frozen statements

`lake exe audit` imports every module of the libraries `Incognita` and `Statements` and checks:

1. every declaration of `Incognita` depends only on `propext`, `Classical.choice` and
   `Quot.sound` (this catches `sorry`, `native_decide` and custom axioms);
2. for every theorem `Incognita.Statements.<rest>` (a frozen statement, proved with `sorry`), if
   the library has a declaration `Incognita.<rest>`, then it is a theorem with exactly the same
   universe parameters and the same type. Frozen statements without a proof are listed as open.

The axiom traversal and the import discipline are adapted from LMLExplore's `scripts/Axioms.lean`
(Apache 2.0).
-/

open Lean

namespace IncognitaAudit

/-- The axioms allowed in the library. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module name for a `.lean` source path, e.g. `Incognita/Foo/Bar.lean ↦ Incognita.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every `.lean` module under `dir`, recursively. -/
partial def collectLeanModules (dir : System.FilePath) : IO (Array Name) := do
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push (pathToModule entry.path)
  return acc

/-- The root module `root` and every module under the directory of the same name. -/
def libraryModules (root : Name) : IO (Array Name) :=
  return #[root] ++ (← collectLeanModules (root.toString : System.FilePath))

/-- Is `m` the module `root` or one of its submodules? -/
def underRoot (root m : Name) : Bool := m == root || root.isPrefixOf m

/-- The declarations defined in the modules under `root`. -/
def declsUnder (env : Environment) (root : Name) : Array Name :=
  let modNames := env.allImportedModuleNames
  env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if underRoot root m then acc.push declName else acc
      | none => acc
    | none => acc

/-- Memoized reachability of a disallowed axiom, as in LMLExplore's audit. -/
abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

/-- Does `c` transitively depend on an axiom outside `allowedAxioms`? -/
partial def reachesDisallowedAxiom (c : Name) : AxiomCacheM Bool := do
  if let some res := (← get).find? c then return res
  modify (·.insert c false)
  let env ← read
  let anyExpr (es : Array Expr) : AxiomCacheM Bool :=
    es.anyM fun e => e.getUsedConstants.anyM reachesDisallowedAxiom
  let res ← match env.checked.get.find? c with
    | some (.axiomInfo v) =>
        if !allowedAxioms.contains c then pure true else anyExpr #[v.type]
    | some (.defnInfo v)   => anyExpr #[v.type, v.value]
    | some (.thmInfo v)    => anyExpr #[v.type, v.value]
    | some (.opaqueInfo v) => anyExpr #[v.type, v.value]
    | some (.quotInfo _)   => pure false
    | some (.ctorInfo v)   => anyExpr #[v.type]
    | some (.recInfo v)    => anyExpr #[v.type]
    | some (.inductInfo v) =>
        if (← anyExpr #[v.type]) then pure true else v.ctors.anyM reachesDisallowedAxiom
    | none                 => pure false
  modify (·.insert c res)
  return res

/-- Is `c` a theorem in `env`? -/
def isTheorem (env : Environment) (c : Name) : Bool :=
  match env.checked.get.find? c with
  | some (.thmInfo _) => true
  | _ => false

/-- Run both checks and print the report; all strings are built inside the environment callback.
Returns the number of violations. -/
def audit (env : Environment) : IO Nat := do
  let mut violations := 0
  -- 1. Axioms of the library.
  let libDecls := declsUnder env `Incognita
  let (bad, _) := Id.run (((libDecls.filterM reachesDisallowedAxiom).run env).run {})
  for c in bad do
    IO.println s!"axioms: {c} depends on an axiom outside propext, Classical.choice, Quot.sound"
  violations := violations + bad.size
  IO.println s!"axioms: {libDecls.size} library declarations audited, {bad.size} violations"
  -- 2. Frozen statements.
  let frozen := (declsUnder env `Statements).filter fun c =>
    (`Incognita.Statements).isPrefixOf c && isTheorem env c
  let mut proved := 0
  for c in frozen do
    let target := c.replacePrefix `Incognita.Statements `Incognita
    match env.checked.get.find? c, env.checked.get.find? target with
    | some s, some t =>
      if !isTheorem env target then
        IO.println s!"frozen: {target} exists but is not a theorem (frozen statement {c})"
        violations := violations + 1
      else if s.levelParams != t.levelParams || !(s.type == t.type) then
        IO.println s!"frozen: {target} does not have the type of the frozen statement {c}"
        violations := violations + 1
      else
        IO.println s!"frozen: {c} is proved by {target}"
        proved := proved + 1
    | _, _ => IO.println s!"frozen: {c} is open (no {target} in the library)"
  IO.println s!"frozen: {frozen.size} frozen statements, {proved} proved"
  return violations

end IncognitaAudit

open IncognitaAudit in
/-- Entry point of `lake exe audit`. -/
def main : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let modules := (← libraryModules `Incognita) ++ (← libraryModules `Statements)
    let violations ← unsafe withImportModules (modules.map fun m => { module := m }) {}
      (fun env => audit env) (trustLevel := 1024)
    if violations == 0 then
      IO.println "audit: OK"
      return 0
    else
      IO.eprintln s!"audit: {violations} violations"
      return 1
  catch e =>
    IO.eprintln s!"audit: {e}"
    return 1
