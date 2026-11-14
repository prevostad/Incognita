/-
Copyright (c) 2026 Incognita contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Incognita contributors
-/
import Lean

/-!
# Audit of the library and of the frozen statements

Run from the repository root. The executable `needs` the libraries `Incognita` and `Statements`,
so `lake exe audit` builds them first.

```
lake exe audit [--check] [--no-replay]   check everything; the default, run by CI
lake exe audit --new-locks               write the missing Statements/<P>/<name>.lock files
lake exe audit --refresh-new-locks       (re)write the locks absent from origin/main
lake exe audit --status                  one line "<P> <name> open|proved|refuted" per statement
lake exe audit --dump <statement>        print the exact bytes hashed into the statement's lock
lake exe audit --selftest                check the SHA-256 implementation on test vectors
```

## Frozen statements

A *frozen statement* is a theorem `Incognita.Statements.<P>.<name>` of a module
`Statements.<P>.…` (file under `Statements/<P>/`), where `<P>` is the paper's namespace (`P001`).
Its proof is `sorry`. `Statements/` holds nothing else, apart from the auxiliary declarations Lean
generates (`match_n`, `_proof_n`, equation lemmas…).

* It is **proved** iff the library has a theorem `Incognita.<P>.<name>`, defined in a module whose
  root is `Incognita`, with the same universe parameters and the same type, whose axioms are only
  `propext`, `Classical.choice` and `Quot.sound`.
* It is **refuted** iff the library has, under the same conditions, a theorem
  `Incognita.<P>.<name>_false` of type `¬ T`, where `T` is the frozen type.
* Otherwise it is **open**.

"The same type" means `Expr` equality (alpha-equivalence), or, failing that, the same canonical
serialisation (below), which also ignores metadata.

## Locks

`Statements/<P>/<name>.lock` freezes the statement and every declaration of the project it rests
on. It records the SHA-256 of a canonical S-expression serialisation (printed by `--dump`):

* the constants hashed are those reachable from the statement's type through types, values of
  definitions and opaque constants, and constructors of inductive types, **stopping at constants
  whose module root is neither `Incognita` nor `Statements`** (Mathlib, LML, LMLExplore, Tau Ceti:
  fixed by `lake-manifest.json`, a human-owned file), which appear by name only;
* each is serialised with its kind, name, universe parameters and type; definitions and opaque
  constants also with their value (and safety); theorems with their type only; inductive types
  with their parameters, indices, mutual block and constructors' types;
* expressions: bound variables by de Bruijn index, constants with their universe levels, binder
  information but no binder names, metadata erased, projections with their structure name,
  literals; atoms are length-prefixed (`9:Incognita`), naturals are written `#n`;
* constants are sorted by name (`Name.cmp`), one per line, after the line `incognita-lock 1`.

`--new-locks` never touches an existing lock. A pull request that adds a statement and then changes
it (answering a review) regenerates the locks it added with `--refresh-new-locks`: every frozen
statement whose lock file is not on `origin/main` (read with `git ls-tree`) gets its lock written
or rewritten, and the lock files absent from `origin/main` that match no frozen statement are
deleted. Locks on `origin/main` are never touched, so CI still fails on a changed frozen statement.

## `--check`

Fails if: a declaration of `Incognita/` depends on an axiom other than the three standard ones, or
is `unsafe`, or lies in the namespace `Incognita.Statements`, or a module of `Incognita/` imports
`Statements`; `Statements/` holds anything but frozen statements and generated auxiliaries; a
frozen statement's type uses a declaration of `Statements/` (a proof in `Incognita/` could never
have the same type); a frozen statement has no lock, or its lock differs from the one
`--new-locks` would write; a lock has no statement; `Incognita.<P>.<name>` (or `_false`) exists but
is not a valid proof (refutation); a statement is both proved and refuted; a proof marker
`catalogue/results/<P>-<name>.toml` names a statement that is not proved (or not refuted, if the
marker has the line `status = "refuted"`); the kernel rejects a declaration of `Incognita/` or
`Statements/` when they are replayed (`Lean.Kernel.Environment.replay`) on top of their
dependencies (skipped with `--no-replay`).

The axiom traversal and the import discipline are adapted from LMLExplore's `scripts/Axioms.lean`
(Apache 2.0). Modules are imported at the private level (`withImportModules`), so the bodies of
non-exposed definitions and of theorems are visible.
-/

open Lean

namespace IncognitaAudit

/-! ## SHA-256 (FIPS 180-4) -/

namespace SHA256

/-- The round constants. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value. -/
def initial : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Process the 64-byte block of `data` starting at `off`. -/
def compress (h : Array UInt32) (data : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let byte (j : Nat) : UInt32 := (data.get! (off + 4 * i + j)).toUInt32
    w := w.push ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut k := h[7]!
  for i in [0:64] do
    let bigS1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := k + bigS1 + ch + roundConstants[i]! + w[i]!
    let bigS0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bigS0 + maj
    k := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + k]

/-- The hexadecimal digits. -/
def hexChars : Array Char := "0123456789abcdef".toList.toArray

/-- A word as eight hexadecimal digits. -/
def hex32 (x : UInt32) : String := Id.run do
  let mut s := ""
  for i in [0:8] do
    let nibble := ((x >>> UInt32.ofNat (28 - 4 * i)) &&& 0xf).toNat
    s := s.push hexChars[nibble]!
  return s

/-- The SHA-256 digest of `msg`, in lowercase hexadecimal. -/
def hashHex (msg : ByteArray) : String := Id.run do
  let len := msg.size
  let mut data := msg.push 0x80
  while data.size % 64 != 56 do
    data := data.push 0
  let bits := len * 8
  for i in [0:8] do
    data := data.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  let mut h := initial
  for blk in [0:data.size / 64] do
    h := compress h data (64 * blk)
  return h.foldl (fun s x => s ++ hex32 x) ""

/-- Standard test vectors (FIPS 180-4 examples, NIST CSRC). -/
def testVectors : List (String × String) := [
  ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
  ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
  ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")]

end SHA256

/-! ## Canonical serialisation -/

/-- The serialisation monad: the output so far, or an error. -/
abbrev SerM := StateT String (Except String)

@[inline] def emit (s : String) : SerM Unit := modify (· ++ s)

/-- A length-prefixed atom, `<UTF-8 length>:<bytes>`. -/
def emitAtom (s : String) : SerM Unit := emit s!"{s.utf8ByteSize}:{s}"

def emitNat (n : Nat) : SerM Unit := emit s!" #{n}"

def emitBool (b : Bool) : SerM Unit := emitNat (if b then 1 else 0)

def emitName (n : Name) : SerM Unit := do
  emit "(name"
  for c in n.components do
    match c with
    | .str _ s =>
      emit " "
      emitAtom s
    | .num _ k => emit s!" #{k}"
    | .anonymous => pure ()
  emit ")"

partial def emitLevel : Level → SerM Unit
  | .zero => emit "(lzero)"
  | .succ l => do
    emit "(lsucc "
    emitLevel l
    emit ")"
  | .max a b => do
    emit "(lmax "
    emitLevel a
    emit " "
    emitLevel b
    emit ")"
  | .imax a b => do
    emit "(limax "
    emitLevel a
    emit " "
    emitLevel b
    emit ")"
  | .param n => do
    emit "(lparam "
    emitName n
    emit ")"
  | .mvar _ => throw "universe level metavariable"

def binderInfoAtom : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def emitExpr : Expr → SerM Unit
  | .bvar i => emit s!"(bvar #{i})"
  | .fvar _ => throw "free variable"
  | .mvar _ => throw "metavariable"
  | .sort l => do
    emit "(sort "
    emitLevel l
    emit ")"
  | .const n ls => do
    emit "(const "
    emitName n
    for l in ls do
      emit " "
      emitLevel l
    emit ")"
  | .app f a => do
    emit "(app "
    emitExpr f
    emit " "
    emitExpr a
    emit ")"
  | .lam _ t b bi => do
    emit "(lam "
    emitAtom (binderInfoAtom bi)
    emit " "
    emitExpr t
    emit " "
    emitExpr b
    emit ")"
  | .forallE _ t b bi => do
    emit "(pi "
    emitAtom (binderInfoAtom bi)
    emit " "
    emitExpr t
    emit " "
    emitExpr b
    emit ")"
  | .letE _ t v b nonDep => do
    emit "(let "
    emitExpr t
    emit " "
    emitExpr v
    emit " "
    emitExpr b
    emitBool nonDep
    emit ")"
  | .lit (.natVal n) => emit s!"(natlit #{n})"
  | .lit (.strVal s) => do
    emit "(strlit "
    emitAtom s
    emit ")"
  | .mdata _ e => emitExpr e
  | .proj s i e => do
    emit "(proj "
    emitName s
    emitNat i
    emit " "
    emitExpr e
    emit ")"

/-- The serialisation of an expression alone. -/
def serExpr (e : Expr) : Except String String := do
  let ((), s) ← (emitExpr e).run ""
  return s

/-- The kernel's view of the environment (all private data: modules are imported at the private
level). -/
def findConst (env : Environment) (c : Name) : Option ConstantInfo := env.checked.get.find? c

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def emitHeader (ci : ConstantInfo) : SerM Unit := do
  emit s!"({kindName ci} "
  emitName ci.name
  emit " (lparams"
  for u in ci.levelParams do
    emit " "
    emitName u
  emit ") "
  emitExpr ci.type

def safetyAtom : DefinitionSafety → String
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

def quotAtom : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def emitNames (tag : String) (ns : List Name) : SerM Unit := do
  emit s!" ({tag}"
  for n in ns do
    emit " "
    emitName n
  emit ")"

/-- The serialisation of a constant hashed into a lock. Theorems: type only. -/
def emitConst (env : Environment) (ci : ConstantInfo) : SerM Unit := do
  emitHeader ci
  match ci with
  | .axiomInfo v => emitBool v.isUnsafe
  | .defnInfo v =>
    emit " "
    emitExpr v.value
    emit " "
    emitAtom (safetyAtom v.safety)
  | .thmInfo _ => pure ()
  | .opaqueInfo v =>
    emit " "
    emitExpr v.value
    emitBool v.isUnsafe
  | .quotInfo v =>
    emit " "
    emitAtom (quotAtom v.kind)
  | .inductInfo v =>
    emitNat v.numParams
    emitNat v.numIndices
    emitNames "all" v.all
    emit " (ctors"
    for c in v.ctors do
      match findConst env c with
      | some (.ctorInfo cv) =>
        emit " (ctor "
        emitName c
        emit " "
        emitExpr cv.type
        emitNat cv.numFields
        emit ")"
      | _ => throw s!"constructor {c} of {ci.name} not found"
    emit ")"
    emitNat v.numNested
    emitBool v.isRec
    emitBool v.isUnsafe
    emitBool v.isReflexive
  | .ctorInfo v =>
    emit " "
    emitName v.induct
    emitNat v.cidx
    emitNat v.numParams
    emitNat v.numFields
    emitBool v.isUnsafe
  | .recInfo v =>
    emitNames "all" v.all
    emitNat v.numParams
    emitNat v.numIndices
    emitNat v.numMotives
    emitNat v.numMinors
    emitBool v.k
    emitBool v.isUnsafe
  emit ")"

/-! ## Modules -/

/-- The module name for a `.lean` source path, e.g. `Incognita/Foo/Bar.lean ↦ Incognita.Foo.Bar`. -/
def pathToModule (p : System.FilePath) : Name :=
  (p.withExtension "").components.foldl (fun n s => Name.mkStr n s) Name.anonymous

/-- Every file with extension `ext` under `dir`, recursively, sorted. -/
partial def collectFiles (dir : System.FilePath) (ext : String) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let mut acc := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      acc := acc ++ (← collectFiles entry.path ext)
    else if entry.path.extension == some ext then
      acc := acc.push entry.path
  return acc.qsort (fun a b => a.toString < b.toString)

/-- The root module `root` and every module under the directory of the same name. -/
def libraryModules (root : Name) : IO (Array Name) :=
  return #[root] ++ (← collectFiles (root.toString : System.FilePath) "lean").map pathToModule

/-- A path with forward slashes. -/
def slashPath (p : System.FilePath) : String := p.toString.replace "\\" "/"

/-- The module defining `c`. -/
def moduleOf? (env : Environment) (c : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? c
  env.header.moduleNames[idx.toNat]?

/-- Is `m` a module of the project (root `Incognita` or `Statements`)? -/
def isProjectModule (m : Name) : Bool := m.getRoot == `Incognita || m.getRoot == `Statements

/-! ## Axioms -/

/-- The axioms allowed in the library. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Memoized reachability of a disallowed axiom, as in LMLExplore's audit. -/
abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

/-- Does `c` transitively depend on an axiom outside `allowedAxioms`? -/
partial def reachesDisallowedAxiom (c : Name) : AxiomCacheM Bool := do
  if let some res := (← get).find? c then return res
  modify (·.insert c false)
  let env ← read
  let anyExpr (es : Array Expr) : AxiomCacheM Bool :=
    es.anyM fun e => e.getUsedConstants.anyM reachesDisallowedAxiom
  let res ← match findConst env c with
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
    | none                 => pure true
  modify (·.insert c res)
  return res

/-- The non-standard axioms `c` depends on (for the report). -/
partial def badAxiomsOf (env : Environment) (c : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack := #[c]
  let mut out := #[]
  while !stack.isEmpty do
    let d := stack.back!
    stack := stack.pop
    if seen.contains d then continue
    seen := seen.insert d
    match findConst env d with
    | some (.axiomInfo _) => if !allowedAxioms.contains d then out := out.push d
    | some ci =>
      let es := match ci with
        | .defnInfo v | .thmInfo v | .opaqueInfo v => #[v.type, v.value]
        | .inductInfo v => #[v.type] ++ v.ctors.toArray.map (mkConst ·)
        | _ => #[ci.type]
      for e in es do
        for u in e.getUsedConstants do
          if !seen.contains u then stack := stack.push u
    | none => out := out.push d
  return out

/-! ## Frozen statements -/

/-- Is `s` the string `pre` followed by at least one digit and only digits? -/
def isNumbered (pre s : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.toList.drop pre.length).all Char.isDigit

/-- Name components Lean generates for auxiliary declarations. -/
def generatedComponent (s : String) : Bool :=
  s.startsWith "_" || isNumbered "match_" s || isNumbered "proof_" s || isNumbered "eq_" s ||
    ["eq_def", "eq_unfold", "induct", "induct_unfolding", "mutual_induct", "fun_cases",
      "fun_cases_unfolding", "splitter", "congr_simp"].contains s

/-- The last string component of a name. -/
def lastString? : Name → Option String
  | .str _ s => some s
  | .num p _ => lastString? p
  | .anonymous => none

/-- Is `c` an auxiliary declaration generated by Lean (matchers, nested proofs, equation lemmas)? -/
def isGenerated (c : Name) : Bool :=
  (lastString? c).any generatedComponent ||
    c.components.any fun x => match x with
      | .str _ s => isNumbered "match_" s
      | _ => false

/-- A generated name must hang off an existing declaration (`foo.match_1` needs `foo`), unless
it has an internal component (`_proof_1`, `_auxLemma`): a frozen statement cannot hide as
`Incognita.Statements.P001.induct`. -/
def generatedOwnerOk (env : Environment) (c : Name) : Bool :=
  c.components.any (fun x => match x with
    | .str _ s => s.startsWith "_"
    | _ => false) ||
  match c with
  | .str p _ => (findConst env p).isSome
  | .num p _ => (findConst env p).isSome
  | .anonymous => false

/-- Declarations of `Statements/` that predate v3 and are tolerated: the placeholder of
`Statements/Basic.lean`. Remove this exemption when that file is deleted (an owner PR). -/
def legacyExempt : List Name := [`Incognita.Statements.placeholder]

/-- A frozen statement. -/
structure Frozen where
  /-- `Incognita.Statements.<P>.<name>`. -/
  decl : Name
  /-- The paper namespace `<P>`. -/
  paper : String
  /-- `<name>`. -/
  short : Name
  /-- The module declaring it. -/
  module : Name

/-- `<name>` as a string (file names, status lines). -/
def Frozen.shortStr (f : Frozen) : String := f.short.toString (escape := false)

/-- `Incognita.<P>.<name>`. -/
def Frozen.proofName (f : Frozen) : Name :=
  (`Incognita ++ Name.mkSimple f.paper) ++ f.short

/-- `Incognita.<P>.<name>_false`. -/
def Frozen.refutationName (f : Frozen) : Name := f.proofName.appendAfter "_false"

def Frozen.lockPath (f : Frozen) : String := s!"Statements/{f.paper}/{f.shortStr}.lock"

def Frozen.markerPath (f : Frozen) : String := s!"catalogue/results/{f.paper}-{f.shortStr}.toml"

/-- The name from a list of components. -/
def ofComponents (cs : List Name) : Name := cs.foldl (· ++ ·) .anonymous

/-- `c`, declared in module `m`, as a frozen statement, if it has the right shape. -/
def frozenOf? (c m : Name) (ci : ConstantInfo) : Option Frozen :=
  match ci, c.components, m.components with
  | .thmInfo _, `Incognita :: `Statements :: p :: rest@(_ :: _), `Statements :: p' :: _ =>
    match p with
    | .str .anonymous ps =>
      if p == p' && !c.isInternal && !isPrivateName c then
        some { decl := c, paper := ps, short := ofComponents rest, module := m }
      else none
    | _ => none
  | _, _, _ => none

/-- Is a string safe as a single path component? -/
def safeFileComponent (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "." &&
    !s.toList.any (fun ch => ch == '/' || ch == '\\' || ch == '\n' || ch == ' ')

/-! ## Locks -/

/-- The constants hashed into the lock of `stmt`, sorted by name. -/
def lockClosure (env : Environment) (stmt : Name) : Except String (Array Name) := do
  let mut seen : NameSet := {}
  let mut stack := #[stmt]
  let mut out := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some m := moduleOf? env c | throw s!"{c} belongs to no imported module"
    if !isProjectModule m then continue
    let some ci := findConst env c | throw s!"{c} not found"
    out := out.push c
    let mut es : Array Expr := #[ci.type]
    let mut refs : Array Name := #[]
    match ci with
    | .defnInfo v => es := es.push v.value
    | .opaqueInfo v => es := es.push v.value
    | .inductInfo v =>
      refs := refs ++ v.all.toArray ++ v.ctors.toArray
      for k in v.ctors do
        match findConst env k with
        | some (.ctorInfo kv) => es := es.push kv.type
        | _ => throw s!"constructor {k} of {c} not found"
    | .ctorInfo v => refs := refs.push v.induct
    | .recInfo v => refs := refs ++ v.all.toArray
    | _ => pure ()
    for e in es do
      refs := refs ++ e.getUsedConstants
    for r in refs do
      if !seen.contains r then stack := stack.push r
  return out.qsort (fun a b => Name.cmp a b == .lt)

/-- The bytes hashed into the lock of `stmt`, and the hashed constants with their kinds. -/
def lockDump (env : Environment) (stmt : Name) : Except String (String × Array (String × Name)) := do
  let consts ← lockClosure env stmt
  let mut s := "incognita-lock 1\n"
  let mut kinds := #[]
  for c in consts do
    let some ci := findConst env c | throw s!"{c} not found"
    let ((), s') ← (emitConst env ci).run s
    s := s' ++ "\n"
    kinds := kinds.push (kindName ci, c)
  return (s, kinds)

/-- The text of the lock file of `stmt`. -/
def lockText (env : Environment) (stmt : Name) : Except String String := do
  let (dump, kinds) ← lockDump env stmt
  let digest := SHA256.hashHex dump.toUTF8
  let mut t := "# Lock of a frozen statement, written by `lake exe audit --new-locks`. " ++
    "Never edit or delete it.\n"
  t := t ++ "format 1\n" ++ s!"statement {stmt}\n" ++ s!"sha256 {digest}\n"
  for (k, c) in kinds do
    t := t ++ s!"constant {k} {c}\n"
  return t

/-- Line endings, trailing spaces and trailing blank lines do not count. -/
def normalizeText (s : String) : String :=
  let blank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'
  let lines := (s.splitOn "\n").map fun l =>
    String.ofList (l.toList.reverse.dropWhile blank).reverse
  let lines := (lines.reverse.dropWhile (·.isEmpty)).reverse
  "\n".intercalate lines

/-! ## Status of a statement -/

/-- What the library says about a frozen statement. -/
inductive Verdict where
  | open
  | proved
  | refuted
  deriving BEq, Inhabited

def Verdict.toString : Verdict → String
  | .open => "open"
  | .proved => "proved"
  | .refuted => "refuted"

/-- Are two types the same: alpha-equivalent, or with the same canonical serialisation? -/
def sameType (a b : Expr) : Bool :=
  a == b || match serExpr a, serExpr b with
    | .ok x, .ok y => x == y
    | _, _ => false

/-- Check that `target` is a valid proof of `expected` (with universe parameters `lps`): `none` if
it does not exist, `some (.ok ())` if it is valid, `some (.error why)` otherwise. -/
def checkProof (env : Environment) (badAxiom : Name → Bool) (target : Name) (lps : List Name)
    (expected : Expr) : Option (Except String Unit) := do
  let ci ← findConst env target
  let some m := moduleOf? env target | some (.error "it belongs to no module")
  if m.getRoot != `Incognita then
    return .error s!"it is declared in {m}, outside Incognita/"
  let .thmInfo _ := ci | return .error s!"it is a {kindName ci}, not a theorem"
  if ci.levelParams != lps then
    return .error s!"its universe parameters {ci.levelParams} differ from {lps}"
  if !sameType ci.type expected then
    return .error "its type differs from the frozen type"
  if badAxiom target then
    return .error s!"it depends on non-standard axioms {badAxiomsOf env target}"
  return .ok ()

/-! ## The audit -/

/-- Mutable report. -/
structure Report where
  errors : Array String := #[]
  notes : Array String := #[]

/-- Everything the audit computes from the environment. -/
structure Analysis where
  frozen : Array Frozen := #[]
  verdicts : Array Verdict := #[]
  report : Report := {}
  libraryDecls : Nat := 0

/-- Analyse the imported environment: library, `Statements/` content, statuses. -/
def analyse (env : Environment) : Analysis := Id.run do
  let mut errors : Array String := #[]
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  -- Library declarations and Statements declarations, by module.
  let mut libDecls : Array Name := #[]
  let mut frozen : Array Frozen := #[]
  for m in names, d in datas do
    if m.getRoot == `Incognita then
      for imp in d.imports do
        if imp.module.getRoot == `Statements || imp.module.getRoot == `Exploration then
          errors := errors.push s!"library: module {m} imports {imp.module}"
      for c in d.constNames do
        libDecls := libDecls.push c
        if (`Incognita.Statements).isPrefixOf c then
          errors := errors.push
            s!"library: {c} (in {m}) lies in the namespace Incognita.Statements, reserved to Statements/"
    else if m.getRoot == `Statements then
      for c in d.constNames do
        if legacyExempt.contains c then continue
        let some ci := findConst env c | continue
        if isGenerated c && generatedOwnerOk env c then continue
        match frozenOf? c m ci with
        | some f => frozen := frozen.push f
        | none =>
          errors := errors.push (s!"statements: {c} ({kindName ci}, in {m}) is not allowed: " ++
            "Statements/<P>/ holds only theorems Incognita.Statements.<P>.<name> (frozen statements)")
  -- Unsafe declarations (the compiler generates unsafe `_impl` helpers: those are allowed).
  for c in libDecls do
    if let some ci := findConst env c then
      if ci.isUnsafe && !isGenerated c then errors := errors.push s!"library: {c} is unsafe"
  -- Axioms of the library.
  let (badList, cache) := Id.run (((libDecls.filterM reachesDisallowedAxiom).run env).run {})
  for c in badList do
    errors := errors.push
      s!"library: {c} depends on non-standard axioms {badAxiomsOf env c} (only propext, Classical.choice, Quot.sound are allowed)"
  let badAxiom (c : Name) : Bool := (cache.find? c).getD true
  -- Frozen statements: shape, statuses.
  frozen := frozen.qsort fun a b =>
    a.paper < b.paper || (a.paper == b.paper && Name.cmp a.short b.short == .lt)
  let mut verdicts := #[]
  for f in frozen do
    let some ci := findConst env f.decl | continue
    if !safeFileComponent f.paper || !safeFileComponent f.shortStr then
      errors := errors.push s!"statements: {f.decl} has a name that cannot be a file name"
    for u in ci.type.getUsedConstants do
      if let some m := moduleOf? env u then
        if m.getRoot == `Statements then
          errors := errors.push (s!"statements: the type of {f.decl} uses {u}, declared in {m}: " ++
            "a proof in Incognita/ could never have the same type; move it to the library")
    let proof := checkProof env badAxiom f.proofName ci.levelParams ci.type
    let refutation := checkProof env badAxiom f.refutationName ci.levelParams (mkNot ci.type)
    if let some (.error why) := proof then
      errors := errors.push s!"proofs: {f.proofName} does not prove {f.decl}: {why}"
    if let some (.error why) := refutation then
      errors := errors.push s!"proofs: {f.refutationName} does not refute {f.decl}: {why}"
    let isProved := proof matches some (.ok ())
    let isRefuted := refutation matches some (.ok ())
    if isProved && isRefuted then
      errors := errors.push s!"proofs: {f.decl} is both proved and refuted"
    verdicts := verdicts.push (if isProved then .proved else if isRefuted then .refuted else .open)
  return { frozen, verdicts, report := { errors }, libraryDecls := libDecls.size }

/-- Lock files on disk: path ↦ content. -/
def readLocks : IO (Array (String × String)) := do
  let files ← collectFiles "Statements" "lock"
  files.mapM fun p => return (slashPath p, ← IO.FS.readFile p)

/-- Proof markers on disk: path ↦ content. -/
def readMarkers : IO (Array (String × String)) := do
  let files ← collectFiles ("catalogue" / "results") "toml"
  files.mapM fun p => return (slashPath p, ← IO.FS.readFile p)

/-- Does a marker ask for a refutation (a line `status = "refuted"`)? -/
def markerWantsRefuted (content : String) : Bool :=
  (content.splitOn "\n").any fun l =>
    (l.replace " " "").replace "\t" "" == "status=\"refuted\""

/-- `--check`: everything. Returns the error messages; prints notes. -/
def check (env : Environment) (locks markers : Array (String × String)) : IO (Array String) := do
  let a := analyse env
  let mut errors := a.report.errors
  -- Locks.
  let mut expectedLocks : Std.HashSet String := {}
  for f in a.frozen do
    expectedLocks := expectedLocks.insert f.lockPath
    match locks.find? (·.1 == f.lockPath) with
    | none =>
      errors := errors.push
        s!"locks: {f.decl} has no lock {f.lockPath} (run lake exe audit --new-locks)"
    | some (_, content) =>
      match lockText env f.decl with
      | .error e => errors := errors.push s!"locks: cannot serialise {f.decl}: {e}"
      | .ok expected =>
        if normalizeText content != normalizeText expected then
          errors := errors.push (s!"locks: {f.lockPath} does not match {f.decl}: the statement " ++
            "or a declaration it rests on changed (lake exe audit --dump shows what is hashed)")
  for (p, _) in locks do
    if !expectedLocks.contains p then
      errors := errors.push s!"locks: {p} matches no frozen statement (removed or renamed?)"
  -- Proof markers.
  let mut nMarkers := 0
  for (p, content) in markers do
    match (a.frozen.zip a.verdicts).find? (fun (f, _) => f.markerPath == p) with
    | none => errors := errors.push s!"markers: {p} names no frozen statement"
    | some (f, v) =>
      nMarkers := nMarkers + 1
      let wanted := if markerWantsRefuted content then Verdict.refuted else .proved
      if v != wanted then
        errors := errors.push
          s!"markers: {p} says {f.decl} is {wanted.toString}, but it is {v.toString}"
  let count (v : Verdict) := (a.verdicts.filter (· == v)).size
  IO.println s!"library: {a.libraryDecls} declarations of Incognita/ audited"
  IO.println (s!"statements: {a.frozen.size} frozen ({count .proved} proved, " ++
    s!"{count .refuted} refuted, {count .open} open), {locks.size} locks, {nMarkers} proof markers")
  for (f, v) in a.frozen.zip a.verdicts do
    IO.println s!"  {f.paper} {f.shortStr} {v.toString}"
  return errors

/-- `--status`. -/
def status (env : Environment) : IO Unit := do
  let a := analyse env
  for (f, v) in a.frozen.zip a.verdicts do
    IO.println s!"{f.paper} {f.shortStr} {v.toString}"
  for e in a.report.errors do
    IO.eprintln s!"warning: {e}"

/-- `--new-locks`: write the missing lock files only. Returns the exit code. -/
def newLocks (env : Environment) : IO UInt32 := do
  let a := analyse env
  let mut failures := 0
  for f in a.frozen do
    let path : System.FilePath := f.lockPath
    if ← path.pathExists then continue
    match lockText env f.decl with
    | .error e =>
      IO.eprintln s!"cannot lock {f.decl}: {e}"
      failures := failures + 1
    | .ok t =>
      if let some dir := path.parent then IO.FS.createDirAll dir
      IO.FS.writeFile path t
      IO.println s!"wrote {f.lockPath}"
  return if failures == 0 then 0 else 1

/-- The lock files of `origin/main` (`git ls-tree`), or `none` if git fails (no `origin/main`). -/
def mainLocks : IO (Option (Std.HashSet String)) := do
  let out ← IO.Process.output
    { cmd := "git", args := #["ls-tree", "-r", "--name-only", "origin/main", "--", "Statements"] }
  if out.exitCode != 0 then return none
  let mut s : Std.HashSet String := {}
  for l in out.stdout.splitOn "\n" do
    if l.endsWith ".lock" then s := s.insert l
  return some s

/-- `--refresh-new-locks`: write or rewrite the lock of every frozen statement whose lock is not on
`origin/main`, and delete the lock files absent from `origin/main` that match no frozen statement.
Returns the exit code. -/
def refreshNewLocks (env : Environment) (onMain : Std.HashSet String) : IO UInt32 := do
  let a := analyse env
  let mut failures := 0
  let mut expected : Std.HashSet String := {}
  for f in a.frozen do
    expected := expected.insert f.lockPath
    if onMain.contains f.lockPath then continue
    match lockText env f.decl with
    | .error e =>
      IO.eprintln s!"cannot lock {f.decl}: {e}"
      failures := failures + 1
    | .ok t =>
      let path : System.FilePath := f.lockPath
      let old : Option String ←
        if (← path.pathExists) then
          some <$> IO.FS.readFile path
        else
          pure none
      if old.map normalizeText == some (normalizeText t) then continue
      if let some dir := path.parent then IO.FS.createDirAll dir
      IO.FS.writeFile path t
      let verb := if old.isSome then "rewrote" else "wrote"
      IO.println s!"{verb} {f.lockPath}"
  for (p, _) in ← readLocks do
    if !expected.contains p && !onMain.contains p then
      IO.FS.removeFile (System.FilePath.mk p)
      IO.println s!"removed {p} (no frozen statement)"
  return if failures == 0 then 0 else 1

/-- Resolve the statement named on the command line. -/
def resolveStatement (env : Environment) (arg : String) : Option Name :=
  let n := (arg.replace "/" ".").toName
  [n, `Incognita.Statements ++ n].find? fun c => (findConst env c).isSome

/-- `--dump`. -/
def dump (env : Environment) (arg : String) : IO UInt32 := do
  let some c := resolveStatement env arg
    | IO.eprintln s!"audit: no declaration {arg} or Incognita.Statements.{arg}"; return 2
  match lockDump env c with
  | .error e =>
    IO.eprintln s!"audit: {e}"
    return 1
  | .ok (s, _) =>
    IO.print s
    IO.eprintln s!"sha256 {SHA256.hashHex s.toUTF8}"
    return 0

/-! ## Kernel replay -/

/-- Re-check every declaration of the project's modules with the kernel, on top of an environment
holding only their dependencies. Returns the number of declarations replayed. -/
def replayProject (modules : Array Name) : IO (Except String Nat) := do
  let mut datas : Array ModuleData := #[]
  for m in modules do
    let f ← findOLean m
    let p := OLeanLevel.private.adjustFileName f
    let parts ←
      if ← p.pathExists then
        readModuleDataParts #[f, OLeanLevel.server.adjustFileName f, p]
      else
        readModuleDataParts #[f]
    let some (d, _) := parts.back? | return .error s!"no data for {m}"
    datas := datas.push d
  let mut external : Array Import := #[]
  let mut seen : NameSet := {}
  for d in datas do
    for i in d.imports do
      if !isProjectModule i.module && !seen.contains i.module then
        seen := seen.insert i.module
        external := external.push { module := i.module }
  let env0 ← importModules external {} (trustLevel := 0) (loadExts := false)
  let kenv := env0.toKernelEnv
  let mut todo : Std.HashMap Name ConstantInfo := {}
  for d in datas do
    for c in d.constNames, ci in d.constants do
      match kenv.find? c with
      | some ci' =>
        -- Declarations realized in a project module for an imported name (equation lemmas).
        unless ci'.type == ci.type && kindName ci' == kindName ci do
          return .error s!"{c} is declared both in the project and in a dependency"
      | none => todo := todo.insert c ci
  try
    discard <| kenv.replay todo
    return .ok todo.size
  catch e =>
    return .error (toString e)

end IncognitaAudit

open IncognitaAudit

/-- Entry point of `lake exe audit`. -/
def main (args : List String) : IO UInt32 := do
  try
    let usage := "usage: lake exe audit [--check [--no-replay] | --new-locks | " ++
      "--refresh-new-locks | --status | --dump <statement> | --selftest]"
    let replay := !args.contains "--no-replay"
    let args := args.filter (· != "--no-replay")
    if args == ["--selftest"] then
      let mut ok := true
      for (msg, digest) in SHA256.testVectors do
        let got := SHA256.hashHex msg.toUTF8
        if got != digest then
          IO.eprintln s!"sha256 \"{msg}\": got {got}, expected {digest}"
          ok := false
      IO.println (if ok then "selftest: OK" else "selftest: FAILED")
      return if ok then 0 else 1
    let mode ← match args with
      | [] | ["--check"] => pure "check"
      | ["--new-locks"] => pure "new-locks"
      | ["--refresh-new-locks"] => pure "refresh-new-locks"
      | ["--status"] => pure "status"
      | ["--dump", _] => pure "dump"
      | ["--replay-only"] => pure "replay-only"
      | _ =>
        IO.eprintln usage
        return 2
    unless ← System.FilePath.isDir "Statements" do
      IO.eprintln "audit: run from the repository root (no Statements/ here)"
      return 2
    initSearchPath (← findSysroot)
    let modules := (← libraryModules `Incognita) ++ (← libraryModules `Statements)
    -- The kernel replay imports the dependencies again: it runs in a child process, since one
    -- process cannot import twice once the first environment's regions are freed.
    if mode == "replay-only" then
      match ← replayProject modules with
      | .ok n =>
        IO.println s!"replay: {n} declarations of Incognita/ and Statements/ re-checked by the kernel"
        return 0
      | .error e =>
        IO.println s!"error: replay: the kernel rejects the project: {e}"
        return 1
    let locks ← readLocks
    let markers ← readMarkers
    let onMain ← if mode == "refresh-new-locks" then mainLocks else pure (some {})
    let some onMain := onMain
      | IO.eprintln "audit: --refresh-new-locks needs origin/main (git ls-tree failed)"; return 2
    let result ← unsafe withImportModules (modules.map fun m => { module := m }) {}
      (trustLevel := 1024) fun env => do
        match mode with
        | "new-locks" => return (← newLocks env, #[])
        | "refresh-new-locks" => return (← refreshNewLocks env onMain, #[])
        | "status" =>
          status env
          return (0, #[])
        | "dump" => return (← dump env (args[1]!), #[])
        | _ => return (0, ← check env locks markers)
    let (code, errors) := result
    if mode != "check" then return code
    let mut errors := errors
    if replay then
      let out ← IO.Process.output { cmd := (← IO.appPath).toString, args := #["--replay-only"] }
      IO.print out.stdout
      IO.eprint out.stderr
      if out.exitCode != 0 then
        errors := errors.push s!"replay: failed (exit code {out.exitCode}), see above"
    for e in errors do
      IO.println s!"error: {e}"
    if errors.isEmpty then
      IO.println "audit: OK"
      return 0
    else
      IO.eprintln s!"audit: {errors.size} errors"
      return 1
  catch e =>
    IO.eprintln s!"audit: {e}"
    return 1
