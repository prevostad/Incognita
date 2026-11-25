#!/usr/bin/env python3
"""Offline test of scripts/library-index.py on fixture `.lean` snippets: namespaces and sections,
attributes, `private`, multi-line signatures, docstrings, aliases, instances, structures,
inductives, comments and strings that look like declarations, frozen statements, packages (Mathlib
and test directories skipped), reading at a git ref, the duplicate report and the size cap.
No network, no Lean. Usage: python3 scripts/test-library-index.py (also run by CI).
"""
import importlib.util
import os
import subprocess
import sys
import tempfile

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("library_index", os.path.join(here, "library-index.py"))
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)
fails = 0


def ok(name, cond):
    global fails
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        fails += 1


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


BASIC = '''/-
Copyright (c) 2026 Incognita contributors.
-/
module

public import Mathlib.Probability.HasLaw

/-! # Laws on the unit interval

theorem not_a_declaration : True := trivial
-/

@[expose] public section

namespace Incognita.BatchedBandits

/-- The set of **laws on `[0, 1]`**. It is used everywhere.
def fake_in_doc : Nat := 0 -/
def unitLaws : Set (Measure ℝ) := {Q | IsProbabilityMeasure Q}

-- theorem commented_out : True := trivial
/- lemma block_commented : True := trivial -/

/-- A multi-line
statement. -/
@[simp,
  nolint unusedArguments]
theorem long_statement {α : Type*} [Fintype α]
    (h : 2 ≤ Fintype.card α) :
    True := by
  have := "-- not a comment"
  trivial

private lemma helper : 1 = 1 := rfl

protected lemma Foo.bar (n : ℕ) : n = n := rfl

lemma _root_.Real.at_root (x : ℝ) : x = x := rfl

section Inner
variable {K : ℕ}

noncomputable def withWhere (n : ℕ) : ℕ where
  toFun := n

end Inner

/-- A grid. -/
structure Grid (K : ℕ) where
  t : ℕ → ℕ
  t_zero : t 0 = 0
  (strictMono : StrictMono t)

inductive Color
  | red
  | blue : Color

instance : Inhabited Color := ⟨.red⟩
instance (priority := 100) instNamed : Nonempty Color := ⟨.blue⟩

lemma Grid.le_bound (g : Grid K) (l : ℕ) : l ≤ g.t l := sorry

@[deprecated (since := "2026-11-19")] alias old_name := long_statement
alias ⟨mp_name, mpr_name⟩ := Iff.rfl

def byCases : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

mutual
def even : ℕ → Bool
  | 0 => true
  | n + 1 => odd n
def odd : ℕ → Bool
  | 0 => false
  | n + 1 => even n
end

end Incognita.BatchedBandits

namespace Incognita.TransferBandits

/-- The instances on `[0, 1]`. -/
def unitBandits (α : Type*) [MeasurableSpace α] : Set (Kernel α ℝ) := ∅

lemma same_sig_a (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * x + x * x := sorry
lemma Grid.le_t (n : ℕ) : n = n := rfl

end Incognita.TransferBandits
'''

OTHER = '''module
namespace Incognita.BatchedBandits
def unitBandits (α : Type*) [MeasurableSpace α] : Set (Kernel α ℝ) := ∅
lemma same_sig_b (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * x + x * x := sorry
structure Other where
  a : ℕ
def Other.le_bound : ℕ := 0
end Incognita.BatchedBandits
namespace Incognita.P001
theorem main_result (n : ℕ) : n ≤ n + 1 := Nat.le_succ n
end Incognita.P001
'''

FROZEN = '''module
public import Incognita.Basic
/-- [INC-P001, Theorem `thm:main`] Every number is below its successor. -/
theorem Incognita.Statements.P001.main_result (n : ℕ) : n ≤ n + 1 := by
  sorry
'''

PKG = '''namespace LMLExplore.Bandits
/-- Laws on the unit interval, in LMLExplore. -/
def unitIntervalLaws : Set (Measure ℝ) := ∅
theorem pkg_thm (x : ℝ) : x = x := rfl
end LMLExplore.Bandits
'''


def find(decls, name):
    return [d for d in decls if d["name"] == name]


with tempfile.TemporaryDirectory() as t:
    repo = os.path.join(t, "repo")
    write(os.path.join(repo, "Incognita/BatchedBandits/Basic.lean"), BASIC)
    write(os.path.join(repo, "Incognita/BatchedBandits/Other.lean"), OTHER)
    write(os.path.join(repo, "Statements/P001/main_result.lean"), FROZEN)
    pk = os.path.join(repo, ".lake/packages")
    write(os.path.join(pk, "LMLExplore/LMLExplore/Bandits/Laws.lean"), PKG)
    write(os.path.join(pk, "LMLExplore/test/Skipped.lean"), "theorem skipped_test : True := trivial\n")
    write(os.path.join(pk, "LMLExplore/lakefile.lean"), "def lakefile_decl : Nat := 0\n")
    write(os.path.join(pk, "mathlib/Mathlib/Foo.lean"), "theorem mathlib_thm : True := trivial\n")

    d = L.parse_file(BASIC, "Incognita.BatchedBandits.Basic", "Incognita/BatchedBandits/Basic.lean")
    names = [x["name"] for x in d]
    B = "Incognita.BatchedBandits."
    ok("namespace resolved", B + "unitLaws" in names)
    ok("docstring: first sentence", find(d, B + "unitLaws")[0]["doc"].strip().startswith("The set")
       and L.first_sentence(find(d, B + "unitLaws")[0]["doc"], 200)
       == "The set of **laws on `[0, 1]`**.")
    ok("nothing from comments, docstrings or the module doc",
       not any(n and ("fake_in_doc" in n or "commented" in n or "not_a_declaration" in n)
               for n in names))
    ls = find(d, B + "long_statement")
    ok("multi-line attributes and signature, read once", len(ls) == 1
       and ls[0]["sig"] == "{α : Type*} [Fintype α] (h : 2 ≤ Fintype.card α) : True"
       and L.first_sentence(ls[0]["doc"], 200) == "A multi-line statement.")
    ok("line of the keyword", ls[0]["line"] == BASIC.split("\n").index(
        "theorem long_statement {α : Type*} [Fintype α]") + 1)
    ok("private marked", find(d, B + "helper")[0]["private"])
    ok("protected name", find(d, B + "Foo.bar") != [])
    ok("_root_ name", find(d, "Real.at_root") != [])
    ok("section scope kept the namespace", find(d, B + "withWhere") != []
       and find(d, B + "withWhere")[0]["sig"] == "(n : ℕ) : ℕ")
    g = find(d, B + "Grid")
    ok("structure fields", g and g[0]["kind"] == "structure"
       and g[0]["fields"] == ["t", "t_zero", "strictMono"])
    c = find(d, B + "Color")
    ok("inductive constructors", c and c[0]["fields"] == ["red", "blue"])
    ok("anonymous instance", any(x["kind"] == "instance" and x["name"] is None for x in d))
    ok("instance with priority", find(d, B + "instNamed") != [])
    ok("deprecated alias", find(d, B + "old_name")[0]["deprecated"]
       and find(d, B + "old_name")[0]["kind"] == "alias")
    ok("alias <mp, mpr>", find(d, B + "mp_name") != [] and find(d, B + "mpr_name") != [])
    ok("pattern-matching def", find(d, B + "byCases")[0]["sig"] == ": ℕ → ℕ")
    ok("mutual block", find(d, B + "even") != [] and find(d, B + "odd") != [])
    ok("end of namespace", find(d, "Incognita.TransferBandits.unitBandits") != [])

    groups, found, missing = L.collect(repo, "", pk)
    allds = [x for _, ds in groups for x in ds]
    ok("frozen statement listed as such",
       find(allds, "Incognita.Statements.P001.main_result")[0]["kind"] == "frozen")
    ok("package indexed, Mathlib, tests and lakefile not",
       found == ["LMLExplore"] and find(allds, "LMLExplore.Bandits.unitIntervalLaws") != []
       and not any(x["name"] in ("mathlib_thm", "skipped_test", "lakefile_decl") for x in allds))
    ok("missing packages named", "LeanMachineLearning" in missing and "TauCeti" in missing)
    ok("package paths", find(allds, "LMLExplore.Bandits.pkg_thm")[0]["path"]
       == ".lake/packages/LMLExplore/LMLExplore/Bandits/Laws.lean")

    text = L.build(groups, found, missing, "", 10 ** 6)
    dup = text.split("## Possible duplicates")[1].split("\n# ")[0]
    ok("duplicate: unitBandits in two modules",
       any("unitBandits" in ln and "same name" in ln for ln in dup.split("\n")))
    ok("duplicate: same signature",
       any("same_sig_a" in ln and "same_sig_b" in ln for ln in dup.split("\n")))
    ok("no duplicate for the proof of a frozen statement", "main_result" not in dup)
    ok("no duplicate for the API of two types (Grid.le_bound, Other.le_bound)",
       "le_bound" not in dup)
    ok("no duplicate for a deprecated alias or a private lemma",
       "old_name" not in dup and "helper" not in dup)
    ok("grouped by module", "## Incognita.BatchedBandits.Basic: Laws on the unit interval" in text
       and "# LMLExplore" in text)
    ok("line format", "- def `Incognita.BatchedBandits.unitLaws` `: Set (Measure ℝ)` — The set of "
       "**laws on `[0, 1]`**. (Incognita/BatchedBandits/Basic.lean:" in text)

    small = L.build(groups, found, missing, "", len(text.encode()) - 200)
    ok("size cap: a lower level, under the cap", "detail level 0" not in small
       and len(small.encode()) <= len(text.encode()) - 200)
    tiny = L.build(groups, found, missing, "", 3000)
    ok("size cap: cut with a note", len(tiny.encode()) <= 3200 and "cut at the size cap" in tiny)

    # Reading at a git ref: the working tree's later changes are not seen.
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t")
    for cmd in (["init", "-q"], ["add", "Incognita", "Statements"], ["commit", "-q", "-m", "fixture"]):
        subprocess.run(["git", "-C", repo] + cmd, check=True, env=env, capture_output=True)
    write(os.path.join(repo, "Incognita/BatchedBandits/New.lean"), "lemma not_committed : True := trivial\n")
    out = os.path.join(t, "index.md")
    rc = L.main(["--repo", repo, "--ref", "HEAD", "--out", out])
    with open(out, encoding="utf-8") as f:
        at_ref = f.read()
    ok("--ref reads the commit", rc == 0 and "Incognita.BatchedBandits.unitLaws" in at_ref
       and "not_committed" not in at_ref and "LMLExplore.Bandits.pkg_thm" in at_ref)
    rc = L.main(["--repo", repo, "--no-packages", "--out", out])
    with open(out, encoding="utf-8") as f:
        wt = f.read()
    ok("working tree and --no-packages", rc == 0 and "not_committed" in wt
       and "LMLExplore.Bandits" not in wt)

print(f"{fails} failure(s)")
sys.exit(1 if fails else 0)
