import GLTableau.Formula

namespace Tableau

open Notation

/-- A line of a tableau: `A, i` (`A` holds at world `i`) or `irj` (world `i` sees world `j`). -/
inductive Line
  | fml (i : Nat) (A : Formula)
  | rel (i j : Nat)
  deriving DecidableEq

namespace Line

def tex : Line → String
  | fml i A => s!"{A.render .tex}, {i}"
  | rel i j => s!"{i}r{j}"

def worlds : Line → List Nat
  | fml i _ => [i]
  | rel i j => [i, j]

/-- The order of expansion: rules that don't branch, then rules that start a new world, then
rules that branch. -/
def priority : Line → Nat
  | fml _ (∼□_) | fml _ (◇_) => 1
  | fml _ (∼(_ ⋏ _)) | fml _ (_ ⋎ _) | fml _ (_ 🡒 _) | fml _ (_ 🡘 _) | fml _ (∼(_ 🡘 _)) => 2
  | _ => 0

instance : Repr Line := ⟨fun
  | fml i A, _ => s!"(.fml {i} {A.repr})"
  | rel i j, _ => s!"(.rel {i} {j})"⟩

end Line

/-- What Priest's procedure builds below a branch. -/
inductive Tree
  /-- A rule that doesn't branch, applied to `line` higher up: the lines it adds, and what's
  below them. -/
  | step (line : Line) (new : List Line) (below : Tree)
  /-- A rule that branches, applied to `line`: the lines each branch gains, and what's below. -/
  | split (line : Line) (new₁ : List Line) (below₁ : Tree) (new₂ : List Line) (below₂ : Tree)
  /-- `A, i` and `¬A, i` are both on the branch, or `A` is `⊥`. -/
  | closed (i : Nat) (A : Formula)
  /-- No rule applies: the branch is open. -/
  | exhausted
  deriving Inhabited

namespace Tree

def isClosed : Tree → Bool
  | step _ _ t => t.isClosed
  | split _ _ t₁ _ t₂ => t₁.isClosed && t₂.isClosed
  | closed .. => true
  | exhausted => false

/-- The lines below the root of the first open branch, oldest first. -/
def openBranch : Tree → Option (List Line)
  | step _ new t => (new ++ ·) <$> t.openBranch
  | split _ n₁ t₁ n₂ t₂ => ((n₁ ++ ·) <$> t₁.openBranch) <|> ((n₂ ++ ·) <$> t₂.openBranch)
  | closed .. => none
  | exhausted => some []

/-- The lines `ls` as nodes of a `prooftree` of the `prooftrees` LaTeX package, each nested in
the one above at depth `d` on, with `rest` inside the last. -/
def chain : List Line → Nat → String → String
  | [], _, rest => rest
  | l :: ls, d, rest => s!"\n{"".pushn ' ' (2 * d)}[\{{l.tex}}{chain ls (d + 1) rest}]"

/-- The nodes below depth `d`, with `close` under a closed branch. -/
def tex : Tree → Nat → String
  | step _ new t, d => chain new d (t.tex (d + new.length))
  | split _ n₁ t₁ n₂ t₂, d => chain n₁ d (t₁.tex (d + n₁.length)) ++ chain n₂ d (t₂.tex (d + n₂.length))
  | closed .., _ => ", close"
  | exhausted, _ => ""

/-- The tree as a Lean term naming the constructors, each node on its own line at depth `d`. -/
protected def repr (t : Tree) (d : Nat) : String :=
  "\n" ++ "".pushn ' ' (2 * d) ++ match t with
  | step l new t => s!"(.step {repr l} {repr new}{t.repr (d + 1)})"
  | split l n₁ t₁ n₂ t₂ => s!"(.split {repr l} {repr n₁}{t₁.repr (d + 1)} {repr n₂}{t₂.repr (d + 1)})"
  | closed i A => s!"(.closed {i} {A.repr})"
  | exhausted => ".exhausted"

end Tree

/-- A world `i` where `A, i` and `¬A, i`, or `⊥, i`, are on the branch. -/
def clash (branch : List Line) : Option (Nat × Formula) :=
  branch.findSome? fun
    | .fml i ⊥ => some (i, ⊥)
    | .fml i (∼A) => if .fml i A ∈ branch then some (i, A) else none
    | _ => none

/-- The lines of `new` not yet on the branch. -/
def absent (branch new : List Line) : List Line := (new.filter (· ∉ branch)).eraseDups

/-- A world not yet on the branch. -/
def fresh (branch : List Line) : Nat := (branch.flatMap Line.worlds).max?.getD 0 + 1

/-- Priest's rules, with the GL rule for `¬□`, the matching rule for `◇`, and transitivity: the
tree below `l`, given what's below the new lines of a branch; `none` when no rule applies.
`□` lines and `irj` lines each look for the other, so whichever comes second finds the first. -/
def rule (l : Line) (branch : List Line) (below : List Line → Tree) : Option Tree :=
  let one new := some (Tree.step l new (below new))
  let two n₁ n₂ := some (Tree.split l n₁ (below n₁) n₂ (below n₂))
  let modal new := if new.isEmpty then none else one new
  match l with
  | .fml i A =>
    let j := fresh branch
    match A with
    | ∼∼B => one [.fml i B]
    | B ⋏ C => one [.fml i B, .fml i C]
    | ∼(B ⋏ C) => two [.fml i ∼B] [.fml i ∼C]
    | B ⋎ C => two [.fml i B] [.fml i C]
    | ∼(B ⋎ C) => one [.fml i ∼B, .fml i ∼C]
    | B 🡒 C => two [.fml i ∼B] [.fml i C]
    | ∼(B 🡒 C) => one [.fml i B, .fml i ∼C]
    | B 🡘 C => two [.fml i B, .fml i C] [.fml i ∼B, .fml i ∼C]
    | ∼(B 🡘 C) => two [.fml i B, .fml i ∼C] [.fml i ∼B, .fml i C]
    | □B => modal <| absent branch <| branch.filterMap fun
        | .rel k j => if k = i then some (.fml j B) else none
        | _ => none
    | ∼□B => one [.rel i j, .fml j ∼B, .fml j □B]
    | ◇B => one [.rel i j, .fml j B, .fml j □∼B]
    | ∼◇B => one [.fml i □∼B]
    | _ => none
  | .rel i j => modal <| absent branch <| branch.filterMap fun
      | .fml k □B => if k = i then some (.fml j B) else none
      | .rel k m => if m = i then some (.rel k j) else if k = j then some (.rel i m) else none
      | _ => none

/-- Priest's procedure below `branch` (oldest line first): close if there is a clash, else
expand the first line of `todo` by priority, until none is left. -/
partial def expand (branch todo : List Line) : Tree :=
  if let some (i, A) := clash branch then .closed i A else
  match todo.mergeSort (·.priority ≤ ·.priority) with
  | [] => .exhausted
  | l :: todo =>
    match rule l branch fun new => expand (branch ++ new) (todo ++ new) with
    | some t => t
    | none => expand branch todo

end Tableau

/-- A tableau for `sentence`: what Priest's procedure builds below `¬sentence, 0`. -/
structure Tableau where
  sentence : Tableau.Formula
  tree : Tableau.Tree

namespace Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand [.fml 0 ∼A] [.fml 0 ∼A]⟩

def tex (t : Tableau) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain [.fml 0 ∼t.sentence] 1 (t.tree.tex 2)
    ++ "\n\\end{prooftree}\n"

/-- `t` as a Lean file defining it as `t`, for `tex` and `verify`. -/
def lean (t : Tableau) : String :=
  s!"import GLTableau\n\ndef t : Tableau where\n  sentence := {t.sentence.repr}\n  tree :={t.tree.repr 2}\n"

end Tableau
