import RMinusTableau.Formula

namespace RMinus.Tableau

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

/-- The four branches of the order rule for `□A` and `□B` at world `i`: neither is witnessed,
`□A` is witnessed first, `□B` is witnessed first, or they are witnessed together. -/
def order (i : Nat) (A B : Formula) : List Line × List Line × List Line × List Line :=
  ([fml i ∼□A, fml i ∼□B], [fml i (□A ≺ □B)], [fml i (□B ≺ □A)], [fml i (□A ≼ □B), fml i (□B ≼ □A)])

instance : Repr Line := ⟨fun
  | fml i A, _ => s!"(.fml {i} {A.repr})"
  | rel i j, _ => s!"(.rel {i} {j})"⟩

end Line

/-- What the procedure builds below a branch. -/
inductive Tree
  /-- A rule that doesn't branch, applied to `line` higher up: the lines it adds, and what's
  below them. -/
  | step (line : Line) (new : List Line) (below : Tree)
  /-- A rule that branches, applied to `line`: the lines each branch gains, and what's below. -/
  | split (line : Line) (new₁ : List Line) (below₁ : Tree) (new₂ : List Line) (below₂ : Tree)
  /-- The order rule for `□A` and `□B` at world `i`: what's below the lines of each of its
  four branches, `Line.order i A B`. -/
  | order (i : Nat) (A B : Formula) (neither first second together : Tree)
  /-- `A, i` and `¬A, i` are both on the branch, or `A` is `⊥`, or `□B ≺ □B`. -/
  | closed (i : Nat) (A : Formula)
  /-- No rule applies: the branch is open. -/
  | exhausted
  deriving Inhabited

namespace Tree

def isClosed : Tree → Bool
  | step _ _ t => t.isClosed
  | split _ _ t₁ _ t₂ => t₁.isClosed && t₂.isClosed
  | order _ _ _ t₁ t₂ t₃ t₄ => t₁.isClosed && t₂.isClosed && t₃.isClosed && t₄.isClosed
  | closed .. => true
  | exhausted => false

/-- The lines below the root of the first open branch, oldest first. -/
def openBranch : Tree → Option (List Line)
  | step _ new t => (new ++ ·) <$> t.openBranch
  | split _ n₁ t₁ n₂ t₂ => ((n₁ ++ ·) <$> t₁.openBranch) <|> ((n₂ ++ ·) <$> t₂.openBranch)
  | order i A B t₁ t₂ t₃ t₄ =>
    let (n₁, n₂, n₃, n₄) := Line.order i A B
    ((n₁ ++ ·) <$> t₁.openBranch) <|> ((n₂ ++ ·) <$> t₂.openBranch)
      <|> ((n₃ ++ ·) <$> t₃.openBranch) <|> ((n₄ ++ ·) <$> t₄.openBranch)
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
  | order i A B t₁ t₂ t₃ t₄, d =>
    let (n₁, n₂, n₃, n₄) := Line.order i A B
    chain n₁ d (t₁.tex (d + n₁.length)) ++ chain n₂ d (t₂.tex (d + n₂.length))
      ++ chain n₃ d (t₃.tex (d + n₃.length)) ++ chain n₄ d (t₄.tex (d + n₄.length))
  | closed .., _ => ", close"
  | exhausted, _ => ""

/-- The tree as a Lean term naming the constructors, each node on its own line at depth `d`. -/
protected def repr (t : Tree) (d : Nat) : String :=
  "\n" ++ "".pushn ' ' (2 * d) ++ match t with
  | step l new t => s!"(.step {repr l} {lines new}{t.repr (d + 1)})"
  | split l n₁ t₁ n₂ t₂ => s!"(.split {repr l} {lines n₁}{t₁.repr (d + 1)} {lines n₂}{t₂.repr (d + 1)})"
  | order i A B t₁ t₂ t₃ t₄ =>
    s!"(.order {i} {A.repr} {B.repr}{t₁.repr (d + 1)}{t₂.repr (d + 1)}{t₃.repr (d + 1)}{t₄.repr (d + 1)})"
  | closed i A => s!"(.closed {i} {A.repr})"
  | exhausted => ".exhausted"
where
  /-- A list of lines, however long, on one line. -/
  lines (ls : List Line) : String := s!"[{", ".intercalate (ls.map fun l => s!"{repr l}")}]"

end Tree

/-- What is left to do on a branch: expand a line, or apply the order rule to `□A` and `□B` at
world `i`. -/
inductive Task
  | line (l : Line)
  | order (i : Nat) (A B : Formula)

/-- The order of the tasks: the lines by their priority, then the order rule, which branches
most, at the earliest world first. -/
def Task.priority : Task → Nat
  | line l => l.priority
  | order i .. => 3 + i

/-- A world `i` where `A, i` and `¬A, i`, or `⊥, i`, or `□B ≺ □B, i`, are on the branch. -/
def clash (branch : List Line) : Option (Nat × Formula) :=
  branch.findSome? fun
    | .fml i ⊥ => some (i, ⊥)
    | .fml i (□A ≺ □B) => if A = B then some (i, □A ≺ □A) else none
    | .fml i (∼A) => if .fml i A ∈ branch then some (i, A) else none
    | _ => none

/-- What follows by transitivity from two comparisons, of `□A` with `□B` and of `□C` with `□D`,
each strict (`≺`) or not (`≼`): a comparison that is strict if either is. That a boxed formula
`≼` itself is left out. -/
def transitive (s : Bool) (A B : Formula) (s' : Bool) (C D : Formula) : List Formula :=
  ((if B = C then [(A, D)] else []) ++ (if D = A then [(C, B)] else [])).filterMap fun (E, F) =>
    if E = F && !(s || s') then none else some (.compare (s || s') E F)

/-- The lines of `new` not yet on the branch. -/
def absent (branch new : List Line) : List Line := (new.filter (· ∉ branch)).eraseDups

/-- A world not yet on the branch. -/
def fresh (branch : List Line) : Nat := (branch.flatMap Line.worlds).max?.getD 0 + 1

/-- The rules of `GLTableau`, and the rules for witness comparisons that don't branch: the tree
below `l`, given what's below the new lines of a branch; `none` when no rule applies. A rule
with two premises is applied to each, which looks for the other, so whichever comes second
finds the first. -/
def rule (l : Line) (branch : List Line) (below : List Line → Tree) : Option Tree :=
  let one new := some (Tree.step l new (below new))
  let two n₁ n₂ := some (Tree.split l n₁ (below n₁) n₂ (below n₂))
  let found new := if (absent branch new).isEmpty then none else one (absent branch new)
  /- What `□A ≺ □B, i` (if `s`) or `□A ≼ □B, i` gives: itself at the worlds `i` sees, and
  what follows from it and each comparison at `i`, by transitivity. -/
  let comparison i s A B := branch.flatMap fun
    | .rel k j => if k = i then [.fml j (.compare s A B)] else []
    | .fml k (□C ≺ □D) => if k = i then (transitive s A B true C D).map (.fml i) else []
    | .fml k (□C ≼ □D) => if k = i then (transitive s A B false C D).map (.fml i) else []
    | _ => []
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
    | □B => found <| branch.filterMap fun
        | .rel k j => if k = i then some (.fml j B) else none
        | _ => none
    | ∼□B => one [.rel i j, .fml j ∼B, .fml j □B]
    | ◇B => one [.rel i j, .fml j B, .fml j □∼B]
    | ∼◇B => one [.fml i □∼B]
    | □B ≺ □C => found (.fml i (□B ≼ □C) :: comparison i true B C)
    | □B ≼ □C => found (.fml i □B :: comparison i false B C)
    | ∼(□B ≼ □C) => if B = C then found [.fml i ∼□B] else none
    | _ => none
  | .rel i j => found <| branch.filterMap fun
      | .fml k □B => if k = i then some (.fml j B) else none
      | .fml k (□B ≺ □C) => if k = i then some (.fml j (□B ≺ □C)) else none
      | .fml k (□B ≼ □C) => if k = i then some (.fml j (□B ≼ □C)) else none
      | .rel k m => if m = i then some (.rel k j) else if k = j then some (.rel i m) else none
      | _ => none

/-- What the lines `new` of `branch` leave to do: to expand them, and to apply the order rule
where it is needed. A comparison `A, j`, or its negation, of two of `pairs`, the pairs of
formulas whose boxes the sentence compares, needs the order rule for them at each world that
sees `j`, and its negation needs it at `j` too. -/
def tasks (pairs : List (Formula × Formula)) (branch new : List Line) : List Task :=
  new.map .line ++ new.flatMap fun
    | .fml j A => (pair A).flatMap fun (B, C) =>
        (branch.filterMap fun | .rel i k => if k = j then some (.order i B C) else none | _ => none)
          ++ (match A with | ∼_ => [.order j B C] | _ => [])
    | .rel i j => branch.flatMap fun
        | .fml k A => if k = j then (pair A).map fun (B, C) => .order i B C else []
        | _ => []
where
  /-- The pair of `pairs` that `A` or the formula it negates compares. -/
  pair : Formula → List (Formula × Formula)
    | □A ≺ □B | □A ≼ □B | ∼(□A ≺ □B) | ∼(□A ≼ □B) => pairs.filter fun p => p = (A, B) || p = (B, A)
    | _ => []

/-- The procedure below `branch` (oldest line first): close if there is a clash, else do the
first of `todo` by priority, until nothing is left. Where the order rule is needed for `□A`
and `□B`, it is not applied if all the lines of one of its branches are there already; and if
one of the two holds and the other doesn't, the rule for that is applied in its place. -/
partial def expand (pairs : List (Formula × Formula)) (branch : List Line) (todo : List Task) : Tree :=
  if let some (i, A) := clash branch then .closed i A else
  let below todo new :=
    let new := absent branch new
    expand pairs (branch ++ new) (todo ++ tasks pairs (branch ++ new) new)
  match todo.mergeSort (·.priority ≤ ·.priority) with
  | [] => .exhausted
  | .line l :: todo =>
    match rule l branch (below todo) with
    | some t => t
    | none => expand pairs branch todo
  | .order i A B :: todo =>
    let (n₁, n₂, n₃, n₄) := Line.order i A B
    if [n₁, n₂, n₃, n₄].any (·.all (· ∈ branch)) then expand pairs branch todo
    else if .fml i □A ∈ branch && .fml i ∼□B ∈ branch then .step (.fml i □A) n₂ (below todo n₂)
    else if .fml i □B ∈ branch && .fml i ∼□A ∈ branch then .step (.fml i □B) n₃ (below todo n₃)
    else .order i A B (below todo n₁) (below todo n₂) (below todo n₃) (below todo n₄)

end RMinus.Tableau

/-- A tableau for `sentence`: what the procedure builds below `¬sentence, 0`. -/
structure RMinus.Tableau where
  sentence : RMinus.Tableau.Formula
  tree : RMinus.Tableau.Tree

namespace RMinus.Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand A.compared [.fml 0 ∼A] (tasks A.compared [.fml 0 ∼A] [.fml 0 ∼A])⟩

def tex (t : Tableau) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain [.fml 0 ∼t.sentence] 1 (t.tree.tex 2)
    ++ "\n\\end{prooftree}\n"

def claim (t : Tableau) : String :=
  s!"{t.sentence} is {if t.tree.isClosed then "" else "not "}a theorem of R⁻"

/-- `t` as a Lean file defining it as `t`, to print. -/
def lean (t : Tableau) : String :=
  s!"import RMinusTableau\n\n/-- {t.claim} -/\ndef t : RMinus.Tableau where\n  sentence := {t.sentence.repr}\n  tree :={t.tree.repr 2}\n"

/-- Prints the tableau for the sentence `s` as a Lean file, or fails with `s`'s parse error:
what the wrapper has Lean evaluate to decide a sentence. -/
def decide (s : String) : IO Unit := do
  IO.print (of (← IO.ofExcept (Formula.parse s))).lean

end RMinus.Tableau
