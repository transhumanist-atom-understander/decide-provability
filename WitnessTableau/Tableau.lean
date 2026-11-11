import WitnessTableau.Formula

namespace Witness.Tableau

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

/-- What the procedure builds below a branch. -/
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
  | step l new t => s!"(.step {repr l} {lines new}{t.repr (d + 1)})"
  | split l n₁ t₁ n₂ t₂ => s!"(.split {repr l} {lines n₁}{t₁.repr (d + 1)} {lines n₂}{t₂.repr (d + 1)})"
  | closed i A => s!"(.closed {i} {A.repr})"
  | exhausted => ".exhausted"
where
  /-- A list of lines, however long, on one line. -/
  lines (ls : List Line) : String := s!"[{", ".intercalate (ls.map fun l => s!"{repr l}")}]"

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

/-- Whether the branch already makes `□A → □B` true at world `i`: `A` is `B`, or `□B` is on it
at `i` or at a world that sees `i`, or `¬□A` is on it at `i` or at a world that `i` sees. A
boxed formula that holds at a world holds at the worlds it sees, since `r` is transitive. -/
def settled (branch : List Line) (i : Nat) (A B : Formula) : Bool :=
  A = B || branch.any fun
    | .fml k (□C) => C = B && (k = i || .rel k i ∈ branch)
    | .fml k (∼□C) => C = A && (k = i || .rel i k ∈ branch)
    | _ => false

/-- That `□B` comes to hold no later than `□A`, at the worlds `ks` on the way down to a world
where a comparison says so: the lines `□A → □B, k` that aren't settled, earliest world first. -/
def noLater (branch : List Line) (ks : List Nat) (A B : Formula) : List Line :=
  ((ks.filter (!settled branch · A B)).mergeSort (· ≤ ·)).map (.fml · (□A 🡒 □B))

/-- The rules of `GLTableau`, and the rules for witness comparisons, none of which branch: the
tree below `l`, given what's below the new lines of a branch; `none` when no rule applies. A
rule with two premises is applied to each, which looks for the other, so whichever comes second
finds the first. -/
def rule (l : Line) (branch : List Line) (below : List Line → Tree) : Option Tree :=
  let one new := some (Tree.step l new (below new))
  let two n₁ n₂ := some (Tree.split l n₁ (below n₁) n₂ (below n₂))
  let found new := if (absent branch new).isEmpty then none else one (absent branch new)
  match l with
  | .fml i A =>
    let j := fresh branch
    /- The worlds that see `i`, and the worlds `i` sees. -/
    let above := branch.filterMap fun | .rel k m => if m = i then some k else none | _ => none
    let seen := branch.filterMap fun | .rel k m => if k = i then some m else none | _ => none
    match A with
    | ∼∼B => one [.fml i B]
    | B ⋏ C => one [.fml i B, .fml i C]
    | ∼(B ⋏ C) => two [.fml i ∼B] [.fml i ∼C]
    | B ⋎ C => two [.fml i B] [.fml i C]
    | ∼(B ⋎ C) => one [.fml i ∼B, .fml i ∼C]
    | □B 🡒 □C => if settled branch i B C then none else two [.fml i ∼□B] [.fml i □C]
    | B 🡒 C => two [.fml i ∼B] [.fml i C]
    | ∼(B 🡒 C) => one [.fml i B, .fml i ∼C]
    | B 🡘 C => two [.fml i B, .fml i C] [.fml i ∼B, .fml i ∼C]
    | ∼(B 🡘 C) => two [.fml i B, .fml i ∼C] [.fml i ∼B, .fml i C]
    | □B => found (seen.map (.fml · B))
    | ∼□B => one [.rel i j, .fml j ∼B, .fml j □B]
    | ◇B => one [.rel i j, .fml j B, .fml j □∼B]
    | ∼◇B => one [.fml i □∼B]
    /- A comparison that holds: it persists, its first formula holds, and its second came to
    hold no earlier than its first. -/
    | □B ≺ □C | □B ≼ □C => found (seen.map (.fml · A) ++ [.fml i □B] ++ noLater branch above C B)
    /- A comparison that fails: its first formula came to hold no earlier than its second. -/
    | ∼(□B ≺ □C) | ∼(□B ≼ □C) => found (noLater branch (above ++ [i]) B C)
    | _ => none
  | .rel i j => found <| branch.flatMap fun
      | .fml k A =>
        match A with
        | □B => if k = i then [.fml j B] else []
        | □B ≺ □C | □B ≼ □C =>
          if k = i then [.fml j A] else if k = j then noLater branch [i] C B else []
        | ∼(□B ≺ □C) | ∼(□B ≼ □C) => if k = j then noLater branch [i] B C else []
        | _ => []
      | .rel k m => if m = i then [.rel k j] else if k = j then [.rel i m] else []

/-- The procedure below `branch` (oldest line first): close if there is a clash, else expand
the first line of `todo` by priority, until none is left. -/
partial def expand (branch todo : List Line) : Tree :=
  if let some (i, A) := clash branch then .closed i A else
  match todo.mergeSort (·.priority ≤ ·.priority) with
  | [] => .exhausted
  | l :: todo =>
    match rule l branch fun new => expand (branch ++ new) (todo ++ new) with
    | some t => t
    | none => expand branch todo

end Witness.Tableau

/-- A tableau for `sentence`: what the procedure builds below `¬sentence, 0`. -/
structure Witness.Tableau where
  sentence : Witness.Tableau.Formula
  tree : Witness.Tableau.Tree

namespace Witness.Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand [.fml 0 ∼A] [.fml 0 ∼A]⟩

def tex (t : Tableau) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain [.fml 0 ∼t.sentence] 1 (t.tree.tex 2)
    ++ "\n\\end{prooftree}\n"

/-- What the tableau shows. A closed tableau is a proof in R⁻; an open one only shows that the
rules here, which leave out how R⁻ orders boxed formulas that come to hold together, are not
enough. -/
def claim (t : Tableau) : String :=
  if t.tree.isClosed then s!"{t.sentence} is a theorem of R⁻"
  else s!"{t.sentence} does not follow from persistence and true before false"

/-- `t` as a Lean file defining it as `t`, to print. -/
def lean (t : Tableau) : String :=
  s!"import WitnessTableau\n\n/-- {t.claim} -/\ndef t : Witness.Tableau where\n  sentence := {t.sentence.repr}\n  tree :={t.tree.repr 2}\n"

/-- Prints the tableau for the sentence `s` as a Lean file, or fails with `s`'s parse error:
what the wrapper has Lean evaluate to decide a sentence. -/
def decide (s : String) : IO Unit := do
  IO.print (of (← IO.ofExcept (Formula.parse s))).lean

end Witness.Tableau
