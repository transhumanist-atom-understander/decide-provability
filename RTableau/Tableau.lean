import RTableau.Formula

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

-- The Kripke model that a branch describes, drawn: its worlds as a tree, each with what the
-- branch says there of the sentence letters and the comparisons.
namespace Model

/-- What the `branch` says at world `i` of a sentence letter or a comparison: that it holds or
that it doesn't, in the order of the branch. -/
def facts (branch : List Line) (i : Nat) : List Formula :=
  (branch.filterMap fun
    | .fml k A =>
      match A with
      | .atom _ | ∼(.atom _) | □_ ≺ □_ | □_ ≼ □_ | ∼(□_ ≺ □_) | ∼(□_ ≼ □_) => if k = i then some A else none
      | _ => none
    | _ => none).eraseDups

/-- The worlds that the rules for `¬□` and `◇` started from world `i`. The other worlds that
see one of them are older than `i`: they are those that see `i`, by transitivity. -/
def started (branch : List Line) (i : Nat) : List Nat :=
  branch.filterMap fun
    | .rel k j => if k = i && branch.all (fun | .rel m n => n ≠ j || m ≤ i | _ => true) then some j else none
    | _ => none

/-- The width in mm to leave for what is written to the right of world `i`: 3 for each
character of the facts, and 5 for the `⊩`. -/
def width (branch : List Line) (i : Nat) : Int :=
  match facts branch i with
  | [] => 0
  | fs => 5 + 3 * (", ".intercalate (fs.map toString)).length

/-- Where the worlds below `i`, and `i`, go: each with how far right of `i` it is, in mm, and
how many steps down from the first world, `i` being `depth` steps down; and how far the drawing
of them reaches to the left and to the right of `i`. A world is midway above the first and last
of the worlds it started, which are side by side, far enough apart that what is drawn below one
and written to its right is clear of the next. -/
partial def layout (branch : List Line) (i depth : Nat) : List (Nat × Int × Nat) × Int × Int :=
  /- Each subtree with where its top world is, the first one's left edge being at 0. -/
  let (subs, _) := ((started branch i).map (layout branch · (depth + 1))).foldl
    (fun (subs, edge) (ws, l, r) => (subs ++ [(edge - l, ws, l, r)], edge - l + r + 4)) ([], 0)
  let mid := match subs.head?, subs.getLast? with
    | some (a, _), some (b, _) => (a + b) / 2
    | _, _ => 0
  ((i, 0, depth) :: subs.flatMap fun (x, ws, _, _) => ws.map fun (w, dx, d) => (w, dx + x - mid, d),
    subs.foldl (fun m (x, _, l, _) => min m (x + l - mid)) (-3),
    subs.foldl (fun m (x, _, _, r) => max m (x + r - mid)) (3 + width branch i))

/-- The model as a `tikzpicture`, which needs the LaTeX packages `tikz` and `amssymb`: an arrow
from each world to the worlds it started, the others that it sees being those further down. -/
def tex (branch : List Line) : String :=
  let worlds := (layout branch 0 0).1
  let node := fun ((i, x, d) : Nat × Int × Nat) =>
    s!"  \\node[inner sep=2pt] (w{i}) at ({x}mm,{-12 * (d : Int)}mm) \{$w_\{{i}}$};\n"
  let fact := fun ((i, _, _) : Nat × Int × Nat) =>
    match facts branch i with
    | [] => ""
    | fs => s!"  \\node[anchor=west, inner sep=0pt] at (w{i}.east) \{$\\,\\Vdash {", ".intercalate (fs.map (·.render .tex))}$};\n"
  let arrows := fun ((i, _, _) : Nat × Int × Nat) =>
    "".intercalate ((started branch i).map fun j => s!"  \\draw[->] (w{i}) -- (w{j});\n")
  "\\begin{tikzpicture}[>=stealth]\n" ++ "".intercalate (worlds.map node ++ worlds.map fact ++ worlds.map arrows)
    ++ "\\end{tikzpicture}\n"

end Model

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

/-- Priest's rules, with the GL rule for `¬□`, the matching rule for `◇`, and transitivity, and
the rules for witness comparisons, none of which branch: the tree below `l`, given what's below
the new lines of a branch; `none` when no rule applies. A rule with two premises is applied to
each, which looks for the other, so whichever comes second finds the first. -/
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

end Tableau

/-- A tableau for `sentence`: what the procedure builds below `¬sentence, 0`. -/
structure Tableau where
  sentence : Tableau.Formula
  tree : Tableau.Tree

namespace Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand [.fml 0 ∼A] [.fml 0 ∼A]⟩

def tex (t : Tableau) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain [.fml 0 ∼t.sentence] 1 (t.tree.tex 2)
    ++ "\n\\end{prooftree}\n"

/-- The model that the tableau's first open branch describes, as a `tikzpicture`, or nothing
if the tableau closed. Of a sentence of GL it is a countermodel: a finite tree, read as the
transitive order it generates, at whose first world the sentence fails, however the letters the
branch doesn't speak of at a world are valued there. Of a sentence with comparisons it is a model
of what the rules say of them, and not always one of R⁻. -/
def modelTex (t : Tableau) : Option String :=
  (fun branch => Model.tex (.fml 0 ∼t.sentence :: branch)) <$> t.tree.openBranch

/-- What the tableau shows. A closed tableau is a proof in R⁻, and in GL if the sentence is
GL's. An open one refutes a sentence of GL, for which the rules are GL's and complete; for a
sentence with comparisons it only shows that the rules here, which leave out how R⁻ orders
boxed formulas that come to hold together, are not enough. -/
def claim (t : Tableau) : String :=
  match t.tree.isClosed, t.sentence.isGL with
  | true, true => s!"{t.sentence} is a theorem of GL"
  | true, false => s!"{t.sentence} is a theorem of R⁻"
  | false, true => s!"{t.sentence} is not a theorem of GL"
  | false, false => s!"{t.sentence} does not follow from persistence and true before false"

/-- `t` as a Lean file defining it as `t`. -/
def lean (t : Tableau) : String :=
  s!"import RTableau\n\n/-- {t.claim} -/\ndef t : Tableau where\n  sentence := {t.sentence.repr}\n  tree :={t.tree.repr 2}\n"

/-- Prints the tableau for the sentence `s` as a Lean file, or fails with `s`'s parse error:
what the wrapper has Lean evaluate to decide a sentence. -/
def decide (s : String) : IO Unit := do
  IO.print (of (← IO.ofExcept (Formula.parse s))).lean

end Tableau
