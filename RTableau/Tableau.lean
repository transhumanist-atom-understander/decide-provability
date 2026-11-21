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

/-- The order of expansion: rules that don't branch, then rules that start a new world, then
rules that branch. -/
def priority : Line → Nat
  | fml _ (∼□_) | fml _ (◇_) => 1
  | fml _ (∼(_ ⋏ _)) | fml _ (_ ⋎ _) | fml _ (_ 🡒 _) | fml _ (_ 🡘 _) | fml _ (∼(_ 🡘 _)) => 2
  | fml _ (∼(□_ ≺ □_)) | fml _ (∼(□_ ≼ □_)) => 2
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
  /-- The comparisons `cs` are on the branch at world `i`, and go round in a circle: each
  compares the second formula of the one before it, the first that of the last, and the first
  is strict. -/
  | cycle (i : Nat) (cs : List Formula)
  /-- No rule applies: the branch is open. -/
  | exhausted
  deriving Inhabited

namespace Tree

def isClosed : Tree → Bool
  | step _ _ t => t.isClosed
  | split _ _ t₁ _ t₂ => t₁.isClosed && t₂.isClosed
  | closed .. | cycle .. => true
  | exhausted => false

/-- The lines below the root of each open branch, oldest first, the branches from left to
right. -/
def openBranches : Tree → List (List Line)
  | step _ new t => t.openBranches.map (new ++ ·)
  | split _ n₁ t₁ n₂ t₂ => t₁.openBranches.map (n₁ ++ ·) ++ t₂.openBranches.map (n₂ ++ ·)
  | closed .. | cycle .. => []
  | exhausted => [[]]

/-- The lines `ls` as nodes of a `prooftree` of the `prooftrees` LaTeX package, each nested in
the one above at depth `d` on, with `rest` inside the last. -/
def chain : List Line → Nat → String → String
  | [], _, rest => rest
  | l :: ls, d, rest => s!"\n{"".pushn ' ' (2 * d)}[\{{l.tex}}{chain ls (d + 1) rest}]"

/-- The nodes below depth `d`, with `close` under a closed branch. -/
def tex : Tree → Nat → String
  | step _ new t, d => chain new d (t.tex (d + new.length))
  | split _ n₁ t₁ n₂ t₂, d => chain n₁ d (t₁.tex (d + n₁.length)) ++ chain n₂ d (t₂.tex (d + n₂.length))
  | closed .., _ | cycle .., _ => ", close"
  | exhausted, _ => ""

/-- The tree as a Lean term naming the constructors, each node on its own line at depth `d`. -/
protected def repr (t : Tree) (d : Nat) : String :=
  "\n" ++ "".pushn ' ' (2 * d) ++ match t with
  | step l new t => s!"(.step {repr l} {lines new}{t.repr (d + 1)})"
  | split l n₁ t₁ n₂ t₂ => s!"(.split {repr l} {lines n₁}{t₁.repr (d + 1)} {lines n₂}{t₂.repr (d + 1)})"
  | closed i A => s!"(.closed {i} {A.repr})"
  | cycle i cs => s!"(.cycle {i} [{", ".intercalate (cs.map (·.repr))}])"
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

/-- The comparisons that the `branch` speaks of, in its order. A drawing names them `c₁`, `c₂`
and so on, since they are long, and what is written by a world is what sets the worlds apart. -/
def comparisons (branch : List Line) : List Formula :=
  (branch.filterMap fun
    | .fml _ (∼(□A ≺ □B)) | .fml _ (□A ≺ □B) => some (□A ≺ □B)
    | .fml _ (∼(□A ≼ □B)) | .fml _ (□A ≼ □B) => some (□A ≼ □B)
    | _ => none).eraseDups

/-- A fact in the style `s`, with the name of a comparison in place of it: in LaTeX if `tex`. -/
def fact (branch : List Line) (s : Formula.Style) (tex : Bool) : Formula → String
  | ∼A => s.neg ++ fact branch s tex A
  | A =>
    match (comparisons branch).idxOf? A with
    | some n => if tex then s!"c_\{{n + 1}}" else s!"c{n + 1}"
    | none => A.render s

/-- The width in mm to leave for what is written to the right of world `i`: 2 for each
character of the facts, and 7 for the `⊩`. -/
def width (branch : List Line) (i : Nat) : Int :=
  match facts branch i with
  | [] => 0
  | fs => 7 + 2 * (", ".intercalate (fs.map (fact branch .unicode false))).length

/-- Where the worlds below `i`, and `i`, go: each with how far right of `i` it is, in mm, and
how many steps down from the first world, `i` being `depth` steps down; and how far the drawing
of them reaches to the left and to the right of `i`. A world is midway above the first and last
of the worlds it started, which are side by side, far enough apart that what is drawn below one
and written to its right is clear of the next. -/
partial def layout (branch : List Line) (i depth : Nat) : List (Nat × Int × Nat) × Int × Int :=
  /- Each subtree with where its top world is, the first one's left edge being at 0. -/
  let (subs, _) := ((started branch i).map (layout branch · (depth + 1))).foldl
    (fun (subs, edge) (ws, l, r) => (subs ++ [(edge - l, ws, l, r)], edge - l + r + 5)) ([], 0)
  let mid := match subs.head?, subs.getLast? with
    | some (a, _), some (b, _) => (a + b) / 2
    | _, _ => 0
  ((i, 0, depth) :: subs.flatMap fun (x, ws, _, _) => ws.map fun (w, dx, d) => (w, dx + x - mid, d),
    subs.foldl (fun m (x, _, l, _) => min m (x + l - mid)) (-4),
    subs.foldl (fun m (x, _, _, r) => max m (x + r - mid)) (4 + width branch i))

/-- The model as a `tikzpicture`, which needs the LaTeX packages `tikz` and `amssymb`: an arrow
from each world to the worlds it started, the others that it sees being those further down, and
below them what the names of the comparisons stand for. -/
def tex (branch : List Line) : String :=
  let (worlds, left, right) := layout branch 0 0
  let node := fun ((i, x, d) : Nat × Int × Nat) =>
    s!"  \\node[inner sep=2pt] (w{i}) at ({x}mm,{-12 * (d : Int)}mm) \{$w_\{{i}}$};\n"
  let says := fun ((i, _, _) : Nat × Int × Nat) =>
    match facts branch i with
    | [] => ""
    | fs => s!"  \\node[anchor=west, inner sep=0pt] at (w{i}.east) \{$\\,\\Vdash {", ".intercalate (fs.map (fact branch .tex true))}$};\n"
  let arrows := fun ((i, _, _) : Nat × Int × Nat) =>
    "".intercalate ((started branch i).map fun j => s!"  \\draw[->] (w{i}.south) -- (w{j}.north);\n")
  let depth := (worlds.map (·.2.2)).max?.getD 0
  let key := (comparisons branch).zipIdx.map fun (c, n) =>
    s!"  \\node[inner sep=0pt] at ({(left + right) / 2}mm,{-12 * (depth : Int) - 10 - 7 * (n : Int)}mm) \{${fact branch .tex true c} = {c.render .tex}$};\n"
  "\\begin{tikzpicture}[>=stealth]\n" ++ "".intercalate (worlds.map node ++ worlds.map says ++ worlds.map arrows ++ key)
    ++ "\\end{tikzpicture}\n"

end Model

/-- A world `i` where `A, i` and `¬A, i`, or `⊥, i`, are on the branch: the one of the first
line `¬A, i` or `⊥, i` that makes it so. The branch is `old` and then `new`, and `old` has no
such world, so that line is a `¬A, i` of `old` with `A, i` in `new`, or it is in `new`. -/
def clash (old new : List Line) : Option (Nat × Formula) :=
  (old.findSome? fun
    | .fml i (∼A) => if .fml i A ∈ new then some (i, A) else none
    | _ => none) <|>
  new.findSome? fun
    | .fml i ⊥ => some (i, ⊥)
    | .fml i (∼A) => if .fml i A ∈ new || .fml i A ∈ old then some (i, A) else none
    | _ => none

/-- The lines of `new` not yet on the branch. -/
def absent (branch new : List Line) : List Line := (new.filter (· ∉ branch)).eraseDups

/-- A world not yet on the branch. -/
def fresh (branch : List Line) : Nat :=
  branch.foldl (fun j => fun | .fml i _ => max j i | .rel i k => max j (max i k)) 0 + 1

/-- Whether the branch already makes `□A → □B` true at world `i`: `A` is `B`, or `□B` is on it
at `i` or at a world that sees `i`, or `¬□A` is on it at `i` or at a world that `i` sees. A
boxed formula that holds at a world holds at the worlds it sees, since `r` is transitive. -/
def settled (branch : List Line) (i : Nat) (A B : Formula) : Bool :=
  A = B || branch.any fun
    | .fml k (□C) => C = B && (k = i || .rel k i ∈ branch)
    | .fml k (∼□C) => C = A && (k = i || .rel i k ∈ branch)
    | _ => false

/-- Whether the branch already makes the comparison `c` true at world `i`: it is on it at `i`
or at a world that sees `i`, since a comparison persists. -/
def holds (branch : List Line) (i : Nat) (c : Formula) : Bool :=
  branch.any fun
    | .fml k A => A = c && (k = i || .rel k i ∈ branch)
    | _ => false

/-- Whether the branch already makes `□A` false at world `i`: `¬□A` is on it at `i` or at a
world that `i` sees. -/
def fails (branch : List Line) (i : Nat) (A : Formula) : Bool :=
  branch.any fun
    | .fml k (∼□C) => C = A && (k = i || .rel i k ∈ branch)
    | _ => false

/-- The comparisons on the branch at world `i`, each with the two formulas whose boxes it
compares: the edges of the graph that the order of the boxed formulas at `i` must extend. -/
def edges (branch : List Line) (i : Nat) : List (Formula × Formula × Formula) :=
  branch.filterMap fun
    | .fml k (□A ≺ □B) => if k = i then some (□A ≺ □B, A, B) else none
    | .fml k (□A ≼ □B) => if k = i then some (□A ≼ □B, A, B) else none
    | _ => none

/-- Comparisons among `es` that lead from `□A` to `□B`, each comparing the second formula of
the one before: none if `A` is `B`. A formula that has been left is not come back to. -/
def path (es : List (Formula × Formula × Formula)) (A B : Formula) : Option (List Formula) :=
  go es.length es A
where
  go : Nat → List (Formula × Formula × Formula) → Formula → Option (List Formula)
    | 0, _, A => if A = B then some [] else none
    | n + 1, es, A =>
      if A = B then some [] else
      es.findSome? fun (c, A', C) =>
        if A' = A then (go n (es.filter (·.2.1 ≠ A)) C).map (c :: ·) else none

/-- A world with comparisons on the branch that no order satisfies, and those comparisons: a
strict one, `□A ≺ □B`, and others that lead from `□B` back to `□A`. The branch ends with the
lines `new` and had no such world before them, so it is a world where one of them is a
comparison, and only those are searched. -/
def circle (branch new : List Line) : Option (Nat × List Formula) :=
  let worlds := new.filterMap fun | .fml i (□_ ≺ □_) | .fml i (□_ ≼ □_) => some i | _ => none
  if worlds.isEmpty then none else
  branch.findSome? fun
    | .fml i (□A ≺ □B) =>
      if i ∈ worlds then (path (edges branch i) B A).map fun cs => (i, (□A ≺ □B) :: cs) else none
    | _ => none

/-- Priest's rules, with the GL rule for `¬□`, the matching rule for `◇`, and transitivity, and
the rules for witness comparisons: the tree below `l`, given what's below the new lines of a
branch; `none` when no rule applies. A rule with two premises is applied to each, which looks
for the other, so whichever comes second finds the first. -/
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
    /- Where a comparison started, which the branch may have settled. -/
    | (□B ≺ □C) ⋎ ∼□D =>
      if holds branch i (□B ≺ □C) || fails branch i D then none else two [.fml i (□B ≺ □C)] [.fml i ∼□D]
    | (□B ≼ □C) ⋎ ∼□D =>
      if holds branch i (□B ≼ □C) || fails branch i D then none else two [.fml i (□B ≼ □C)] [.fml i ∼□D]
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
    /- A comparison that holds: it persists, its first formula holds, and at the world that
    started this one it held already, or its second formula didn't. -/
    | □B ≺ □C | □B ≼ □C =>
      let before := match above.max? with
        | some k => if holds branch k A || fails branch k C then [] else [.fml k (A ⋎ ∼□C)]
        | none => []
      found (seen.map (.fml · A) ++ [.fml i □B] ++ before)
    /- A comparison that fails: its first formula doesn't hold, or the converse comparison
    does. -/
    | ∼(□B ≺ □C) =>
      if fails branch i B || holds branch i (□C ≼ □B) then none else two [.fml i ∼□B] [.fml i (□C ≼ □B)]
    | ∼(□B ≼ □C) =>
      if fails branch i B || holds branch i (□C ≺ □B) then none else two [.fml i ∼□B] [.fml i (□C ≺ □B)]
    | _ => none
  | .rel i j => found <| branch.flatMap fun
      | .fml k A =>
        match A with
        | □B => if k = i then [.fml j B] else []
        | □_ ≺ □_ | □_ ≼ □_ => if k = i then [.fml j A] else []
        | _ => []
      | .rel k m => if m = i then [.rel k j] else if k = j then [.rel i m] else []

/-- The procedure below `branch` (oldest line first) once the lines `new` are added to it and
to `todo`: close if there is a clash, or a circle of comparisons, else expand the first line of
`todo` by priority, until none is left. The branch had no clash and no circle before `new`, or
it would have closed, so they are looked for only where `new` can have made one. -/
partial def expand (branch new todo : List Line) : Tree :=
  if let some (i, A) := clash branch new then .closed i A else
  if let some (i, cs) := circle (branch ++ new) new then .cycle i cs else
  next (branch ++ new) (todo ++ new)
where
  next (branch todo : List Line) : Tree :=
    match todo.mergeSort (·.priority ≤ ·.priority) with
    | [] => .exhausted
    | l :: todo =>
      match rule l branch (expand branch · todo) with
      | some t => t
      | none => next branch todo

end Tableau

/-- A tableau for `sentence`: what the procedure builds below `¬sentence, 0`. -/
structure Tableau where
  sentence : Tableau.Formula
  tree : Tableau.Tree

namespace Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand [] [.fml 0 ∼A] []⟩

def tex (t : Tableau) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain [.fml 0 ∼t.sentence] 1 (t.tree.tex 2)
    ++ "\n\\end{prooftree}\n"

/-- The models that the tableau's open branches describe, each as a `tikzpicture`, the branches
from left to right: none if the tableau closed, and one for branches that are drawn the same.
Of a sentence of GL each is a countermodel: a finite tree, read as the transitive order it
generates, at whose first world the sentence fails, however the letters the branch doesn't
speak of at a world are valued there. Of a sentence with comparisons each is a countermodel
too, a model of R⁻: the comparisons the branch doesn't speak of at a world hold there or don't
as the boxed formulas came to hold on the way down to it, those that came to hold together in
any order that the comparisons the branch does speak of there allow. -/
def modelsTex (t : Tableau) : List String :=
  (t.tree.openBranches.map fun branch => Model.tex (.fml 0 ∼t.sentence :: branch)).eraseDups

/-- What the tableau shows. A closed tableau is a proof, and an open one a refutation: the
rules are complete for R⁻, and for a sentence of GL they are GL's. -/
def claim (t : Tableau) : String :=
  match t.tree.isClosed, t.sentence.isGL with
  | true, true => s!"{t.sentence} is a theorem of GL"
  | true, false => s!"{t.sentence} is a theorem of R⁻"
  | false, true => s!"{t.sentence} is not a theorem of GL"
  | false, false => s!"{t.sentence} is not a theorem of R⁻"

/-- `t` as a Lean file defining it as `t`. -/
def lean (t : Tableau) : String :=
  s!"import RTableau\n\n/-- {t.claim} -/\ndef t : Tableau where\n  sentence := {t.sentence.repr}\n  tree :={t.tree.repr 2}\n"

/-- The tableau for the sentence `s`, or `s`'s parse error. -/
def ofSentence (s : String) : IO Tableau := of <$> IO.ofExcept (Formula.parse s)

/-- Prints the tableau for the sentence `s` as a Lean file, or fails with `s`'s parse error:
what the wrapper has Lean evaluate to decide a sentence. -/
def decide (s : String) : IO Unit := do
  IO.print (← ofSentence s).lean

end Tableau
