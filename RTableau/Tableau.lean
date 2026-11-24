import RTableau.Model

namespace Tableau

open Notation

/-- A line of a tableau: `A, i` (`A` holds at world `i`) or `irj` (world `i` sees world `j`). -/
inductive Line
  | fml (i : Nat) (A : Formula)
  | rel (i j : Nat)
  deriving DecidableEq

namespace Line

def tex (s : Formula.Style) : Line → String
  | fml i A => s!"{A.render s}, {i}"
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

/-- The lines `ls`, in the style `s`, as nodes of a `prooftree` of the `prooftrees` LaTeX
package, each nested in the one above at depth `d` on, with `rest` inside the last. -/
def chain (s : Formula.Style) : List Line → Nat → String → String
  | [], _, rest => rest
  | l :: ls, d, rest => s!"\n{"".pushn ' ' (2 * d)}[\{{l.tex s}}{chain s ls (d + 1) rest}]"

/-- The nodes below depth `d`, in the style `s`, with `close` under a closed branch. -/
def tex (s : Formula.Style) : Tree → Nat → String
  | step _ new t, d => chain s new d (tex s t (d + new.length))
  | split _ n₁ t₁ n₂ t₂, d =>
    chain s n₁ d (tex s t₁ (d + n₁.length)) ++ chain s n₂ d (tex s t₂ (d + n₂.length))
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

-- The model that an open branch describes: its worlds as a tree, each with the sentence
-- letters the branch has there and an order that the comparisons it has there allow.

/-- The worlds that the rules for `¬□` and `◇` started from world `i`. The other worlds that
see one of them are older than `i`: they are those that see `i`, by transitivity. -/
def started (branch : List Line) (i : Nat) : List Nat :=
  branch.filterMap fun
    | .rel k j => if k = i && branch.all (fun | .rel m n => n ≠ j || m ≤ i | _ => true) then some j else none
    | _ => none

/-- An order that satisfies the comparisons on the `branch` at world `i`, which have no circle:
the formulas whose boxes they compare, `A` for `□A`, each as early as they allow. A formula is
after the first formula of each strict comparison it is the second of, and no earlier than that
of each other one, which as many rounds as there are formulas see to. -/
def witnessed (branch : List Line) (i : Nat) : List (List Formula) :=
  let es := edges branch i
  let formulas := (es.flatMap fun (_, A, B) => [A, B]).eraseDups
  let round (when : List (Formula × Nat)) : List (Formula × Nat) :=
    when.map fun (B, n) => (B, es.foldl (fun n (c, A, B') =>
      if B' = B then max n (((when.lookup A).getD 0) + (match c with | □_ ≺ □_ => 1 | _ => 0)) else n) n)
  let when := formulas.length.repeat round (formulas.map (·, 0))
  (List.range formulas.length).filterMap fun n =>
    match (when.filter (·.2 = n)).map (·.1) with
    | [] => none
    | together => some together

namespace Model

/-- The model that the open `branch` describes, from world `i` down, as the completeness of the
rules has it: the worlds that each world started below it, the letters that the branch has at a
world holding there and no others, and at each world an order that satisfies the comparisons
the branch has there. What is on the branch is true in it. -/
partial def ofBranch (branch : List Line) (i : Nat := 0) : Model where
  letters := (branch.filterMap fun
    | .fml k (.atom a) => if k = i then some a else none
    | _ => none).eraseDups
  order := (witnessed branch i).map (·.map fun A => toString (□A))
  sees := (started branch i).map fun j => ofBranch branch j

/-- The model without the orders that order nothing: those of one list, which only put what is
in it before what is not. A branch asks that of no world, so its model can do without. -/
partial def plain (m : Model) : Model :=
  { m with order := if m.order.length ≤ 1 then [] else m.order, sees := m.sees.map plain }

end Model

end Tableau

/-- A tableau for `sentence`: what the procedure builds below `¬sentence, 0`. -/
structure Tableau where
  sentence : Tableau.Formula
  tree : Tableau.Tree

namespace Tableau

open Notation

def of (A : Formula) : Tableau := ⟨A, expand [] [.fml 0 ∼A] []⟩

/-- The tableau as a `prooftree` of the `prooftrees` LaTeX package, in the LaTeX style `s`. -/
def tex (t : Tableau) (s : Formula.Style := .tex) : String :=
  "\\begin{prooftree}{not line numbering}" ++ Tree.chain s [.fml 0 ∼t.sentence] 1 (t.tree.tex s 2)
    ++ "\n\\end{prooftree}\n"

/-- The models that the tableau's open branches describe, the branches from left to right: none
if the tableau closed, and one for branches that describe the same. Each is a countermodel, a
model of R⁻ at whose first world the sentence fails, and of a sentence of GL a model of GL: a
finite tree, read as the transitive order it generates. A letter holds at a world if the branch
has it there. The boxed formulas that come to hold at a world are witnessed in an order that
the comparisons the branch has there allow, and the model has an order only at a world where
that sets some of those before others. -/
def models (t : Tableau) : List Model :=
  (t.tree.openBranches.map fun branch => (Model.ofBranch (.fml 0 ∼t.sentence :: branch)).trimmed.plain).foldl
    (fun found m => if found.any (·.lean == m.lean) then found else found ++ [m]) []

/-- The tableau's `models`, each as a Lean term. -/
def modelsLean (t : Tableau) : List String := t.models.map (·.lean)

/-- The tableau's `models`, each as a tree of the `forest` LaTeX package, in the LaTeX style
`s`. -/
def modelsTex (t : Tableau) (s : Formula.Style := .tex) : List String := t.models.map (·.tex s)

/-- The LaTeX that `print` gives of the tableau, in a LaTeX style, as a Python format string
with a replacement field for each sentence letter, `{0}` for the first of `t.sentence.letters`:
what the wrapper asks for, to put in each letter as LaTeX has it, `\varphi` for `φ`. -/
def format (t : Tableau) (print : Tableau → Formula.Style → String) : String :=
  Formula.formatString (print t (.fields t.sentence.letters))

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

/-- Prints the tableau for the sentence `s`, as a Lean file or as `print` has it, or fails with
`s`'s parse error: what the wrapper has Lean evaluate, of a sentence, for all that it wants of
its tableau. -/
def decide (s : String) (print : Tableau → String := lean) : IO Unit := do
  IO.print (print (of (← IO.ofExcept (Formula.parse s))))

/-- Prints the sentence `s` in LaTeX, as a Python format string with a replacement field for
each sentence letter, as `format` gives the LaTeX of a tableau, or fails with `s`'s parse
error. No tableau is built for it. -/
def sentenceTex (s : String) : IO Unit := do
  let A ← IO.ofExcept (Formula.parse s)
  IO.print (Formula.formatString (A.render (.fields A.letters)))

/-- Prints the sentence letters of the sentence `s`, each once, in the order they first come
in, with a space between them, or fails with `s`'s parse error: what the wrapper has Lean
evaluate for the letters that the fields of a format string are for. -/
def letters (s : String) : IO Unit := do
  IO.print (" ".intercalate (← IO.ofExcept (Formula.parse s)).letters)

end Tableau
