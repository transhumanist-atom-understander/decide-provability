import RTableau.Formula

namespace Tableau

open Notation

/-- A model of R⁻, written as its first world: a finite tree of worlds, read as the transitive
order it generates, with the sentence letters that hold at each and an order for the boxed
formulas that first hold there.

A boxed formula holds at a world if its formula holds at every world below it, so once it holds
it holds at every world further down, and it is witnessed at the world where it first does. The
boxed formulas that hold at a world are witnessed in the order they had at the world above,
followed by those that first hold at this one, in its `order`. `□A ≺ □B` holds at a world if
`□A` holds there and `□B` doesn't, or was witnessed after it, and `□A ≼ □B` if `□A` holds there
and `□B` doesn't, or wasn't witnessed before it.

Every term of this type is a model of R⁻: that is de Jongh's Lemma 2 (*A simplification of a
completeness proof of Guaspari and Solovay*, 1987), with persistence. So a sentence that doesn't
hold at the first world of one is not a theorem of R⁻, and no tableau is needed to see it. A
field that is left out is empty: `{}` is a world where no letter holds, with no world below. -/
structure Model where
  /-- The sentence letters that hold at this world. The others don't. -/
  letters : List String := []
  /-- Boxed formulas, written as in a sentence, as they are witnessed if they first hold at
  this world: those of a list together, before those of the next. A boxed formula that first
  holds here and is in none of the lists is witnessed after all that are, together with the
  others in none. One that doesn't first hold here is not ordered here, whatever is written. -/
  order : List (List String) := []
  /-- The worlds just below this one: it sees them, and every world that they see. -/
  sees : List Model := []
  deriving Inhabited

namespace Model

/-- The formula `A` of the boxed formula `□A` that `s` is, written as in a sentence. -/
def boxed (s : String) : Except String Formula :=
  match Formula.parse s with
  | .ok (□A) => pure A
  | .ok A => throw s!"{A} is not a boxed formula, and an order is of boxed formulas"
  | .error e => throw s!"{s} is not a formula: {e}"

/-- What is wrong with the model as written, if anything is: a letter that no sentence has, or
something in an order that is not a boxed formula. -/
partial def check (m : Model) : Except String Unit := do
  for a in m.letters do
    if Formula.parse a matches .ok (.atom _) then pure () else throw s!"{a} is not a sentence letter"
  for together in m.order do
    for s in together do
      discard (boxed s)
  m.sees.forM check

/-- The number of worlds. -/
partial def size (m : Model) : Nat := m.sees.foldl (· + ·.size) 1

/-- The worlds just below the first, each with its place. The worlds of a model are counted
from its first, each before the worlds below it and those before the next beside it; `i` is the
place of the first. -/
def seesAt (m : Model) (i : Nat) : List (Model × Nat) :=
  (m.sees.foldl (fun (found, j) w => (found ++ [(w, j)], j + w.size)) ([], i + 1)).1

/-- A world, as what holds is worked out from: one of the worlds of a model, in their places. -/
structure World where
  /-- The place of the world just above, if there is one. -/
  above : Option Nat
  /-- The place of the last world below: the worlds below are those after this one, up to it. -/
  last : Nat
  letters : List String
  /-- The world's order, `A` for `□A`, without what is not a boxed formula. -/
  order : List (List Formula)
  deriving Inhabited

/-- The worlds of the model, in their places, where `i` is the place of the first and `above`
that of the world just above it. -/
partial def worlds (m : Model) (i : Nat := 0) (above : Option Nat := none) : List World :=
  { above, last := i + m.size - 1, letters := m.letters,
    order := m.order.map (·.filterMap fun s => (boxed s).toOption) }
    :: (m.seesAt i).flatMap fun (w, j) => w.worlds j (some i)

/-- Where `□A` holds, given where `A` does: at the worlds with `A` at every world below. -/
def always (ws : Array World) (holds : Array Bool) : Array Bool :=
  ws.mapIdx fun i w => (List.range' (i + 1) (w.last - i)).all (holds[·]!)

/-- For each world where a boxed formula holds, the place of the world where it first held, on
the way down to it, given where it holds. -/
def first (ws : Array World) (holds : Array Bool) : Array (Option Nat) := Id.run do
  let mut found := #[]
  for i in [0:ws.size] do
    found := found.push (if holds[i]! then ws[i]!.above.bind (found[·]!) <|> some i else none)
  return found

/-- When `□A` is witnessed at a world, among the boxed formulas that first hold there: the
place in the order of the list it is in, or after them all. -/
def World.rank (w : World) (A : Formula) : Nat :=
  (w.order.findIdx? (·.contains A)).getD w.order.length

/-- Where `A` holds: for each world, in its place, whether it does. A comparison holds as its
two boxed formulas came to hold on the way down: the first at a world above the one where the
second did, or the second never, or both at one world, whose order then says. -/
def truth (ws : Array World) : Formula → Array Bool
  | .atom a => ws.map (·.letters.contains a)
  | ⊥ => ws.map fun _ => false
  | ∼A => (truth ws A).map (!·)
  | A ⋏ B => (truth ws A).zipWith (· && ·) (truth ws B)
  | A ⋎ B => (truth ws A).zipWith (· || ·) (truth ws B)
  | A 🡒 B => (truth ws A).zipWith (!· || ·) (truth ws B)
  | A 🡘 B => (truth ws A).zipWith (· == ·) (truth ws B)
  | □A => always ws (truth ws A)
  | ◇A => (always ws ((truth ws A).map (!·))).map (!·)
  | □A ≺ □B => compare (· < ·) A B (always ws (truth ws A)) (always ws (truth ws B))
  | □A ≼ □B => compare (· ≤ ·) A B (always ws (truth ws A)) (always ws (truth ws B))
where
  /-- Where `□A` is witnessed and `□B` is not, or is and `before` says how the two were
  witnessed where they first held together, given where each holds. A world above another
  comes before it, so of two on the way down to a world it has the earlier place. -/
  compare (before : Nat → Nat → Bool) (A B : Formula) (a b : Array Bool) : Array Bool :=
    let (a, b) := (first ws a, first ws b)
    ws.mapIdx fun i _ =>
      match a[i]!, b[i]! with
      | none, _ => false
      | some _, none => true
      | some j, some k => if j = k then before (ws[j]!.rank A) (ws[j]!.rank B) else j < k

/-- Whether `A` holds in the model: at its first world. -/
def satisfies (m : Model) (A : Formula) : Bool := (truth m.worlds.toArray A)[0]!

/-- The model with only what first holds at a world in that world's order. It is the same
model, since nothing else is ordered there, written with what its orders do say. -/
partial def trimmed (m : Model) : Model := go m.worlds.toArray m 0
where
  go (ws : Array World) (w : Model) (i : Nat) : Model :=
    let here (s : String) : Bool :=
      match boxed s with
      | .ok A => (first ws (always ws (truth ws A)))[i]! == some i
      | .error _ => false
    { w with
      order := (w.order.map (·.filter here)).filter (!·.isEmpty)
      sees := (w.seesAt i).map fun (v, j) => go ws v j }

/-- The formulas of the boxed formulas in the model's orders, `A` for `□A`, each once, in the
order of the worlds. -/
partial def ordered (m : Model) : List Formula := (all m).eraseDups
where
  all (m : Model) : List Formula :=
    m.order.flatMap (·.filterMap fun s => (boxed s).toOption) ++ m.sees.flatMap all

/-- The sentence letters that the model has, at its worlds and in its orders, each once, in the
order of the worlds. -/
partial def alphabet (m : Model) : List String := (all m).eraseDups
where
  all (m : Model) : List String :=
    m.letters ++ m.order.flatMap (·.flatMap fun s => ((boxed s).toOption.map (·.letters)).getD [])
      ++ m.sees.flatMap all

/-- The model as a Lean term, as it would be written: each world on a line of its own, at depth
`d`, within the world above, and no field that is empty. -/
partial def lean (m : Model) (d : Nat := 0) : String :=
  let list (items : List String) := s!"[{", ".intercalate items}]"
  let letters := if m.letters.isEmpty then [] else [s!"letters := {list (m.letters.map (·.quote))}"]
  let order := if m.order.isEmpty then [] else
    [s!"order := {list (m.order.map fun together => list (together.map (·.quote)))}"]
  let sees := if m.sees.isEmpty then [] else
    [s!"sees := [{",".intercalate (m.sees.map fun w => s!"\n{"".pushn ' ' (2 * (d + 1))}{w.lean (d + 1)}")} ]"]
  match letters ++ order ++ sees with
  | [] => "{}"
  | fields => s!"\{ {", ".intercalate fields} }"

/-- The world `w`, at place `i`, and the worlds below it, as a tree of the `forest` LaTeX
package, `w` at depth `d`: a node for each, of two parts, the world and what holds there, with
the nodes of the worlds just below nested in it. What holds is the world's letters, and then
its order, with the name that `name` gives a boxed formula in place of it: `≺` between those
witnessed one before the other, and `≈` between those witnessed together. -/
partial def tree (s : Formula.Style) (name : Formula → String) (w : Model) (i d : Nat) : String :=
  let order := w.order.map fun together =>
    " \\approx ".intercalate (together.filterMap fun x => (boxed x).toOption.map name)
  let holds := w.letters.map s.letter ++ (if order.isEmpty then [] else [" \\prec ".intercalate order])
  let says := if holds.isEmpty then "" else s!"$\\Vdash {", ".intercalate holds}$"
  s!"\n{"".pushn ' ' (2 * d)}[\{$w_\{{i}}$\\nodepart\{two}{says}}{"".intercalate ((w.seesAt i).map fun (v, j) => tree s name v j (d + 1))}]"

/-- The model as a tree of the `forest` LaTeX package, which also needs `amssymb` and the TikZ
library `shapes.multipart`, in the LaTeX style `s`: an arrow from each world to the worlds just
below it, the others that it sees being those further down, and by each world the letters that
hold there and the order of the boxed formulas that first hold there, as `trimmed` has it. The
boxed formulas are long, so they are named `b₁`, `b₂` and so on where the worlds are, and
spelled out below them. A world is midway above the first and last of the worlds just below it,
which are side by side, and `forest` puts them as far apart as what is drawn below each and
written to its right takes: it has the sizes of what is typeset, which are not to be had here. -/
def tex (m : Model) (s : Formula.Style := .tex) : String :=
  let m := m.trimmed
  let name (A : Formula) := s!"b_\{{m.ordered.idxOf A + 1}}"
  let key := m.ordered.map fun A =>
    s!"\n  \\node[anchor=north, inner sep=0pt] at ([yshift=-3mm]current bounding box.south) \{${name A} = {(□A).render s}$};"
  "\\begin{forest}\n  for tree={rectangle split, rectangle split horizontal, rectangle split parts=2, inner sep=2pt,\n"
    ++ "    anchor=text, parent anchor=one south, child anchor=one north, l=12mm, l sep=0pt, s sep=5mm,\n"
    ++ "    edge={->, >=stealth}}" ++ tree s name m 0 1 ++ "".intercalate key ++ "\n\\end{forest}\n"

/-- The model's sentence letters, with a space between them, and on the lines after that its
LaTeX, as a Python format string with a replacement field for each letter, `{0}` for the first:
what the wrapper asks for, to put in each letter as LaTeX has it. -/
def format (m : Model) : String :=
  " ".intercalate m.alphabet ++ "\n" ++ Formula.formatString (m.tex (.fields m.alphabet))

end Model

/-- Prints the model `m` as a Lean term, or as `print` has it, or fails with what is wrong with
it as written: what the wrapper has Lean evaluate, of a model, for what it wants of it. -/
def model (m : Model) (print : Model → String := Model.lean) : IO Unit := do
  IO.ofExcept m.check
  IO.print (print m)

/-- Prints whether the sentence `s` holds in the model `m`, `true` or `false`, or fails with
`s`'s parse error, or with what is wrong with `m` as written. A sentence that doesn't hold in a
model is not a theorem of R⁻. -/
def satisfied (s : String) (m : Model) : IO Unit := do
  IO.ofExcept m.check
  IO.print (m.satisfies (← IO.ofExcept (Formula.parse s)))

end Tableau
