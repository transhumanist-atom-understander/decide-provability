# decide-provability

Priest-style labelled tableaux for sentences with witness comparisons: those of Guaspari and
Solovay's R⁻, the logic of Rosser sentences, which is GL (Gödel–Löb provability logic) with
`□A ≺ □B` and `□A ≼ □B`. The tableaux are those of Priest's *An Introduction to Non-Classical
Logic* §1.4 and §2.4, with the rule for `¬□` that makes them GL tableaux and rules for the
comparisons. It is a Lean library, `RTableau`, that the Python package `rtableau` of
[wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability) uses;
use it from there. It depends on nothing but Lean and the
[Lean REPL](https://github.com/augustepoiroux/repl), so it builds in half a minute, the library
and the REPL that the wrapper runs:

    $ lake build

The rules for comparisons are complete for R⁻, [as set out below](#why-they-are-complete): a
tableau closes if its sentence is a theorem of R⁻ and doesn't if it is not, and then each open
branch describes a countermodel. For a sentence of GL, one with no comparison, the rules that
apply are GL's, so its tableau closes if it is a theorem of GL and doesn't if it is not.

The wrapper runs that REPL in this project, with `RTableau` imported once, and has it evaluate
Lean. `#eval Tableau.decide A` prints the tableau for the sentence `A` as a Lean file, defining
it as `t`, or fails with `A`'s parse error: a sentence letter is any run of characters other
than whitespace, parentheses and the connectives, `¬ □ ◇ ⊡` bind tightest, then `≺` and `≼`,
then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` is read as `¬⊥` and `⊡A` as
`A ∧ □A`. What `≺` and `≼` compare must be written as boxed formulas: `□p ≺ □q ∧ r` is
`(□p ≺ □q) ∧ r`, and `¬□p ≺ □q` doesn't parse, but `¬(□p ≺ □q)` does.

`Tableau.decide` takes a second argument, what to print of the tableau in place of the file.
`#eval Tableau.decide A (·.tex)` prints the tableau as a `prooftree` of the `prooftrees` LaTeX
package, with its sentence letters as they are. `#eval Tableau.decide A ("\n".intercalate ·.modelsTex)` prints the
models that the open branches describe, from left to right and one for branches that are drawn
the same, each as a tree of the `forest` LaTeX package, for a document that also has the package
`amssymb` and the TikZ library `shapes.multipart`, with a blank line between them, or nothing if
the tableau closed. A model is drawn with its worlds as a tree, an arrow from each
to the worlds that the rules for `¬□` and `◇` started from it, which stands for the transitive
order that generates, and by each world what the branch says there of the sentence letters and
the comparisons, which are named `c₁`, `c₂` and so on there and spelled out below the worlds,
to keep the drawing narrow. Each is a countermodel, however the letters a world says nothing of
are valued there; the comparisons it says nothing of are then settled by how the boxed formulas
came to hold on the way down to it, [as below](#why-they-are-complete).

A sentence letter is printed as it is, in LaTeX too, so one that is LaTeX is as LaTeX has it:
`\varphi`, or `p_{1}`. What the LaTeX is for `φ` is not for this library to know. The wrapper
knows, and asks for two things. `#eval Tableau.letters A` prints the sentence letters of `A`,
each once, with a space between them. `#eval Tableau.decide A (·.format fun t s => t.tex s)`
prints the `prooftree` as a Python format string: the place of each letter among those, `{0}`
for the first, where the letter would be, and the braces that are LaTeX's doubled. The wrapper
turns each letter into LaTeX and formats the string with them. `fun t s => t.modelsTex s` and
the like take the place of `fun t s => t.tex s`: `s` is how to spell the connectives and the
letters, a `Formula.Style`. `#eval Tableau.sentenceTex A` prints such a format string for the
sentence alone, and builds no tableau for it.

The REPL is required at the tag for this project's toolchain, so the two move together, and is
built here as the executable `repl`, with the library linked in. The REPL interprets the Lean it
is given, and its own executable interprets a library that is imported too; this one runs what
is evaluated of `RTableau` as compiled code, which builds a tableau some fifteen times faster.
It is the library it was linked with that it runs, so `lake build` after a change to it.

The tableau is built each time, for each thing that is printed of it, and nothing is kept: for
a sentence of a line, that takes a tenth of a millisecond, where the REPL takes a few
milliseconds to evaluate anything at all. The Lean file is a record of the tableau, which
`#eval IO.print t.tex` and the like can be added to, but Lean builds a tableau much faster than
it reads the file of one: it takes far longer to elaborate the definition of `t` than to work
out what it defines. So there is nothing to gain by keeping the file to read again.

    $ lake exe repl
    {"cmd": "import RTableau"}

    {"env": 0}

    {"cmd": "#eval Tableau.decide \"□(□⊤ ≺ □⊥)\"", "env": 0}

    {"messages": [{"severity": "info", "data": "import RTableau\n\n/-- □(□¬⊥ ≺ □⊥) is a theorem of R⁻ -/\ndef t : Tableau where ..."}], "env": 1}

The file says what its tableau shows: that the sentence is a theorem of R⁻, or of GL if it has
no comparison; or that it is not a theorem of R⁻, or of GL.

## The tableau

The tableau starts from `¬A, 0` and applies Priest's rules for `¬¬`, `∧`, `∨`, `→`, `↔` and
their negations, with these modal rules:

    □A, i   irj  ⟹  A, j
    ¬□A, i       ⟹  irj,  ¬A, j,  □A, j     j new
    ◇A, i        ⟹  irj,  A, j,  □¬A, j     j new
    ¬◇A, i       ⟹  □¬A, i
    irj   jrk    ⟹  irk

The rule for `¬□` is Priest's rule for `◇¬`, with the `□A, j` that makes it GL's, so Löb's
theorem goes through, and the rule for `◇` likewise. Transitivity is Priest's rule for K4.
The branch closes on `A, i` and `¬A, i`, or on `⊥, i`.

An implication between boxed formulas, `□A → □B, i`, is not split where the branch has settled
it: where `□B` is on the branch at `i` or at a world that sees `i`, or `¬□A` at `i` or at a
world `i` sees, or `A` is `B`. That changes the tableau and not what it shows: an implication
the branch has settled is true in the model an open branch describes.

Each line is expanded once; a rule with two premises is applied to each, which looks for the
other, so whichever comes second finds the first. Lines are expanded in order of appearance,
except that rules that don't branch go before the rules for `¬□` and `◇`, which start a new
world, and those before rules that branch. Branching rules add their lines even when they are
already there; the other rules only add lines that are new.

## Witness comparisons

`□A ≺ □B` says that `□A` is witnessed before `□B` is, and `□A ≼ □B` that `□A` is witnessed and
`□B` is not witnessed before it: in arithmetic, that there is a proof of `A` with no smaller
proof of `B`, or none as small. R⁻ is GL with Guaspari and Solovay's axioms for them (*Rosser
sentences*, 1979): a comparison that holds is provable, as a boxed formula that holds is, and
there are the order axioms, of which the one a proof most often needs is that true comes before
false,

    (□A ∧ ¬□B) → □A ≺ □B

### The rules

The tableau has these rules for them, where `c` is `□A ≺ □B` or `□A ≼ □B`, and `c̄` is its
converse, `□B ≼ □A` or `□B ≺ □A`:

    c, i   irj     ⟹  c, j                    persistence
    c, i           ⟹  □A, i                   the first is true
    ¬c, i          ⟹  ¬□A, i  |  c̄, i         a comparison that fails
    c, j   irj     ⟹  c ∨ ¬□B, i              where it started; i the world that started j

and a branch also closes on a circle of comparisons at a world, one of them strict:

    □A₁ ≺ □A₂, i   □A₂ ≼ □A₃, i   ...   □Aₙ ≼ □A₁, i        each ≼ or ≺

The third is how a comparison fails: `□A` is not witnessed, or it is, and then `□B` is witnessed
no later, or earlier, which is the converse comparison. So a comparison that fails is traded for
one that holds, and the rules need only say what it is for a comparison to hold. The converse,
and the disjunction of the fourth rule, are the formulas a tableau has that are not subformulas
of its sentence.

The fourth says where a comparison that holds came to hold. If `c` holds at `j` and not at the
world `i` that started `j`, then `□B` doesn't hold at `i`: had it held there, without `c`, the
converse of `c` would have held at `i`, by the third rule, and at `j`, since it persists. The
rule adds the disjunction as a line, for the rule for `∨` to split, and neither adds nor splits
it where the branch has settled it: where `c` is on the branch at `i` or at a world that sees
`i`, or `¬□B` at `i` or at a world `i` sees. The third rule likewise doesn't split where `¬□A`
is on the branch at `i` or at a world `i` sees, or `c̄` at `i` or at a world that sees `i`.

A circle is what no order satisfies: `≼` is a preorder of the boxed formulas that hold, and `≺`
is its strict part. `□A ≺ □A` is a circle, and so are `c` and `c̄`, but a circle can be any
length, `¬(□p ≺ □q ∧ □q ≺ □r ∧ □r ≺ □p)` being a theorem. The check is of the comparisons on
the branch at one world, as the edges of a graph of the boxed formulas they compare: it needs
no comparison that the other rules didn't put there.

### Why they are complete

A model of R⁻ is a finite tree-ordered model of GL in which the comparisons persist and order
the boxed formulas as Guaspari and Solovay's axioms say. De Jongh's *A simplification of a
completeness proof of Guaspari and Solovay* (1987), Lemma 2, spells that out, and with
persistence it comes to this: at each world the boxed formulas that hold there are totally
preordered; that order is the order they had at the world before, followed by the formulas that
came to hold at this world, in any order at all. So a model is a model of GL with, at each
world, a total preorder of the boxed formulas that first hold there, and a comparison holds at a
world as its two formulas came to hold on the way down to it: the first came to hold at an
earlier world than the second, or the second never did, or they came to hold at the same world,
and its order says so.

Take an open branch. At each world, the comparisons on the branch there have no circle, so
there is a total preorder of all boxed formulas that satisfies them: choose one for each world.
With the model of GL that the branch describes, in which a comparison is first read as a
sentence letter, they define a model of R⁻, comparisons within comparisons being settled from
the inside out. What is on the branch is true in it:

- `c, j`. Go up from `j` to the first world `k` on the way down that has `c`. By the fourth
  rule, the world that started `k` has `¬□B`, or a world it sees does, or `k` is the first
  world, so `□B` doesn't hold before `k`; by the second, `□A` holds at `k`. So `□A` came to hold
  before `□B` did, or both at `k`, where `c` is on the branch, and the order chosen for `k`
  satisfies it.
- `¬c, i`. By the third rule the branch has `¬□A` at `i` or at a world `i` sees, and `c` fails,
  or it has `c̄` at `i`, which is true by the case above, and `c` fails.

The comparisons of formulas outside the sentence are then as in de Jongh's extension lemma.
That the rules are sound is that each is a theorem of R⁻: the third is
`¬c ↔ ¬□A ∨ c̄`, and the fourth `◇c → c ∨ ¬□B`.

What the rules are worth is in the sizes. The Parikh sentence `Π ↔ □□Π ≺ □Π` is provably
provable, `⊡(Π ↔ □□Π ≺ □Π) → □Π`: the tableau here has 10 branches and some 70 lines, and the tableau
with just the axioms for persistence and true before false as premises, the comparison read as a
sentence letter, has 9,500 branches and 26,000 lines.

## Files

- `RTableau/Formula.lean`: formulas, their parser, and their LaTeX and Lean printers.
- `RTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, the procedure, the drawing of
  an open branch's model, and the `Tableau` a Lean file defines.
- `RTableau.lean`: the library, the two modules above.
- `Main.lean`: the executable `repl`, the REPL with the library linked in.
