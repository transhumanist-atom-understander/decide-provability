# decide-provability

Priest-style labelled tableaux for sentences with witness comparisons: those of Guaspari and
Solovay's R⁻, the logic of Rosser sentences, which is GL (Gödel–Löb provability logic) with
`□A ≺ □B` and `□A ≼ □B`. The tableaux are those of Priest's *An Introduction to Non-Classical
Logic* §1.4 and §2.4, with the rule for `¬□` that makes them GL tableaux and rules for the
comparisons. It is a Lean library, `RTableau`, that the Python package `rtableau` of
[wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability) uses;
use it from there. It depends on nothing but Lean and the
[Lean REPL](https://github.com/augustepoiroux/repl), so it builds in seconds:

    $ lake build

The rules for comparisons are not all of R⁻ yet: they are in place of two of its axioms, that a
comparison persists and that true comes before false. So a tableau that closes shows a theorem
of R⁻, and one that doesn't shows only that these rules are not enough, [as set out
below](#what-they-prove). A sentence of GL, one with no comparison, is the special case that is
decided: the rules that apply to it are GL's, so its tableau closes if it is a theorem of GL and
doesn't if it is not.

The wrapper runs the REPL in this project, with `RTableau` imported once, and has it evaluate
Lean. `#eval Tableau.decide A` prints the tableau for the sentence `A` as a Lean file, defining
it as `t`, or fails with `A`'s parse error: a sentence letter is any run of characters other
than whitespace, parentheses and the connectives, `¬ □ ◇ ⊡` bind tightest, then `≺` and `≼`,
then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` is read as `¬⊥` and `⊡A` as
`A ∧ □A`. What `≺` and `≼` compare must be written as boxed formulas: `□p ≺ □q ∧ r` is
`(□p ≺ □q) ∧ r`, and `¬□p ≺ □q` doesn't parse, but `¬(□p ≺ □q)` does. That file, with
`#eval IO.print t.tex` added, prints the tableau as a `prooftree` of the `prooftrees` LaTeX
package; sentence letters are printed as they are, and the wrapper turns Greek letters and other
such characters into LaTeX commands. The REPL is required at the tag for this project's
toolchain, so the two move together.

    $ lake env .lake/packages/REPL/.lake/build/bin/repl
    {"cmd": "import RTableau"}

    {"env": 0}

    {"cmd": "#eval Tableau.decide \"□(□⊤ ≺ □⊥)\"", "env": 0}

    {"messages": [{"severity": "info", "data": "import RTableau\n\n/-- □(□¬⊥ ≺ □⊥) is a theorem of R⁻ -/\ndef t : Tableau where ..."}], "env": 1}

The file says what its tableau shows: that the sentence is a theorem of R⁻, or of GL if it has
no comparison; that it is not a theorem of GL; or, of a sentence with comparisons whose tableau
doesn't close, that it does not follow from persistence and true before false.

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

The tableau has these rules for them, where `c` is `□A ≺ □B` or `□A ≼ □B`:

    c, i   irj     ⟹  c, j              persistence
    ¬c, j  irj     ⟹  □A → □B, i        true before false; also for i = j
    c, i           ⟹  □A, i             the first is true
    c, j   irj     ⟹  □B → □A, i        false is not before true

None of them branches. The second is the axiom: had `□A` held at `i` without `□B`, `c` would
have held there, and at `j` since it persists. So `¬c, j` says, of `j` and of every world that
sees it, what the axiom's contrapositive says of one world, and that is all of the axiom that a
tableau can use, since the comparison it concludes can only clash with its negation, at that
world or a later one. It is in this form, as a line to split, that the axiom is a premise of a
tableau drawn by hand; the rule adds it only where a comparison has failed, and without its
third branch, `c, i`, which would close. The fourth is its mirror image, for a comparison that
holds: had `□B` held at `i` without `□A`, the opposite comparison would have held at `i`, and
at `j`. Both say that a boxed formula came to hold *no later* than another on the way down to
`j`, which is what a comparison can say about boxed formulas that didn't come to hold together.

The implications are split by the rule for `→`, as `¬□A, i` and `□B, i`. One is not split where
the branch has settled it: where `□B` is on the branch at `i` or at a world that sees `i`, or
`¬□A` at `i` or at a world `i` sees, or `A` is `B`. That is the only change to GL's rules, and
it keeps a comparison at a world `n` steps down from costing more than `n + 2` branches. It
holds of any implication between boxed formulas, a sentence of GL's too, where it changes the
tableau and not what it shows: an implication the branch has settled is true in the model an
open branch describes.

### What they prove

The tableau for a sentence closes exactly when GL proves it from these axioms, for each
comparison `c` in it, with `c` read as a sentence letter and each axiom taken at the first
world and at the worlds it sees, as `⊡` of it:

    c → □c                     (□A ∧ ¬□B) → c
    c → □A                     (□B ∧ ¬□A) → □¬c

They are theorems of R⁻, so a tableau that closes shows a theorem of R⁻. A tableau that
doesn't close shows only that these axioms are not enough, and its file says so: R⁻ also has
the axioms that make `≼` a total preorder of the boxed formulas that hold, with `≺` its strict
part, and those matter for boxed formulas that come to hold at the same world, of which the
rules here say nothing. So `□p ≺ □q → ¬(□q ≺ □p)` and `□p ≺ □q → □p ≼ □q` are not proved, nor
is `¬(□p ≺ □q) ∧ □q → □¬(□p ≺ □q)`. For a sentence with no comparison there are no such axioms,
and the tableau decides whether GL proves it.

In a model, the rules say that the comparisons that hold at a world lie between two orders of
the boxed formulas, both read off the path down to it: every boxed formula that held at a world
where another didn't is before it, and no boxed formula is before one that held at a world
where it didn't. These are `<` and `≤` of de Jongh's *A simplification of a completeness proof
of Guaspari and Solovay* (1987), Lemma 4, which has that a model of R⁻ puts `≺` and `≼` between
them. Within those bounds the rules leave the comparisons free; R⁻ does not.

What the rules are worth is in the sizes. The Parikh sentence `Π ↔ □□Π ≺ □Π` is provably
provable, `⊡(Π ↔ □□Π ≺ □Π) → □Π`: the tableau here has 9 branches and some 50 lines, and
the tableau with the four axioms as premises has 9,500 branches and 26,000 lines.

## Files

- `RTableau/Formula.lean`: formulas, their parser, and their LaTeX and Lean printers.
- `RTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, the procedure, and the
  `Tableau` a Lean file defines.
- `RTableau.lean`: the library, the two modules above.
