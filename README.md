# decide-provability

Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as in
Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□` that
makes them GL tableaux. It is a Lean library, `GLTableau`, that the Python package `gltableau`
of [wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability)
uses; use it from there. A second library, `WitnessTableau`, has the same tableaux for
sentences with the witness comparisons `□A ≺ □B` and `□A ≼ □B` of Guaspari and Solovay's R⁻,
with rules for them in place of two of its axioms: [see below](#witness-comparisons). They
depend on nothing but Lean and the [Lean REPL](https://github.com/augustepoiroux/repl), so they
build in seconds:

    $ lake build

Having Lean check what a tableau shows is the separate project
[verify-provability](https://github.com/transhumanist-atom-understander/verify-provability),
which depends on this one and on `ProvabilityLogic`, hence Mathlib. It checks GL tableaux;
nothing checks the tableaux of `WitnessTableau`.

The wrapper runs the REPL in this project, with one of the libraries imported once, and has it
evaluate Lean. `#eval Tableau.decide A` prints the tableau for the sentence `A` as a Lean
file, defining it as `t`, or fails with `A`'s parse error: a sentence letter is any run of
characters other than whitespace, parentheses and the connectives, `¬ □ ◇ ⊡` bind tightest,
then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` is read as `¬⊥` and `⊡A` as
`A ∧ □A`. That file, with `#eval IO.print t.tex` added, prints the tableau as a `prooftree`
of the `prooftrees` LaTeX package; sentence letters are printed as they are, and the wrapper
turns Greek letters and other such characters into LaTeX commands. The REPL is required at
the tag for this project's toolchain, so the two move together.

    $ lake env .lake/packages/REPL/.lake/build/bin/repl
    {"cmd": "import GLTableau"}

    {"env": 0}

    {"cmd": "#eval Tableau.decide \"□(□p → p) → □p\"", "env": 0}

    {"messages": [{"severity": "info", "data": "import GLTableau\n\n/-- □(□p → p) → □p is a theorem of GL -/\ndef t : Tableau where ..."}], "env": 1}

## The GL tableau

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

Each line is expanded once; `□A, i` lines and `irj` lines each look for the other, so
whichever comes second finds the first. Lines are expanded in order of appearance, except that
rules that don't branch go before the rules for `¬□` and `◇`, which start a new world, and
those before rules that branch. Branching rules add their lines even when they are already
there; the modal rules only add lines that are new.

## Witness comparisons

`□A ≺ □B` says that `□A` is witnessed before `□B` is, and `□A ≼ □B` that `□A` is witnessed and
`□B` is not witnessed before it: in arithmetic, that there is a proof of `A` with no smaller
proof of `B`, or none as small. R⁻ is GL with Guaspari and Solovay's axioms for them (*Rosser
sentences*, 1979): a comparison that holds is provable, as a boxed formula that holds is, and
there are the order axioms, of which the one a proof most often needs is that true comes before
false,

    (□A ∧ ¬□B) → □A ≺ □B

`WitnessTableau` is used as `GLTableau` is, with `Witness.Tableau` for `Tableau`:
`#eval Witness.Tableau.decide A` prints the tableau for `A` as a Lean file that imports
`WitnessTableau` and defines `t : Witness.Tableau`. Comparisons bind tighter than `∧` and looser
than `¬ □ ◇ ⊡`, and what they compare must be written as boxed formulas: `□p ≺ □q ∧ r` is
`(□p ≺ □q) ∧ r`, and `¬□p ≺ □q` doesn't parse, but `¬(□p ≺ □q)` does. The two libraries share
no code, so that the verifier's `GLTableau` is not touched.

### The rules

The tableau has GL's rules and these, where `c` is `□A ≺ □B` or `□A ≼ □B`:

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
it keeps a comparison at a world `n` steps down from costing more than `n + 2` branches.

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
is `¬(□p ≺ □q) ∧ □q → □¬(□p ≺ □q)`.

In a model, the rules say that the comparisons that hold at a world lie between two orders of
the boxed formulas, both read off the path down to it: every boxed formula that held at a world
where another didn't is before it, and no boxed formula is before one that held at a world
where it didn't. These are `<` and `≤` of de Jongh's *A simplification of a completeness proof
of Guaspari and Solovay* (1987), Lemma 4, which has that a model of R⁻ puts `≺` and `≼` between
them. Within those bounds the rules leave the comparisons free; R⁻ does not.

What the rules are worth is in the sizes. The Parikh sentence `Π ↔ □□Π ≺ □Π` is provably
provable, `⊡(Π ↔ □□Π ≺ □Π) → □Π`: the tableau here has 9 branches and some 50 lines, and
GL's tableau with the four axioms as premises has 6,000 branches and 14,000 lines.

## Files

- `GLTableau/Formula.lean`: formulas, their parser, and their LaTeX and Lean printers.
- `GLTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, Priest's procedure,
  and the `Tableau` a Lean file defines.
- `GLTableau.lean`: the library, the two modules above.
- `WitnessTableau/Formula.lean`, `WitnessTableau/Tableau.lean`, `WitnessTableau.lean`: the same
  with witness comparisons, in the namespace `Witness`.
