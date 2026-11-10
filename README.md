# decide-provability

Priest-style labelled tableaux for sentences of two provability logics. One is GL (Gödel–Löb
provability logic), with tableaux as in Priest's *An Introduction to Non-Classical Logic* §1.4
and §2.4 and the rule for `¬□` that makes them GL tableaux. The other is R⁻, the logic of
Guaspari and Solovay's *Rosser sentences* (1979): GL with the witness comparisons `□A ≺ □B` and
`□A ≼ □B` that Rosser sentences are made of. They are two Lean libraries, `GLTableau` and
`RMinusTableau`, that the Python package `tableau` of
[wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability)
uses; use them from there. They depend on nothing but Lean and the
[Lean REPL](https://github.com/augustepoiroux/repl), so they build in seconds:

    $ lake build

Having Lean check what a tableau shows is the separate project
[verify-provability](https://github.com/transhumanist-atom-understander/verify-provability),
which depends on this one and on `ProvabilityLogic`, hence Mathlib. It checks GL tableaux;
nothing checks R⁻ tableaux yet.

The wrapper runs the REPL in this project, with one of the libraries imported once, and has it
evaluate Lean. `#eval Tableau.decide A` prints the GL tableau for the sentence `A` as a Lean
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

`RMinusTableau` is used the same way, with `RMinus.Tableau` for `Tableau`:
`#eval RMinus.Tableau.decide A` prints the R⁻ tableau for `A` as a Lean file that imports
`RMinusTableau` and defines `t : RMinus.Tableau`. Its sentences are GL's with `□A ≺ □B` and
`□A ≼ □B`, which bind tighter than `∧` and looser than `¬ □ ◇ ⊡`, and what they compare must be
written as boxed formulas: `□p ≺ □q ∧ r` is `(□p ≺ □q) ∧ r`, and `¬□p ≺ □q` doesn't parse, but
`¬(□p ≺ □q)` does. The two libraries share no code, so that the verifier's `GLTableau` is not
touched by what R⁻ needs.

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

## The R⁻ tableau

`□A ≺ □B` says that `□A` is witnessed before `□B` is, and `□A ≼ □B` that `□A` is witnessed and
`□B` is not witnessed before it: in arithmetic, that there is a proof of `A` with no smaller
proof of `B`. R⁻ is GL with Guaspari and Solovay's axioms for them. A comparison that holds is
provable, as a boxed formula that holds is. `≼` is a total preorder of the boxed formulas that
hold, `≺` is its strict part, and the boxed formulas that hold come before those that don't,
which are not compared.

The tableau has GL's rules and these, where `a`, `b` and `c` are boxed formulas:

    a ≼ b, i   irj        ⟹  a ≼ b, j                   likewise for ≺
    a ≺ b, i              ⟹  a ≼ b, i
    a ≼ b, i              ⟹  a, i
    a ≼ b, i   b ≼ c, i   ⟹  a ≼ c, i                   a ≺ c, i if either is ≺
    ¬(a ≼ a), i           ⟹  ¬a, i
    a, i   ¬b, i          ⟹  a ≺ b, i
                          ⟹  ¬a, i  ¬b, i  |  a ≺ b, i  |  b ≺ a, i  |  a ≼ b, i  b ≼ a, i

and the branch also closes on `a ≺ a, i`. The last is the order rule: it has no premises, and
its four branches are that neither `a` nor `b` is witnessed at `i`, that `a` is witnessed
first, that `b` is, and that they are witnessed together.

The rules that don't branch are applied wherever they can be, except that transitivity never
adds `a ≼ a`, which gives nothing, and the rule for `a, i` and `¬b, i` is only applied in place
of the order rule. The order rule is applied to `a` and `b` at `i` only where a line needs it:
a comparison of `a` and `b` at a world `j`, or the negation of one, needs it at every world
that sees `j`, and the negation needs it at `j` too. It comes after every other rule, at the
earliest world first, so that what a world decides persists to the worlds it sees before they
are asked. It is not applied where all the lines of one of its branches are there already; and
where `a, i` and `¬b, i` are, `a ≺ b, i` is added instead, without branching.

That is enough. On an open branch, say that a boxed formula holds at a world if its formula
holds at every world that world sees, and order the boxed formulas that hold at a world by the
world, on the way down to it, where each first held, and those that first held at the same
world by a total preorder that extends that world's comparisons; there is one, since
transitivity has not given `a ≺ a`. That is a model of R⁻, in Guaspari and Solovay's sense, and
by induction on its formula every line of the branch is true in it. For a comparison at `j`
this is because the order rule, at each world that sees `j`, has said whether its boxed
formulas hold there, and in which order, and what it said has persisted to `j` without closing
the branch; for the negation of one, because of what the order rule said at `j`. So the
sentence fails at world 0 of a model of R⁻, and is not a theorem.

The tree a tableau builds has one more kind of node than GL's, for the order rule, which is
applied to no line: `order i A B`, with what is below each of the four branches for `□A` and
`□B` at `i`.

## Files

- `GLTableau/Formula.lean`: formulas, their parser, and their LaTeX and Lean printers.
- `GLTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, Priest's procedure,
  and the `Tableau` a Lean file defines.
- `GLTableau.lean`: the library, the two modules above.
- `RMinusTableau/Formula.lean`, `RMinusTableau/Tableau.lean`, `RMinusTableau.lean`: the same
  for R⁻, in the namespace `RMinus`.
