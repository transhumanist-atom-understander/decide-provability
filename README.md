# decide-provability

Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as in
Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□` that
makes them GL tableaux. It is a Lean library, `GLTableau`, that the Python package `gltableau`
of [wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability)
uses; use it from there. It depends on nothing but Lean and the
[Lean REPL](https://github.com/augustepoiroux/repl), so it builds in seconds:

    $ lake build

Having Lean check what a tableau shows is the separate project
[verify-provability](https://github.com/transhumanist-atom-understander/verify-provability),
which depends on this one and on `ProvabilityLogic`, hence Mathlib.

The wrapper runs the REPL in this project, with `GLTableau` imported once, and has it
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

Each line is expanded once; `□A, i` lines and `irj` lines each look for the other, so
whichever comes second finds the first. Lines are expanded in order of appearance, except that
rules that don't branch go before the rules for `¬□` and `◇`, which start a new world, and
those before rules that branch. Branching rules add their lines even when they are already
there; the modal rules only add lines that are new.

## Files

- `GLTableau/Formula.lean`: formulas, their parser, and their LaTeX and Lean printers.
- `GLTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, Priest's procedure,
  and the `Tableau` a Lean file defines.
- `GLTableau.lean`: the library, the two modules above.
