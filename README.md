# gl-tableau

Builds Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as
in Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□`
that makes them GL tableaux. The tableau is built by a compiled Lean program and can be
printed as text, as LaTeX, or as a derivation in the labelled sequent calculus of the sibling
[`ProvabilityLogic`](../ProvabilityLogic) checkout, which Lean then checks.

    $ lake build
    $ echo '□(□p → p) → □p' | ./gltableau.py
    ¬(□(□p → p) → □p), 0
    □(□p → p), 0
    ¬□p, 0
    0r1
    ¬p, 1
    □p, 1
    □p → p, 1
    - ¬□p, 1
      ⊗
    - p, 1
      ⊗

The sentence is read from stdin, with letters as sentence letters, `¬ □ ◇` binding tightest,
then `∧`, `∨`, `→`, `↔`, each associating to the right, and `⊤` read as `¬⊥`. Formulas are
printed Priest's way, with parentheses around every operand that has a binary connective.
Branches below a split are `-` items; `⊗` closes a branch. The exit status is 0 if the tableau closed, so
the sentence is a theorem of GL, 1 if a branch stayed open, 2 if the sentence didn't parse.

    $ echo '□(□p → p) → □p' | ./gltableau.py --tex

prints the tableau as a `prooftree` of the `prooftrees` LaTeX package, with `\lnot`, `\Box`,
`\Diamond`, `\land`, `\lor`, `\to`, `\leftrightarrow`.

    $ echo '□(□p → p) → □p' | ./gltableau.py --lean

prints a Lean file deriving the sentence in `ProvabilityLogic`'s calculus `G3KGL` from the
rules of [`rules.lean`](rules.lean), and

    $ echo '□(□p → p) → □p' | ./gltableau.py --verify
    verified

runs Lean on that file in the `ProvabilityLogic` checkout (`lake env lean`), which takes a
couple of seconds and needs that repo built: `just cache` then `lake build` there. For a
non-theorem the derivation has a `sorry` in it and Lean's warning is printed instead.

From Python, `import gltableau` gives `text`, `tex`, `lean` and `verify`, each taking the
sentence as a string, and `tableau(sentence, *flags)`, which returns the output and whether
the tableau closed.

## The tableau

The tableau starts from `¬A, 0` and applies Priest's rules for `¬¬`, `∧`, `∨`, `→`, `↔` and
their negations, with these modal rules:

    □A, i   irj  ⟹  A, j
    ¬□A, i       ⟹  irj,  ¬A, j,  □A, j        j new
    ◇A, i        ⟹  irj,  A, j,  □¬A, j        j new
    ¬◇A, i       ⟹  □¬A, i
    irj   jrk    ⟹  irk

The rule for `¬□` is Priest's rule for `◇¬`, with the `□A, j` that makes it GL's (so Löb's
theorem goes through). `◇A` is treated as `¬□¬A`, and with `A` itself a negation `¬B` the two
negations cancel: `◇¬B, i` gives `¬B, j` and `□B, j`. Transitivity is Priest's rule for K4.
The branch closes on `A, i` and `¬A, i`, or on `⊥, i`.

Each line is expanded once; `□A, i` lines and `irj` lines each look for the other, so
whichever comes second finds the first. Lines are expanded in order of appearance, except
that rules that don't branch go before the rules for `¬□` and `◇` (which start a new world),
and those before rules that branch. Branching rules add their lines even when they are
already there; the modal rules only add lines that are new.

## The derivation

A branch is a labelled sequent of `ProvabilityLogic`: a line `A, i` is `i ∶ A` on the left,
`¬A, i` is `i ∶ A` on the right, and `irj` is a relational atom. Read from the bottom up,
each tableau rule is one rule of `G3KGL`, with the rule for `¬□` being its `boxRLob` and the
transitivity rule its `trans`; `□A, i` makes one `boxL` per world reached. `rules.lean`
states the calculus's rules in this tableau-shaped form, with the principal formula found
on the branch by a membership proof (`by decide`) rather than being the last formula added.
When a rule copies a negated formula `¬B` to the left (as `∧` does to `¬p ∧ q`) the line
`¬B, i` is moved to the right as `i ∶ B` by `negL_mem`, so that later rules find it where the
tableau's reading expects it.

The derivation is of the sentence with `◇B` written as `¬□¬B` — or as `¬□C` if `B` is `¬C` —
and `⊤` as `¬⊥`, which is how `Formula.lean` translates it to `ProvabilityLogic`'s formulas.
Checking it is Lean type-checking the proof term: there is no separate verifier.

## Files

- `GLTableau/Formula.lean`: formulas, their parser, and their three printers.
- `GLTableau/Tableau.lean`: lines, the tree a tableau builds, the rules, Priest's procedure.
- `GLTableau/Print.lean`: the tree as text, as LaTeX, and as a derivation.
- `Main.lean`: the command-line program `tableau` that `lake build` puts in `.lake/build/bin`.
- `rules.lean`: the tableau-shaped rules of `G3KGL`, prepended to every derivation.
- `gltableau.py`: the Python module and command.
- `tests.csv`, `test.py`: sentences with whether they are theorems, checked by tableau and
  by Lean; `crosscheck.py`: random sentences decided by tableau and by the repo's
  `LogicGL.search0`.
