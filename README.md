# gl-tableau

Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as in
Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□` that
makes them GL tableaux, checked by the sibling [`ProvabilityLogic`](../ProvabilityLogic)
checkout.

    $ lake build
    $ echo '□(□p → p) → □p' | lake exe tableau > lob.lean
    $ ./tex lob.lean > lob.tex
    $ ./verify lob.lean
    □(□p → p) → □p is a theorem of GL

`tableau` reads the sentence from stdin, with letters as sentence letters, `¬ □ ◇ ⊡` binding
tightest, then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` read as `¬⊥` and `⊡A`
as `A ∧ □A`. It writes the tableau as a Lean file, and exits 0 if the tableau closed, so the
sentence is a theorem of GL, 1 if a branch stayed open, 2 if the sentence didn't parse.

`tex` prints the tableau in such a file as a `prooftree` of the `prooftrees` LaTeX package.

`verify` has Lean check what the tableau shows, with `ProvabilityLogic`: that the sentence is
in `LogicGL` if the tableau closed, by the derivation it is in the labelled sequent calculus
`G3KGL`, and that it is not if a branch stayed open, by the finite Kripke countermodel the
branch describes. It prints the claim, then Lean's errors if any; a couple of seconds, most of
it loading Mathlib.

The Lake workspace takes Mathlib and the rest from `../ProvabilityLogic/.lake/packages`, so
that checkout must be built, at least `ProvabilityLogic.Logic.GL.Basic`.

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
- `GLTableau/Check.lean`: a tableau as a derivation in `G3KGL`, an open branch as a
  countermodel, and the theorem `Tableau.verified` that Lean's kernel proves by evaluating
  them; it is what `verify` asks for.
- `Main.lean`: the program `tableau`.
- `tex`, `verify`: run Lean on a tableau's file with one more line.
- `practice-notebook-examples.txt`: sentences to try.
