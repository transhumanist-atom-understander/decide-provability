# gl-tableau

Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as in
Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□` that
makes them GL tableaux, checked by [`ProvabilityLogic`](https://github.com/FormalizedFormalLogic/ProvabilityLogic).
It is a Lean library, `GLTableau`, and a server, `tableau`, that the Python package
[`gltableau`](../wrap-tableau) runs; use it from there.

    $ lake exe cache get   # Mathlib's prebuilt artifacts
    $ lake build           # then Foundation and ProvabilityLogic, from source: slow, once

`tableau` reads requests from stdin, one JSON object per line, and answers each on a line
of stdout. `{"sentence": A}` is answered with `{"closed": ..., "lean": ...}`, the tableau for
`A` as a Lean file, or `{"error": ...}` if `A` doesn't parse: letters are sentence letters,
`¬ □ ◇ ⊡` bind tightest, then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` is read
as `¬⊥` and `⊡A` as `A ∧ □A`. `{"lean": source}` is answered with `{"output": ...,
"errors": ...}`: what the `#eval`s of the Lean file `source` print, and Lean's errors, with
the file's header taken to be `import GLTableau`. That import is loaded once, when the server
starts, which takes a couple of seconds, most of it Mathlib; each request then takes a
fraction of a second. So the tableau in a file `t.lean` is printed as a `prooftree` of the
`prooftrees` LaTeX package by sending the file with `#eval IO.print t.tex` added, and Lean
checks what it shows, that its sentence is in `LogicGL` if it closed, by the derivation it is
in the labelled sequent calculus `G3KGL`, and that it is not if a branch stayed open, by the
finite Kripke countermodel the branch describes, by sending it with
`theorem proof : t.verdict := t.verified` added.

    $ echo '{"sentence": "□(□p → p) → □p"}' | lake exe tableau
    {"closed":true,"lean":"import GLTableau\n\n/-- □(□p → p) → □p is a theorem of GL -/\ndef t : Tableau where ..."}

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
  them.
- `Main.lean`: the server `tableau`.
- `practice-notebook-examples.txt`: sentences to try.
