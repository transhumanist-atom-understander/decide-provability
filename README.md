# decide-provability

Priest-style labelled tableaux for sentences of GL (Gödel–Löb provability logic), as in
Priest's *An Introduction to Non-Classical Logic* §1.4 and §2.4, with the rule for `¬□` that
makes them GL tableaux. It is a Lean library, `GLTableau`, and a server, `tableau`, that the
Python package `gltableau` of
[wrap-provability](https://github.com/transhumanist-atom-understander/wrap-provability) runs;
use it from there. It depends on nothing but Lean, so it builds in seconds:

    $ lake build

Having Lean check what a tableau shows is the separate project
[verify-provability](https://github.com/transhumanist-atom-understander/verify-provability),
which depends on this one and on `ProvabilityLogic`, hence Mathlib.

`tableau` reads requests from stdin, one JSON object per line, and answers each on a line
of stdout. `{"sentence": A}` is answered with `{"closed": ..., "lean": ...}`, the tableau for
`A` as a Lean file, or `{"error": ...}` if `A` doesn't parse: letters are sentence letters,
`¬ □ ◇ ⊡` bind tightest, then `∧`, `∨`, `→`, `↔`, each associating to the right, `⊤` is read
as `¬⊥` and `⊡A` as `A ∧ □A`. `{"lean": source}` is answered with `{"output": ...,
"errors": ...}`: what the `#eval`s of the Lean file `source` print, and Lean's errors, with
the file's own `import`s ignored in favour of `GLTableau`, loaded once, when the server
starts; each request then takes a fraction of a second. So the tableau in a file `t.lean` is
printed as a `prooftree` of the `prooftrees` LaTeX package by sending the file with
`#eval IO.print t.tex` added.

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
- `GLTableau.lean`: the library the Lean files of tableaux import: the two modules above.
- `GLTableau/Server.lean`: `Tableau.serve`, the request loop, given the modules to load;
  `verify-provability` runs it too, with its own modules.
- `Main.lean`: the server `tableau`, `Tableau.serve` with `GLTableau`.
