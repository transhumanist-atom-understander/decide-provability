import REPL.Main
import RTableau

/-! The executable `repl`: the Lean REPL, whose `main` this is, with `RTableau` linked in.

The REPL evaluates Lean by interpreting it, except where the code it calls is compiled into the
executable it is. Its own executable has only the REPL in it, and interprets a library that it
imports. This one has `RTableau` too, so a tableau is built by compiled code. It has to be
built again when the library changes, as `lake build` does: it runs the library that it was
linked with, whatever the REPL imports. -/
