import GLTableau.Tableau

/-- Reads a sentence of GL from stdin and prints its tableau as a Lean file. Exits 0 if the
tableau closes (the sentence is a theorem), 1 if not, 2 if the sentence doesn't parse. -/
def main : IO UInt32 := do
  match Tableau.Formula.parse (← (← IO.getStdin).readToEnd) with
  | .error e => IO.eprintln e; return 2
  | .ok A =>
    let t := Tableau.of A
    IO.print t.lean
    return if t.tree.isClosed then 0 else 1
