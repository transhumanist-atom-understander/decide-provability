import GLTableau

/-- Reads a sentence from stdin and prints its tableau as text, or with `--tex` as LaTeX, or
with `--lean` as a derivation for `ProvabilityLogic`. Exits 0 if the tableau closes, 1 if
not, 2 if the sentence doesn't parse. -/
def main (args : List String) : IO UInt32 := do
  match Formula.parse (← (← IO.getStdin).getLine) with
  | .error e => IO.eprintln e; return 2
  | .ok A =>
    let t := tableau A
    IO.print <| match args with
      | ["--tex"] => tex A t
      | ["--lean"] => lean A t
      | _ => text A t
    return if t.isClosed then 0 else 1
