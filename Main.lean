import GLTableau.Server

/-- The server `tableau`: `Tableau.serve` with `GLTableau` imported, so it builds tableaux and
runs the Lean files that define them, to print them. -/
unsafe def main : IO Unit := Tableau.serve #[`GLTableau]
