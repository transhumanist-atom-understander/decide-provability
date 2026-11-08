import Lean
import GLTableau.Tableau

/-!
# The server

`Tableau.serve` is the loop behind the executable `tableau` of this project and `verify` of
`verify-provability`: it answers requests read from stdin with the Lean modules it was given
imported once, at the start. It is not part of `GLTableau` itself, which the Lean files of
tableaux import, so that they see no more of Lean than they need.
-/

open Lean

namespace Tableau

/-- Reads requests from stdin, one JSON object per line, and answers each on a line of stdout,
until stdin ends. `{"sentence": A}` is answered with `{"closed": ..., "lean": ...}`, the
tableau for `A` as a Lean file, or `{"error": ...}` if `A` doesn't parse. `{"lean": source}`
is answered with `{"output": ..., "errors": ...}`: what the `#eval`s of the Lean file `source`
print, and Lean's errors, where the file's own `import`s are ignored and `modules` are imported
instead, once, when the server starts. -/
unsafe def serve (modules : Array Name) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let request ← IO.ofExcept (Json.parse line)
    let reply ← match request.getObjValAs? String "sentence", request.getObjValAs? String "lean" with
      | .ok A, _ => pure <| match Formula.parse A with
        | .error e => json% { error: $e }
        | .ok A => let t := Tableau.of A; json% { closed: $(t.tree.isClosed), lean: $(t.lean) }
      | _, .ok source => do
        let ctx := Parser.mkInputContext source "<input>"
        let (_, parserState, _) ← Parser.parseHeader ctx
        let s ← Elab.IO.processCommands ctx parserState (Elab.Command.mkState env {} {})
        let mut output := ""
        let mut errors := ""
        for m in s.commandState.messages.toList do
          if m.severity == .information then output := output ++ (← m.data.toString)
          else errors := errors ++ (← m.toString)
        pure <| json% { output: $output, errors: $errors }
      | _, _ => throw <| .userError s!"bad request: {line}"
    IO.println reply.compress
    (← IO.getStdout).flush

end Tableau
