import GLTableau.Tableau

/-- The tableau as text: each line below the last, the branches below a split as `-` items. -/
partial def text (A : Formula) (t : Tree) : String := s!"{Line.fml 0 ∼A}\n" ++ go t ""
where
  go : Tree → String → String
    | .closed .., ind => ind ++ "⊗\n"
    | .exhausted, _ => ""
    | .step _ branches, ind =>
      let (mark, ind') := if branches.length = 1 then ("", ind) else ("- ", ind ++ "  ")
      String.join <| branches.map fun (new, t) =>
        ind ++ mark ++ String.intercalate ind' (new.map (s!"{·}\n")) ++ go t ind'

/-- The tableau as a `prooftree` of the `prooftrees` LaTeX package: each line a node nested in
the one above, `close` under a closed branch. -/
partial def tex (A : Formula) (t : Tree) : String :=
  "\\begin{prooftree}{not line numbering}" ++ chain [.fml 0 ∼A] 1 (go t 2) ++ "\n\\end{prooftree}"
where
  go : Tree → Nat → String
    | .closed .., _ => ", close"
    | .exhausted, _ => ""
    | .step _ branches, d =>
      String.join <| branches.map fun (new, t) => chain new d (go t (d + new.length))
  /-- The lines nested one in the next, `rest` inside the last. -/
  chain : List Line → Nat → String → String
    | [], _, rest => rest
    | l :: ls, d, rest => s!"\n{"".pushn ' ' (2 * d)}[\{{l.render .tex}}{chain ls (d + 1) rest}]"

/-- The tableau as a derivation in `ProvabilityLogic`'s labelled sequent calculus for GL, as
Lean source for the rules of `rules.lean`. A line `B, i` is `i ∶ B` on the left of the sequent
and `¬B, i` is `i ∶ B` on the right, so each tableau rule is one sequent rule, except that
`□B, i` applies once per world it reaches and `irj` once per `□` at `i` and per relation it
composes with. Side conditions are left to `decide`; an open branch is a `sorry`. -/
partial def lean (A : Formula) (t : Tree) : String :=
  s!"example : ⊢ˡᵍ[GL]! (∅ ⸴ ∅ ⟹ˡ \{0 ∶ {L A}}) :=\n  {(go t).replace "\n" "\n  "}\n"
where
  L := Formula.lean A.atoms
  h := "(by decide)"
  go : Tree → String
    | .closed i ⊥ => s!"botL_mem {i} {h}"
    | .closed i (∼B) => s!"negR_mem {i} {L B} {h} <| union {i} {L B} {h} {h}"
    | .closed i B => s!"union {i} {L B} {h} {h}"
    | .exhausted => "sorry"
    | .step (.fml i A) branches =>
      match A, branches with
      | ∼∼B, [(_, t)] => s!"negR_mem {i} {L B} {h} <|\n{left i B (go t)}"
      | B ⋏ C, [(_, t)] => s!"andL_mem {i} {L B} {L C} {h} <|\n{left i B <| left i C <| go t}"
      | ∼(B ⋏ C), [(_, t), (_, u)] => s!"andR_mem {i} {L B} {L C} {h}\n({go t})\n({go u})"
      | B ⋎ C, [(_, t), (_, u)] => s!"orL_mem {i} {L B} {L C} {h}\n({left i B (go t)})\n({left i C (go u)})"
      | ∼(B ⋎ C), [(_, t)] => s!"orR_mem {i} {L B} {L C} {h} <|\n{go t}"
      | B 🡒 C, [(_, t), (_, u)] => s!"impL_mem {i} {L B} {L C} {h}\n({go t})\n({left i C (go u)})"
      | ∼(B 🡒 C), [(_, t)] => s!"impR_mem {i} {L B} {L C} {h} <|\n{left i B (go t)}"
      | B 🡘 C, [(_, t), (_, u)] =>
        s!"iffL_mem {i} {L B} {L C} {h}\n({left i B <| left i C <| go t})\n({go u})"
      | ∼(B 🡘 C), [(_, t), (_, u)] =>
        s!"iffR_mem {i} {L B} {L C} {h}\n({left i B (go t)})\n({left i C (go u)})"
      | □_, [(new, t)] => new.foldr (boxL i) (go t)
      | ∼□B, [(.rel _ j :: _, t)] => s!"boxR_mem {i} {j} {L B} {h} {h} <|\n{go t}"
      | ◇B, [(.rel _ j :: _, t)] =>
        s!"diaL_mem {i} {j} {L B.negate} {h} {h} <|\n"
        ++ (if B matches ∼_ then "" else s!"negR_mem {j} {L B} {h} <|\n") ++ go t
      | ∼◇B, [(_, t)] => s!"negR_mem {i} {L □B.negate} {h} <|\n{go t}"
      | _, _ => panic! "no rule"
    | .step (.rel i j) [(new, t)] => new.foldr (fun l p => match l with
        | .fml _ _ => boxL i l p
        | .rel k m => s!"trans {if m = j then s!"{k} {i} {j}" else s!"{i} {j} {m}"} {h} {h} <|\n{p}") (go t)
    | .step _ _ => panic! "no rule"
  /-- `p` after a rule has put `B, j` on the left, where a negation belongs on the right. -/
  left (j : Nat) : Formula → String → String
    | ∼C, p => s!"negL_mem {j} {L C} {h} <|\n{p}"
    | _, p => p
  /-- `l` is `B, j`, from `□B, i`. -/
  boxL (i : Nat) : Line → String → String
    | .fml j B, p => s!"boxL {i} {j} {L B} {h} {h} <|\n{left j B p}"
    | _, p => p
