import Std.Internal.Parsec

/-- A formula of GL, with every connective Priest's tableau rules speak about. -/
inductive Formula
  | atom (name : String)
  | bot
  | neg (A : Formula)
  | and (A B : Formula)
  | or (A B : Formula)
  | imp (A B : Formula)
  | iff (A B : Formula)
  | box (A : Formula)
  | dia (A : Formula)
  deriving DecidableEq

namespace Formula

-- `ProvabilityLogic`'s symbols, at Lean's usual precedences.
prefix:max "#" => atom
notation:max "⊥" => bot
prefix:max "∼" => neg
infixr:35 " ⋏ " => and
infixr:30 " ⋎ " => or
infixr:25 " 🡒 " => imp
infix:20 " 🡘 " => iff
prefix:max "□" => box
prefix:max "◇" => dia

/-- `¬A`, or `B` if `A` is `¬B`. -/
def negate : Formula → Formula
  | ∼A => A
  | A => ∼A

/-- The atoms, in order of first occurrence. -/
def atoms : Formula → List String
  | #a => [a]
  | ⊥ => []
  | ∼A | □A | ◇A => atoms A
  | A ⋏ B | A ⋎ B | A 🡒 B | A 🡘 B => (atoms A ++ atoms B).eraseDups

open Std.Internal.Parsec String in
/-- `¬ □ ◇` bind tightest, then `∧`, `∨`, `→`, `↔`, each associating to the right; `⊤` is `¬⊥`. -/
partial def parse (s : String) : Except String Formula := (ws *> formula <* eof).run s
where
  formula : Parser Formula := binary [("↔", iff), ("→", imp), ("∨", or), ("∧", and)]
  /-- Formulas whose binary connectives are from `ops`, loosest first. -/
  binary : List (String × (Formula → Formula → Formula)) → Parser Formula
    | [] => unary
    | ops@((sym, op) :: rest) => do
      let A ← binary rest
      (do tok sym; pure (op A (← binary ops))) <|> pure A
  unary : Parser Formula :=
    (tok "¬" *> neg <$> unary) <|> (tok "□" *> box <$> unary) <|> (tok "◇" *> dia <$> unary)
    <|> (tok "⊥" *> pure ⊥) <|> (tok "⊤" *> pure ∼⊥)
    <|> (tok "(" *> formula <* tok ")")
    <|> atom <$> (many1Chars asciiLetter <* ws)
  tok (s : String) : Parser Unit := skipString s <* ws

/-- How to spell the connectives. -/
structure Style where
  (neg box dia bot and or imp iff : String)

def Style.unicode : Style :=
  { neg := "¬", box := "□", dia := "◇", bot := "⊥", and := " ∧ ", or := " ∨ ", imp := " → ", iff := " ↔ " }

def Style.tex : Style :=
  { neg := "\\lnot ", box := "\\Box ", dia := "\\Diamond ", bot := "\\bot",
    and := " \\land ", or := " \\lor ", imp := " \\to ", iff := " \\leftrightarrow " }

/-- `A` in style `s`, with parentheses around any operand that has a binary connective. -/
def render (s : Style) : Formula → String
  | #a => a
  | ⊥ => s.bot
  | ∼A => s.neg ++ operand A (render s A)
  | □A => s.box ++ operand A (render s A)
  | ◇A => s.dia ++ operand A (render s A)
  | A ⋏ B => operand A (render s A) ++ s.and ++ operand B (render s B)
  | A ⋎ B => operand A (render s A) ++ s.or ++ operand B (render s B)
  | A 🡒 B => operand A (render s A) ++ s.imp ++ operand B (render s B)
  | A 🡘 B => operand A (render s A) ++ s.iff ++ operand B (render s B)
where
  /-- The operand `A`, rendered as `r`, parenthesized if it has a binary connective. -/
  operand : Formula → String → String
    | #_, r | ⊥, r | ∼_, r | □_, r | ◇_, r => r
    | _, r => s!"({r})"

instance : ToString Formula := ⟨render .unicode⟩

/-- `A` as a `Formula ℕ` of `ProvabilityLogic`, fully parenthesized, the atoms numbered by their
place in `atoms`. `◇A` becomes `¬□¬A` with the inner `¬` cancelled by `negate`, as in the
tableau rule for `◇`. -/
def lean (atoms : List String) : Formula → String
  | #a => s!"(#{atoms.idxOf a})"
  | ⊥ => "(⊥ : Formula ℕ)"
  | ∼A => s!"(∼{lean atoms A})"
  | □A => s!"(□{lean atoms A})"
  | ◇∼A => s!"(∼(□{lean atoms A}))"
  | ◇A => s!"(∼(□(∼{lean atoms A})))"
  | A ⋏ B => s!"({lean atoms A} ⋏ {lean atoms B})"
  | A ⋎ B => s!"({lean atoms A} ⋎ {lean atoms B})"
  | A 🡒 B => s!"({lean atoms A} 🡒 {lean atoms B})"
  | A 🡘 B => s!"({lean atoms A} 🡘 {lean atoms B})"

end Formula
