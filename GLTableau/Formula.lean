import Std.Internal.Parsec

namespace Tableau

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

instance : Coe String Formula := ⟨.atom⟩

-- `ProvabilityLogic`'s symbols for the connectives, for the tableau's own code. They are
-- scoped so as not to clash with `ProvabilityLogic`'s own, which the `.lean` files of tableaux
-- avoid by naming the constructors instead.
namespace Notation
scoped notation:max "⊥" => Formula.bot
scoped prefix:max "∼" => Formula.neg
scoped infixr:35 " ⋏ " => Formula.and
scoped infixr:30 " ⋎ " => Formula.or
scoped infixr:25 " 🡒 " => Formula.imp
scoped infix:20 " 🡘 " => Formula.iff
scoped prefix:max "□" => Formula.box
scoped prefix:max "◇" => Formula.dia
end Notation

open Notation

namespace Formula

open Std.Internal.Parsec String in
/-- `¬ □ ◇ ⊡` bind tightest, then `∧`, `∨`, `→`, `↔`, each associating to the right; `⊤` is
`¬⊥` and `⊡A` is `A ∧ □A`. -/
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
    <|> (tok "⊡" *> (fun A => A ⋏ □A) <$> unary)
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
  | atom a => a
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
    | atom _, r | ⊥, r | ∼_, r | □_, r | ◇_, r => r
    | _, r => s!"({r})"

instance : ToString Formula := ⟨render .unicode⟩

/-- `A` as a Lean term naming the constructors, as in the `.lean` file of a tableau. -/
protected def repr : Formula → String
  | atom a => a.quote
  | ⊥ => ".bot"
  | ∼A => s!"(.neg {A.repr})"
  | □A => s!"(.box {A.repr})"
  | ◇A => s!"(.dia {A.repr})"
  | A ⋏ B => s!"(.and {A.repr} {B.repr})"
  | A ⋎ B => s!"(.or {A.repr} {B.repr})"
  | A 🡒 B => s!"(.imp {A.repr} {B.repr})"
  | A 🡘 B => s!"(.iff {A.repr} {B.repr})"

instance : Repr Formula := ⟨fun A _ => A.repr⟩

end Formula

end Tableau
