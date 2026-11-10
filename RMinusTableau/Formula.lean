import Std.Internal.Parsec

namespace RMinus.Tableau

/-- A formula of R⁻: a formula of GL, or a witness comparison of two boxed formulas. -/
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
  /-- `□A ≺ □B`: `□A` is witnessed before `□B` is. -/
  | prec (A B : Formula)
  /-- `□A ≼ □B`: `□A` is witnessed, and `□B` is not witnessed before it. -/
  | preceq (A B : Formula)
  deriving DecidableEq

instance : Coe String Formula := ⟨.atom⟩

-- The symbols of `GLTableau` for the connectives, with the witness comparisons, which are
-- written with the boxes of the formulas they compare.
namespace Notation
scoped notation:max "⊥" => Formula.bot
scoped prefix:max "∼" => Formula.neg
scoped infixr:35 " ⋏ " => Formula.and
scoped infixr:30 " ⋎ " => Formula.or
scoped infixr:25 " 🡒 " => Formula.imp
scoped infix:20 " 🡘 " => Formula.iff
scoped prefix:max "□" => Formula.box
scoped prefix:max "◇" => Formula.dia
scoped notation:40 "□" A:max " ≺ " "□" B:max => Formula.prec A B
scoped notation:40 "□" A:max " ≼ " "□" B:max => Formula.preceq A B
end Notation

open Notation

namespace Formula

open Std.Internal.Parsec String in
/-- The sentences of `GLTableau`, with `□A ≺ □B` and `□A ≼ □B`, which bind tighter than `∧` and
looser than `¬ □ ◇ ⊡`, so that what they compare must be written as boxed formulas. -/
partial def parse (s : String) : Except String Formula := (ws *> formula <* eof).run s
where
  formula : Parser Formula := binary [("↔", iff), ("→", imp), ("∨", or), ("∧", and)]
  /-- Formulas whose binary connectives are from `ops`, loosest first. -/
  binary : List (String × (Formula → Formula → Formula)) → Parser Formula
    | [] => comparison
    | ops@((sym, op) :: rest) => do
      let A ← binary rest
      (do tok sym; pure (op A (← binary ops))) <|> pure A
  comparison : Parser Formula := do
    let a ← unary
    (tok "≺" *> compare prec a) <|> (tok "≼" *> compare preceq a) <|> pure a
  /-- `a` compared, by `op`, with the formula that comes next. -/
  compare (op : Formula → Formula → Formula) (a : Formula) : Parser Formula := do
    match a, ← unary with
    | □A, □B => pure (op A B)
    | _, _ => fail "≺ and ≼ compare boxed formulas"
  unary : Parser Formula :=
    (tok "¬" *> neg <$> unary) <|> (tok "□" *> box <$> unary) <|> (tok "◇" *> dia <$> unary)
    <|> (tok "⊡" *> (fun A => A ⋏ □A) <$> unary)
    <|> (tok "⊥" *> pure ⊥) <|> (tok "⊤" *> pure ∼⊥)
    <|> (tok "(" *> formula <* tok ")")
    <|> atom <$> (many1Chars (satisfy fun c => !c.isWhitespace && !"()¬□◇⊡⊥⊤∧∨→↔≺≼".contains c) <* ws)
  tok (s : String) : Parser Unit := skipString s <* ws

/-- How to spell the connectives. -/
structure Style where
  (neg box dia bot and or imp iff prec preceq : String)

def Style.unicode : Style :=
  { neg := "¬", box := "□", dia := "◇", bot := "⊥", and := " ∧ ", or := " ∨ ", imp := " → ", iff := " ↔ ",
    prec := " ≺ ", preceq := " ≼ " }

def Style.tex : Style :=
  { neg := "\\lnot ", box := "\\Box ", dia := "\\Diamond ", bot := "\\bot",
    and := " \\land ", or := " \\lor ", imp := " \\to ", iff := " \\leftrightarrow ",
    prec := " \\prec ", preceq := " \\preccurlyeq " }

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
  | □A ≺ □B => s.box ++ operand A (render s A) ++ s.prec ++ s.box ++ operand B (render s B)
  | □A ≼ □B => s.box ++ operand A (render s A) ++ s.preceq ++ s.box ++ operand B (render s B)
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
  | □A ≺ □B => s!"(.prec {A.repr} {B.repr})"
  | □A ≼ □B => s!"(.preceq {A.repr} {B.repr})"

instance : Repr Formula := ⟨fun A _ => A.repr⟩

/-- `□A ≺ □B` if `strict`, else `□A ≼ □B`. -/
def compare (strict : Bool) (A B : Formula) : Formula := if strict then □A ≺ □B else □A ≼ □B

/-- The pairs `(A, B)` of distinct formulas whose boxes `A` compares, either way round and by
either comparison, each pair once. -/
def compared : Formula → List (Formula × Formula)
  | atom _ | ⊥ => []
  | ∼A | □A | ◇A => A.compared
  | A ⋏ B | A ⋎ B | A 🡒 B | A 🡘 B => merge A.compared B.compared
  | □A ≺ □B | □A ≼ □B => merge (merge A.compared B.compared) (if A = B then [] else [(A, B)])
where
  merge (ps qs : List (Formula × Formula)) : List (Formula × Formula) :=
    ps ++ qs.filter fun (A, B) => (A, B) ∉ ps && (B, A) ∉ ps

end Formula

end RMinus.Tableau
