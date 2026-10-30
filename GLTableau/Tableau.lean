import GLTableau.Formula

/-- A line of a tableau: `A, i` (`A` holds at world `i`) or `irj` (world `i` sees world `j`). -/
inductive Line
  | fml (i : Nat) (A : Formula)
  | rel (i j : Nat)
  deriving DecidableEq

namespace Line

def render (s : Formula.Style) : Line → String
  | fml i A => s!"{A.render s}, {i}"
  | rel i j => s!"{i}r{j}"

instance : ToString Line := ⟨render .unicode⟩

def worlds : Line → List Nat
  | fml i _ => [i]
  | rel i j => [i, j]

/-- The order of expansion: rules that don't branch, then rules that start a new world, then
rules that branch. -/
def priority : Line → Nat
  | fml _ (∼□_) | fml _ (◇_) => 1
  | fml _ (∼(_ ⋏ _)) | fml _ (_ ⋎ _) | fml _ (_ 🡒 _) | fml _ (_ 🡘 _) | fml _ (∼(_ 🡘 _)) => 2
  | _ => 0

end Line

/-- What Priest's procedure builds below a branch. -/
inductive Tree
  /-- A rule applied to `line`, higher up the branch: the lines each branch gains, and what's
  below them. -/
  | step (line : Line) (branches : List (List Line × Tree))
  /-- `A, i` and `¬A, i` are both on the branch, or `A` is `⊥`. -/
  | closed (i : Nat) (A : Formula)
  /-- No rule applies: the branch is open. -/
  | exhausted
  deriving Inhabited

partial def Tree.isClosed : Tree → Bool
  | step _ branches => branches.all (·.2.isClosed)
  | closed .. => true
  | exhausted => false

/-- A world `i` where `A, i` and `¬A, i`, or `⊥, i`, are on the branch. -/
def clash (branch : List Line) : Option (Nat × Formula) :=
  branch.findSome? fun
    | .fml i ⊥ => some (i, ⊥)
    | .fml i (∼A) => if .fml i A ∈ branch then some (i, A) else none
    | _ => none

/-- The lines of `new` not yet on the branch. -/
def absent (branch new : List Line) : List Line := (new.filter (· ∉ branch)).eraseDups

/-- A world not yet on the branch. -/
def fresh (branch : List Line) : Nat := (branch.flatMap Line.worlds).max?.getD 0 + 1

/-- Priest's rules, with the GL rule for `¬□`, the matching rule for `◇`, and transitivity:
the new lines of each branch below `l`, so `[[]]` when there is nothing to add. `□` lines
and `irj` lines each look for the other, so whichever comes second finds the first. -/
def rule (l : Line) (branch : List Line) : List (List Line) :=
  match l with
  | .fml i A =>
    let j := fresh branch
    match A with
    | ∼∼B => [[.fml i B]]
    | B ⋏ C => [[.fml i B, .fml i C]]
    | ∼(B ⋏ C) => [[.fml i ∼B], [.fml i ∼C]]
    | B ⋎ C => [[.fml i B], [.fml i C]]
    | ∼(B ⋎ C) => [[.fml i ∼B, .fml i ∼C]]
    | B 🡒 C => [[.fml i ∼B], [.fml i C]]
    | ∼(B 🡒 C) => [[.fml i B, .fml i ∼C]]
    | B 🡘 C => [[.fml i B, .fml i C], [.fml i ∼B, .fml i ∼C]]
    | ∼(B 🡘 C) => [[.fml i B, .fml i ∼C], [.fml i ∼B, .fml i C]]
    | □B => [absent branch <| branch.filterMap fun
        | .rel k j => if k = i then some (.fml j B) else none
        | _ => none]
    | ∼□B => [[.rel i j, .fml j ∼B, .fml j □B]]
    | ◇B => [[.rel i j, .fml j B, .fml j □B.negate]]
    | ∼◇B => [[.fml i □B.negate]]
    | _ => [[]]
  | .rel i j => [absent branch <| branch.filterMap fun
      | .fml k □B => if k = i then some (.fml j B) else none
      | .rel k m => if m = i then some (.rel k j) else if k = j then some (.rel i m) else none
      | _ => none]

/-- Priest's procedure below `branch` (oldest line first): close if there is a clash, else
expand the first line of `todo` by priority, until none is left. -/
partial def expand (branch todo : List Line) : Tree :=
  if let some (i, A) := clash branch then .closed i A else
  match todo.mergeSort (·.priority ≤ ·.priority) with
  | [] => .exhausted
  | l :: todo =>
    match rule l branch with
    | [[]] => expand branch todo
    | branches => .step l <| branches.map fun new => (new, expand (branch ++ new) (todo ++ new))

/-- The tableau below `¬A, 0`. -/
def tableau (A : Formula) : Tree := expand [.fml 0 ∼A] [.fml 0 ∼A]
