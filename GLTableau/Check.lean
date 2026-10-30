import GLTableau.Tableau
import ProvabilityLogic.Logic.GL.Basic

/-!
# Checking a tableau with `ProvabilityLogic`

A branch of a tableau is a labelled sequent of `ProvabilityLogic`'s calculus `G3KGL` for GL: a
line `A, i` is `i ∶ A` on the left, `¬A, i` is `i ∶ A` on the right, and `irj` is a relational
atom. Read upwards, each tableau rule is a rule of the calculus, so a closed tableau is a
derivation of its sentence, which `check` builds, and `certificate` turns it into a proof that
the sentence is in `LogicGL`; an open branch it turns into the finite Kripke countermodel
showing the sentence is not. `verified` has Lean's kernel do the checking, by evaluating
`certificate` with `decide`.
-/

open LogicGL ProofLabelledGentzen

namespace Tableau

/-- `A` as a formula of `ProvabilityLogic`, whose `∧ ∨ ↔ ◇` are abbreviations. -/
def Formula.pl : Tableau.Formula → _root_.Formula String
  | .atom a => .atom a
  | .bot => .bot
  | .neg A => .neg A.pl
  | .and A B => .and A.pl B.pl
  | .or A B => .or A.pl B.pl
  | .imp A B => .imp A.pl B.pl
  | .iff A B => .iff A.pl B.pl
  | .box A => .box A.pl
  | .dia A => .dia A.pl

variable {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula String)}

/-! ### The rules the calculus lacks, in its own terms -/

/-- A derivation of `R ⸴ insert ℓA Γ ⟹ˡ Δ` is one of `R ⸴ Γ ⟹ˡ Δ` when `ℓA ∈ Γ`: they are
the same sequent. -/
def ofMemAnt {ℓA} (h : ℓA ∈ Γ) (p : ⊢ˡᵍ[GL]! (R ⸴ insert ℓA Γ ⟹ˡ Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  Finset.insert_eq_of_mem h ▸ p

def ofMemSuc {ℓA} (h : ℓA ∈ Δ) (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert ℓA Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  Finset.insert_eq_of_mem h ▸ p

/-- `A ↔ B, x ⟹ A, x; B, x | ¬A, x; ¬B, x` -/
def iffL {x A B} (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) (insert (x ∶ B) Γ) ⟹ˡ Δ))
    (q : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) (insert (x ∶ B) Δ))) :
    ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A 🡘 B) Γ ⟹ˡ Δ) := by
  apply andL
  apply impL
  · apply impL
    · exact Finset.insert_comm (x ∶ A) (x ∶ B) Δ ▸ q
    · exact union x A
  · apply ofMemAnt (ℓA := x ∶ B 🡒 A) (by grind)
    apply impL
    · exact union x B
    · exact wkAnt p

/-- `¬(A ↔ B), x ⟹ A, x; ¬B, x | ¬A, x; B, x` -/
def iffR {x A B} (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ))
    (q : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ B) Γ ⟹ˡ insert (x ∶ A) Δ)) :
    ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A 🡘 B) Δ) :=
  andR (impR p) (impR q)

/-- GL's rule for `◇`: `◇A, x ⟹ xry; A, y; □¬A, y`, `y` new. -/
def diaL (x y A) (hy : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □(∼A)) Δ).labels)
    (p : ⊢ˡᵍ[GL]! (insert (x, y) R ⸴ insert (y ∶ A) (insert (y ∶ □(∼A)) Γ) ⟹ˡ Δ)) :
    ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ ◇A) Γ ⟹ˡ Δ) :=
  negL (boxRLob x y (∼A) hy (negR p))

/-! ### A tableau as a derivation -/

/-- `f` of a proof of `p`, if `p` holds. -/
def given (p : Prop) [Decidable p] (f : p → Option α) : Option α := if h : p then f h else none

/-- The derivation `k` of the sequent with `ℓA` on the left, as one of the sequent itself,
where `ℓA` must already be. -/
def ant (ℓA) (k : Option (⊢ˡᵍ[GL]! (R ⸴ insert ℓA Γ ⟹ˡ Δ))) : Option (⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ)) :=
  given (ℓA ∈ Γ) fun h => ofMemAnt h <$> k

def suc (ℓA) (k : Option (⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert ℓA Δ))) : Option (⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ)) :=
  given (ℓA ∈ Δ) fun h => ofMemSuc h <$> k

/-- `Γ` with the lines `As` at `x` on the left, in order. -/
abbrev left (x : Label) (As : List Tableau.Formula) (Γ : Finset (LabelledFormula String)) :=
  As.foldl (fun Γ A => insert (x ∶ A.pl) Γ) Γ

theorem subset_left (x As) : Γ ⊆ left x As Γ := by
  induction As generalizing Γ with
  | nil => exact Finset.Subset.refl _
  | cons _ _ ih => exact (Finset.subset_insert _ _).trans (ih ..)

/-- A derivation of each sequent, when there is one to give. -/
abbrev Deriver :=
  ∀ (R : Finset LabelRel) (Γ Δ : Finset (LabelledFormula String)), Option (⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ))

/-- The derivation, by `k`, of the sequent after the lines `As` at `x` are put on the left,
with each negation `¬C` also put on the right as `C`, where the reading of the branch has it. -/
def adds (x : Label) : (As : List Tableau.Formula) → Deriver →
    ∀ R Γ Δ, Option (⊢ˡᵍ[GL]! (R ⸴ left x As Γ ⟹ˡ Δ))
  | [], k, R, Γ, Δ => k R Γ Δ
  | .neg C :: As, k, R, Γ, Δ =>
    (ofMemAnt (subset_left x As (Finset.mem_insert_self _ _)) ∘ negL) <$>
      adds x As k R (insert (x ∶ C.pl.neg) Γ) (insert (x ∶ C.pl) Δ)
  | A :: As, k, R, Γ, Δ => adds x As k R (insert (x ∶ A.pl) Γ) Δ

/-- The derivation, by `k`, after the lines `new` that `l` (`□B, i` or `irj`) adds, each by
its rule: `boxL` for `B, j` and `trans` for `irk`. -/
def after (l : Line) : List Line → Deriver → Deriver
  | [], k => k
  | .fml j B :: ls, k => fun R Γ Δ =>
    let i := match l with | .fml i _ | .rel i _ => i
    given ((i, j) ∈ R) fun hij => given ((i ∶ B.pl.box) ∈ Γ) fun hB =>
      boxL i j B.pl hij hB <$> adds j [B] (after l ls k) R Γ Δ
  | .rel a b :: ls, k => fun R Γ Δ =>
    match l with
    | .rel i j =>
      let y := if b = j then i else j
      given ((a, y) ∈ R) fun h₁ => given ((y, b) ∈ R) fun h₂ =>
        trans a y b h₁ h₂ <$> after l ls k (insert (a, b) R) Γ Δ
    | _ => none

/-- The derivation of `R ⸴ Γ ⟹ˡ Δ` that the tree `t` below it describes, if it is closed. -/
def check : Tree → Deriver
  | .closed i .bot, _, Γ, _ => given ((i ∶ _root_.Formula.bot) ∈ Γ) fun h => some (botL_mem i h)
  | .closed i (.neg B), _, _, Δ => suc (i ∶ B.pl.neg) <| given ((i ∶ B.pl) ∈ Δ) fun h =>
      some (negR (union i B.pl (Finset.mem_insert_self _ _) h))
  | .closed i B, _, Γ, Δ => given ((i ∶ B.pl) ∈ Γ) fun hΓ => given ((i ∶ B.pl) ∈ Δ) fun hΔ =>
      some (union i B.pl hΓ hΔ)
  | .exhausted, _, _, _ => none
  | .step (.fml i A) new t, R, Γ, Δ =>
    match A, new with
    | .neg (.neg B), _ => suc (i ∶ B.pl.neg) (negR <$> adds i [B] (check t) R Γ Δ)
    | .and B C, _ => ant (i ∶ (B.and C).pl) (andL <$> adds i [C, B] (check t) R Γ Δ)
    | .neg (.or B C), _ => suc (i ∶ (B.or C).pl)
        (orR <$> check t R Γ (insert (i ∶ B.pl) (insert (i ∶ C.pl) Δ)))
    | .neg (.imp B C), _ => suc (i ∶ (B.imp C).pl) (impR <$> adds i [B] (check t) R Γ (insert (i ∶ C.pl) Δ))
    | .neg (.box B), .rel _ j :: _ => suc (i ∶ B.pl.box) <|
        given (j ∉ (R ⸴ Γ ⟹ˡ insert (i ∶ B.pl.box) Δ).labels) fun hj =>
          boxRLob i j B.pl hj <$> check t (insert (i, j) R) (insert (j ∶ B.pl.box) Γ) (insert (j ∶ B.pl) Δ)
    | .dia B, .rel _ j :: _ => ant (i ∶ B.dia.pl) <|
        given (j ∉ (R ⸴ Γ ⟹ˡ insert (i ∶ B.pl.neg.box) Δ).labels) fun hj =>
          diaL i j B.pl hj <$> adds j [B] (check t) (insert (i, j) R) (insert (j ∶ B.pl.neg.box) Γ) Δ
    | .neg (.dia B), _ => suc (i ∶ B.dia.pl) (negR <$> check t R (insert (i ∶ B.pl.neg.box) Γ) Δ)
    | .box _, _ => after (.fml i A) new (check t) R Γ Δ
    | _, _ => none
  | .step (.rel i j) new t, R, Γ, Δ => after (.rel i j) new (check t) R Γ Δ
  | .split (.fml i A) _ t₁ _ t₂, R, Γ, Δ =>
    match A with
    | .neg (.and B C) => suc (i ∶ (B.and C).pl)
        (andR <$> check t₁ R Γ (insert (i ∶ B.pl) Δ) <*> check t₂ R Γ (insert (i ∶ C.pl) Δ))
    | .or B C => ant (i ∶ (B.or C).pl)
        (orL <$> adds i [B] (check t₁) R Γ Δ <*> adds i [C] (check t₂) R Γ Δ)
    | .imp B C => ant (i ∶ (B.imp C).pl)
        (impL <$> check t₁ R Γ (insert (i ∶ B.pl) Δ) <*> adds i [C] (check t₂) R Γ Δ)
    | .iff B C => ant (i ∶ (B.iff C).pl)
        (iffL <$> adds i [C, B] (check t₁) R Γ Δ <*> check t₂ R Γ (insert (i ∶ B.pl) (insert (i ∶ C.pl) Δ)))
    | .neg (.iff B C) => suc (i ∶ (B.iff C).pl)
        (iffR <$> adds i [B] (check t₁) R Γ (insert (i ∶ C.pl) Δ) <*> adds i [C] (check t₂) R Γ (insert (i ∶ B.pl) Δ))
    | _ => none
  | .split .., _, _, _ => none

/-! ### An open branch as a countermodel -/

/-- The lines of the first open branch of `t`, oldest first. -/
def branch (t : Tableau) : List Line := .fml 0 (.neg t.sentence) :: t.tree.openBranch.getD []

/-- The Kripke model the open branch describes: a world for each label, `irj` as the relation
and `p, i` as the valuation. -/
abbrev model (t : Tableau) : Model (Fin ((t.branch.flatMap Line.worlds).max?.getD 0 + 1)) String where
  Rel' i j := Line.rel i j ∈ t.branch
  Val' i a := Line.fml i (.atom a) ∈ t.branch

open Model.World in
instance decForces [Nonempty κ] [Fintype κ] (M : Model κ String) [DecidableRel M.Rel']
    [∀ x a, Decidable (M.Val' x a)] (x : κ) : ∀ A, Decidable (Forces M x A)
  | .atom a => inferInstanceAs (Decidable (M.Val' x a))
  | .bot => inferInstanceAs (Decidable False)
  | .imp A B => haveI := decForces M x A; haveI := decForces M x B
      inferInstanceAs (Decidable (Forces M x A → Forces M x B))
  | .box A => haveI := fun y => decForces M y A
      inferInstanceAs (Decidable (∀ y, x ≺ y → Forces M y A))

/-! ### The verdict -/

/-- What a tableau shows about its sentence when it is closed, and when it is not. -/
def Verdict (A : _root_.Formula String) : Bool → Prop
  | true => A ∈ LogicGL
  | false => A ∉ LogicGL

abbrev verdict (t : Tableau) : Prop := Verdict t.sentence.pl t.tree.isClosed

def claim (t : Tableau) : String :=
  s!"{t.sentence} is {if t.tree.isClosed then "" else "not "}a theorem of GL"

/-- The derivation of a closed tableau, or the countermodel of an open one, as a proof of its
verdict, if its rules were applied properly. -/
def certificate (t : Tableau) : Option (PLift (Verdict t.sentence.pl t.tree.isClosed)) :=
  match t.tree.isClosed with
  | true => (check t.tree ∅ ∅ {0 ∶ t.sentence.pl}).map fun p => ⟨iff_provableLabelledGentzen.mpr ⟨p⟩⟩
  | false =>
    given (∀ x y z : t.model.World, x ≺ y → y ≺ z → x ≺ z) fun trans =>
    given (∀ x : t.model.World, ¬x ≺ x) fun irrefl =>
    given (¬Model.World.Forces t.model 0 t.sentence.pl) fun h =>
      have : t.model.IsFiniteGL := { trans, irrefl }
      some ⟨not_mem_of_concrete_not_forces t.model h⟩

/-- The verdict of `t`, proved by Lean's kernel evaluating its certificate. -/
theorem verified (t : Tableau) (h : t.certificate.isSome := by decide +kernel) : t.verdict :=
  (t.certificate.get h).down

end Tableau
