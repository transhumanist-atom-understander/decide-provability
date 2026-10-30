import ProvabilityLogic.LabelledGentzen.GL.Basic

/-!
# Tableau-shaped rules for `ProvabilityLogic`'s sequent calculus for GL

A tableau branch is a labelled sequent: a line `A, i` is `i ∶ A` on the left and `¬A, i` is
`i ∶ A` on the right, so a tableau rule is a sequent rule read upwards. The calculus's rules
expect their principal formula to be the last one inserted, which on a branch it rarely is,
so each rule here takes instead a proof that the formula is there (`by decide` will find it)
and the world and formulas explicitly, which lets Lean check the proof terms `tableau --lean`
writes without inferring anything.
-/

namespace LogicGL.ProofLabelledGentzen

open Formula

variable {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula ℕ)}

/-- A derivation of `R ⸴ insert ℓA Γ ⟹ˡ Δ` is one of `R ⸴ Γ ⟹ˡ Δ` when `ℓA ∈ Γ`: they are
the same sequent. -/
def ofMemAnt {ℓA} (h : ℓA ∈ Γ) (p : ⊢ˡᵍ[GL]! (R ⸴ insert ℓA Γ ⟹ˡ Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  Finset.insert_eq_of_mem h ▸ p

def ofMemSuc {ℓA} (h : ℓA ∈ Δ) (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert ℓA Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  Finset.insert_eq_of_mem h ▸ p

/-- A line `¬A, x` that a rule has put on the left belongs on the right. -/
def negL_mem (x A) (h : (x ∶ ∼A) ∈ Γ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemAnt h (negL p)

/-- `¬¬A, x ⟹ A, x`; also `¬◇A, x ⟹ □¬A, x`, since `◇A` is `¬□¬A`. -/
def negR_mem (x A) (h : (x ∶ ∼A) ∈ Δ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) Γ ⟹ˡ Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (negR p)

/-- `A ∧ B, x ⟹ A, x; B, x` -/
def andL_mem (x A B) (h : (x ∶ A ⋏ B) ∈ Γ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) (insert (x ∶ B) Γ) ⟹ˡ Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemAnt h (andL p)

/-- `¬(A ∧ B), x ⟹ ¬A, x | ¬B, x` -/
def andR_mem (x A B) (h : (x ∶ A ⋏ B) ∈ Δ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (q : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ B) Δ)) :
  ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (andR p q)

/-- `A ∨ B, x ⟹ A, x | B, x` -/
def orL_mem (x A B) (h : (x ∶ A ⋎ B) ∈ Γ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) Γ ⟹ˡ Δ)) (q : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) :
  ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemAnt h (orL p q)

/-- `¬(A ∨ B), x ⟹ ¬A, x; ¬B, x` -/
def orR_mem (x A B) (h : (x ∶ A ⋎ B) ∈ Δ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) (insert (x ∶ B) Δ))) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (orR p)

/-- `A → B, x ⟹ ¬A, x | B, x` -/
def impL_mem (x A B) (h : (x ∶ A 🡒 B) ∈ Γ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (q : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) :
  ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemAnt h (impL p q)

/-- `¬(A → B), x ⟹ A, x; ¬B, x` -/
def impR_mem (x A B) (h : (x ∶ A 🡒 B) ∈ Δ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (impR p)

/-- `A ↔ B, x ⟹ A, x; B, x | ¬A, x; ¬B, x` -/
def iffL_mem (x A B) (h : (x ∶ A 🡘 B) ∈ Γ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) (insert (x ∶ B) Γ) ⟹ˡ Δ))
  (q : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ insert (x ∶ A) (insert (x ∶ B) Δ))) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) := by
  apply ofMemAnt h;
  apply andL;
  apply impL;
  . apply impL;
    . exact Finset.insert_comm (x ∶ A) (x ∶ B) Δ ▸ q;
    . exact union x A;
  . apply ofMemAnt (ℓA := x ∶ B 🡒 A) (by grind);
    apply impL;
    . exact union x B;
    . exact wkAnt p;

/-- `¬(A ↔ B), x ⟹ A, x; ¬B, x | ¬A, x; B, x` -/
def iffR_mem (x A B) (h : (x ∶ A 🡘 B) ∈ Δ)
  (p : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ))
  (q : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ B) Γ ⟹ˡ insert (x ∶ A) Δ)) : ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (andR (impR p) (impR q))

/-- GL's rule `¬□A, x ⟹ xry; ¬A, y; □A, y`, `y` new. -/
def boxR_mem (x y A) (h : (x ∶ □A) ∈ Δ) (hy : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
  (p : ⊢ˡᵍ[GL]! (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)) :
  ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemSuc h (boxRLob x y A hy p)

/-- The same for `◇¬A, x`, which is `¬□A` on the left: `xry; ¬A, y; □A, y`. For `◇B, x` with
`B` not a negation, `A` is `¬B` and the premise's `¬B, y` on the right is turned into `B, y`
on the left by `negR_mem`. -/
def diaL_mem (x y A) (h : (x ∶ ∼□A) ∈ Γ) (hy : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
  (p : ⊢ˡᵍ[GL]! (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)) :
  ⊢ˡᵍ[GL]! (R ⸴ Γ ⟹ˡ Δ) :=
  ofMemAnt h (negL (boxRLob x y A hy p))

-- `□A, x; xry ⟹ A, y` is the calculus's own `boxL`, `xry; yrz ⟹ xrz` its `trans`, and a
-- branch closes by `union` (`A, x` and `¬A, x`) or `botL_mem` (`⊥, x`).

end LogicGL.ProofLabelledGentzen

open LogicGL.ProofLabelledGentzen Formula
