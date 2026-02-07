module

public import Foundation.ProvabilityLogic.Classification.Trace

@[expose] public section



namespace LO

open FirstOrder (ArithmeticTheory)

namespace Modal

variable {T : ArithmeticTheory} [T.Δ₁] {L : Logic ℕ}

def Formula.standardTheory (T : ArithmeticTheory) [T.Δ₁] (A : Formula ℕ) : ArithmeticTheory := (Set.univ (α := T.StandardRealization)).image (λ f => f A)
def FormulaSet.standardTheory (T : ArithmeticTheory) [T.Δ₁] (X : FormulaSet ℕ) : ArithmeticTheory := ⋃₀ ((Formula.standardTheory T) '' X)

def ArithmeticalConsequence (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) (A : Modal.Formula ℕ) := (𝗜𝚺₁ + X.standardTheory T) ⊢* A.standardTheory T
notation X " ⊢[" T "]* " A => ArithmeticalConsequence T X A

def Logic.arithmeticalCompletion (T : ArithmeticTheory) [T.Δ₁] (L : Logic ℕ) : Modal.Logic ℕ := { A | L ⊢[T]* A }

@[simp, grind .]
lemma Logic.arithmeticalCompletion_isProvabilityLogic : (L.arithmeticalCompletion T).IsProvabilityLogic T (𝗜𝚺₁ + FormulaSet.standardTheory T L) := by
  intro A;
  simp only [
    arithmeticalCompletion, ArithmeticalConsequence, Entailment.ProvableSet,
    Formula.standardTheory, Set.image_univ, Set.mem_range, FormulaSet.standardTheory,
    Set.sUnion_image, forall_exists_index, forall_apply_eq_imp_iff, iff_provable, Set.mem_setOf_eq
  ];

end Modal



namespace ProvabilityLogic

open Modal.Logic (arithmeticalCompletion)

variable {A : Modal.Formula ℕ}
variable {T U : ArithmeticTheory} [T.Δ₁]
-- def lowr (T) (Γ : Modal.FormulaSet ℕ) (A : Modal.Formula ℕ)

lemma lem1 (h : Modal.D ⊬ A) :
  ∃ B : Modal.Formula ℕ,
    B.atoms = A.atoms ∧
    Modal.S ⊬ B ∧
    letI p := B.freshAtom; (Modal.D.sumQuasiNormal {A}) ⊢ B ⋎ (□(.atom p) ➝ (.atom p)) := by
  sorry;

lemma lem2
  [𝗜𝚺₁ ⪯ T]
  (h : Modal.D ⊬ A) :
    (Modal.D.sumQuasiNormal {A}) ⊢[T]* (□(.atom 0) ➝ (.atom 0)) := by
    obtain ⟨B, hB₁, hB₂, hB₃⟩ := lem1 h;
    have hPL := Modal.Logic.arithmeticalCompletion_isProvabilityLogic (T := T) (L := Modal.D.sumQuasiNormal {A});
    have := @eq_provabilityLogic_GLβMinus_of_not_subset_S (hPL := hPL);


    sorry;

end ProvabilityLogic

end LO

end
