import Foundation.ProvabilityLogic.Classification.LetterlessTrace

namespace LO

namespace Modal

open Kripke

variable {φ ψ : Formula ℕ}

def Formula.gTrace (φ : Formula ℕ) : Set ℕ := { n | ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ φ }

@[grind]
lemma Formula.eq_gTrace_trace_of_letterless {φ : Formula ℕ} (φ_letterless : φ.letterless) : φ.gTrace = φ.trace := by
  ext n;
  apply Iff.trans ?_ (Kripke.spectrum_TFAE φ_letterless (n := n) |>.out 1 0 |>.not);
  simp [Formula.gTrace];

open Formula.Kripke

lemma Formula.gTrace_and : (φ ⋏ ψ).gTrace = φ.gTrace ∪ ψ.gTrace := by
  ext n;
  calc
    _ ↔ ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ (φ ⋏ ψ) := by simp [Formula.gTrace]
    _ ↔
      (∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ φ) ∨
      (∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ ψ) := by
      constructor;
      . rintro ⟨M, r, _, _, w, _, h⟩;
        replace h := Satisfies.and_def.not.mp h;
        set_option push_neg.use_distrib true in push_neg at h;
        rcases h with (h | h);
        . left; tauto;
        . right; tauto;
      . rintro (⟨M, r, _, _, w, _, h⟩ | ⟨M, r, _, _, w, _, h⟩) <;>
        . refine ⟨M, r, by assumption, by assumption, w, by assumption, ?_⟩;
          apply Satisfies.and_def.not.mpr;
          tauto;
    _ ↔ _ := by simp [Formula.gTrace];


abbrev FormulaSet.gTrace (X : FormulaSet ℕ) : Set ℕ := ⋃ φ ∈ X, φ.gTrace

@[simp]
lemma FormulaSet.gTrace_empty : (∅ : FormulaSet ℕ).gTrace = ∅ := by simp [FormulaSet.gTrace];

abbrev Logic.trace (L : Logic ℕ) : Set ℕ := FormulaSet.gTrace L

lemma GL.eq_trace_ext
  {X : FormulaSet ℕ}
  (hX : ∀ ξ ∈ X, ∀ s : Substitution _, ξ⟦s⟧ ∈ X)
  : (Modal.GL.sumQuasiNormal X).trace = X.gTrace := by
  ext n;
  suffices (∃ φ ∈ Modal.GL.sumQuasiNormal X, n ∈ φ.gTrace) ↔ (∃ φ ∈ X, n ∈ φ.gTrace) by
    simpa [Logic.trace];
  constructor;
  . rintro ⟨φ, hφ₁, hφ₂⟩;
    obtain ⟨Y, hY₁, hY₂⟩ := Logic.sumQuasiNormal.iff_provable_finite_provable hX |>.mp $ Logic.iff_provable.mpr hφ₁;
    sorry;
  . rintro ⟨φ, hφ₁, hφ₂⟩;
    use φ;
    constructor;
    . apply Logic.iff_provable.mp;
      apply Logic.sumQuasiNormal.mem₂!;
      simpa [Logic.iff_provable];
    . assumption;

lemma Logic.sumQuasiNormal.with_empty [DecidableEq α] {L₁ : Logic α} [L₁.IsQuasiNormal] : L₁.sumQuasiNormal ∅ = L₁ := by
  ext φ;
  suffices L₁.sumQuasiNormal ∅ ⊢! φ ↔ L₁ ⊢! φ by simpa [Logic.iff_provable];
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | mem₁ => assumption;
    | mem₂ => simp_all;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => exact Logic.subst! _ ihφ;
  . intro h;
    exact Entailment.WeakerThan.pbl h;

lemma GL.unprovable_of_exists_trace (φ_letterless : φ.letterless) : (∃ n, n ∈ φ.trace) → Modal.GL ⊬ φ := by
  contrapose!;
  intro h;
  have := Modal.iff_GL_provable_spectrum_Univ φ_letterless |>.mp (by simpa using h);
  simp_all [Formula.trace];

@[simp]
lemma TBBMinus_trace (hβ : βᶜ.Finite) : (∼⩕ n ∈ hβ.toFinset, TBB n).trace = β := by
  simp [Formula.trace, TBBMinus_spectrum']

@[simp]
lemma GL.eq_trace_emptyset : Modal.GL.trace = ∅ := by
  rw [←Logic.sumQuasiNormal.with_empty (L₁ := Modal.GL)]
  simpa using GL.eq_trace_ext (X := ∅) (by simp);

@[simp]
lemma GLα.eq_trace {α : Set ℕ} : (Modal.GLα α).trace = α := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.gTrace, Formula.eq_gTrace_trace_of_letterless];

@[simp]
lemma GLβMinus.eq_trace {β : Set ℕ} (hβ : βᶜ.Finite := by grind) : (Modal.GLβMinus β).trace = β := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.gTrace, Formula.eq_gTrace_trace_of_letterless];

@[simp] lemma S.provable_TBB {n : ℕ} : Modal.S ⊢! TBB n := by simp [TBB]

@[simp]
lemma S.eq_trace : Modal.S.trace = Set.univ := by
  suffices ∀ (x : ℕ), ∃ i ∈ Modal.S, x ∈ i.gTrace by simpa [Set.eq_univ_iff_forall]
  intro n;
  use (TBB n);
  constructor;
  . apply Logic.iff_provable.mp; simp;
  . simp [Formula.eq_gTrace_trace_of_letterless];

end Modal

end LO
