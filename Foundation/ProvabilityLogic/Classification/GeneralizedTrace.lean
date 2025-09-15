import Foundation.ProvabilityLogic.Classification.LetterlessTrace

namespace LO

namespace Modal

open Kripke

variable {φ ψ : Formula ℕ}

def Formula.gTrace (φ : Formula ℕ) : Set ℕ := { n | ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ φ }

def Formula.gTrace' (φ : Formula ℕ) : Set ℕ := { n | ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, M.finHeight = n ∧ ¬r ⊧ φ }

lemma satisfies_of_not_mem_gTrace' : n ∉ φ.gTrace' ↔ (∀ M : Kripke.Model, ∀ r : M, [M.IsTree r] → [Fintype M] → M.finHeight = n → r ⊧ φ) := by
  simp [Formula.gTrace'];

lemma satisfies_of_not_mem_gTrace : n ∉ φ.gTrace ↔ (∀ M : Kripke.Model, ∀ r, [M.IsTree r] → [Fintype M] → ∀ w : M, Frame.World.finHeight w = n → w ⊧ φ) := by
  simp [Formula.gTrace];

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

variable {L : Logic ℕ} {φ : Formula ℕ}

attribute [grind] Modal.Logic.iff_provable

lemma subset_of_provable (h : L ⊢! φ) : φ.gTrace ⊆ L.trace := by
  intro n h;
  simp_all [Logic.trace, FormulaSet.gTrace];
  use φ;

abbrev _root_.Set.Cofinite (s : Set α) := sᶜ.Finite
abbrev _root_.Set.Coinfinite (s : Set α) := sᶜ.Infinite

lemma _root_.Set.Cofinite.subset {s t : Set α} (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

lemma _root_.Set.Coinfinite.subset {s t : Set α} (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  simpa using Set.Cofinite.subset h;

@[grind]
lemma Formula.gTrace.finite_or_cofinite : φ.gTrace.Finite ∨ φ.gTrace.Cofinite := by
  sorry;

@[grind]
lemma Formula.gTrace.finite_of_coinfinite (h_ci : φ.gTrace.Coinfinite) : φ.gTrace.Finite := by
  rcases Formula.gTrace.finite_or_cofinite (φ := φ) with h | h_cf;
  . assumption;
  . exfalso;
    apply h_ci;
    exact h_cf;

@[simp]
lemma TBB_injective : Function.Injective TBB := by sorry;

lemma iff_satisfies_TBB_ne_finHeight {M : Model} {r : M} [M.IsTree r] [Fintype M] {n : ℕ} : r ⊧ (TBB n) ↔ M.finHeight ≠ n := by
  apply Iff.trans $ iff_satisfies_mem_finHeight_spectrum (φ := TBB n) (w := r)
  simp;
  tauto;

lemma subset_GLα_of_trace_coinfinite (hL : L.trace.Coinfinite) : L ⊆ Modal.GLα L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.gTrace ⊆ L.trace := subset_of_provable (by grind);
  have : φ.gTrace.Finite := by
    have : φ.gTrace.Coinfinite := Set.Coinfinite.subset this hL
    grind
  let Tφ := this.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨(Tφ.image TBB), ?_, ?_⟩;
  . grind;
  . simpa [Tφ, Set.preimage_image_eq L.trace TBB_injective];
  . apply GL.Kripke.tree_completeness_TFAE.out 3 0 |>.mp;
    intro M r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply satisfies_of_not_mem_gTrace (n := M.finHeight) |>.mp;
    . replace hr : ∀ n ∈ φ.gTrace, M.finHeight ≠ n := by
        intro n h;
        apply iff_satisfies_TBB_ne_finHeight.mp;
        apply Satisfies.fconj_def.mp hr _;
        simp [Tφ];
        use n;
      by_contra hC;
      apply hr _ hC rfl;
    . rfl;


lemma Formula.Kripke.Satisfies.fconj'_def {M : Kripke.Model} {w : M} {X : Finset α} {ι : α → Formula ℕ} : w ⊧ (⩕ i ∈ X, ι i) ↔ ∀ i ∈ X, w ⊧ ι i := by
  sorry;

lemma Formula.Kripke.Satisfies.not_fconj'_def {M : Kripke.Model} {w : M} {X : Finset α} {ι : α → Formula ℕ} : ¬(w ⊧ (⩕ i ∈ X, ι i)) ↔ ∃ i ∈ X, ¬(w ⊧ ι i) := by
  simpa using Formula.Kripke.Satisfies.fconj'_def.not;


lemma subset_GLβMinus_of_trace_cofinite (hL : L.trace.Cofinite) : L ⊆ Modal.GLβMinus L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.gTrace ⊆ L.trace := subset_of_provable (by grind);

  let Tφ := hL.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨{∼⩕ n ∈ Tφ, TBB n}, ?_, ?_⟩;
  . grind;
  . simp_all [Set.compl_iUnion, Tφ];
  . apply GL.Kripke.tree_completeness_TFAE.out 3 0 |>.mp;
    intro M r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply satisfies_of_not_mem_gTrace (n := M.finHeight) |>.mp;
    . replace hr : ∀ (n : ℕ), ∀ x ∈ L, n ∈ x.gTrace → ¬M.finHeight = n := by
        rintro n ξ hξ₁ hξ₂ rfl;
        obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ∈ Tφ ∧ ¬r ⊧ TBB m := Satisfies.not_fconj'_def.mp $ Satisfies.not_def.mp $ by simpa using hr;
        replace hm₁ : ∀ i ∈ L, m ∉ i.gTrace := by simpa [Tφ] using hm₁;
        replace hm₂ : M.finHeight = m := by simpa using iff_satisfies_TBB_ne_finHeight.not.mp hm₂;
        apply hm₁ ξ;
        . assumption;
        . grind;
      by_contra hC;
      apply hr M.finHeight φ hφ hC rfl;
    . rfl;

end Modal

end LO
