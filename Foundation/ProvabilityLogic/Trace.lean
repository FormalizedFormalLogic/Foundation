import Foundation.Modal.Formula
import Foundation.Modal.Axioms
import Foundation.ProvabilityLogic.SolovaySentences
import Foundation.ProvabilityLogic.S.Completeness
import Foundation.Modal.Logic.S.Basic
import Foundation.Modal.Logic.Dz.Basic
import Mathlib.Tactic.TFAE

lemma Set.compl_inj_iff {a b : Set α} : aᶜ = bᶜ ↔ a = b := _root_.compl_inj_iff


namespace LO

open FirstOrder ProvabilityLogic

variable {φ ψ : Modal.Formula ℕ}
         {X Y : Modal.FormulaSet ℕ}
         {T : ArithmeticTheory} [T.Δ₁]

namespace Modal

namespace Formula

namespace letterless

variable {φ ψ : Formula α}

attribute [grind] letterless.def_imp₁ letterless.def_imp₂ letterless.def_box

@[simp, grind] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]
@[simp, grind] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]

@[grind] lemma of_imp (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ➝ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_neg (hφ : φ.letterless) : (∼φ).letterless := by simp_all [letterless]
@[grind] lemma of_or (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋎ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_and (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋏ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_box (hφ : φ.letterless) : (□φ).letterless := by simp_all [letterless]
@[grind] lemma of_multibox (hφ : φ.letterless) : (□^[n]φ).letterless := by
  induction n with
  | zero => simpa [letterless]
  | succ n ih => simp [letterless, ih]

lemma of_fconj {Φ : Finset (Formula α)} (h : ∀ φ ∈ Φ, φ.letterless) : (Φ.conj).letterless := by
  sorry;

lemma of_fconj' {s : Finset β} {Φ : β → Formula α} (h : ∀ i, (Φ i).letterless) : (⩕ i ∈ s, Φ i).letterless := by
  sorry;

end letterless


/-- spectrum for letterless formula -/
def spectrum (φ : Formula ℕ) (φ_closed : φ.letterless := by grind) : Set ℕ :=
  match φ with
  | ⊥ => ∅
  | φ ➝ ψ => φ.spectrumᶜ ∪ ψ.spectrum
  | □φ => { n | ∀ i < n, i ∈ φ.spectrum }

namespace spectrum

variable (hφ : φ.letterless := by grind) (hψ : ψ.letterless := by grind)

@[simp, grind] lemma def_bot : (⊥ : Formula _).spectrum = ∅ := by simp [spectrum]
@[simp, grind] lemma def_top : (⊤ : Formula _).spectrum = Set.univ := by simp [spectrum]
@[grind] lemma def_imp : (φ ➝ ψ).spectrum = φ.spectrumᶜ ∪ ψ.spectrum := by simp [spectrum]
@[grind] lemma def_neg : (∼φ).spectrum = φ.spectrumᶜ := by simp [spectrum]
@[grind] lemma def_or  : (φ ⋎ ψ).spectrum = φ.spectrum ∪ ψ.spectrum := by simp [spectrum];
@[grind] lemma def_and : (φ ⋏ ψ).spectrum = φ.spectrum ∩ ψ.spectrum := by simp [spectrum];
@[grind] lemma def_box : (□φ).spectrum = { n | ∀ i < n, i ∈ φ.spectrum } := by simp [spectrum];
@[grind] lemma def_multibox : (□^[(n + 1)]φ).spectrum = { k | ∀ i < k, i ∈ (□^[n]φ).spectrum } := by
  apply Eq.trans ?_ $ def_box (φ := □^[n]φ);
  induction n generalizing φ with
  | zero => simp [spectrum]
  | succ n ih =>
    suffices (□^[n](□□φ)).spectrum = (□□^[n](□φ)).spectrum by simpa
    rw [←ih];
    simp;
@[grind] lemma def_boxdot : (⊡φ).spectrum = { n | ∀ i ≤ n, i ∈ φ.spectrum } := by
  ext i;
  suffices (i ∈ φ.spectrum ∧ ∀ j < i, j ∈ φ.spectrum) ↔ ∀ j ≤ i, j ∈ φ.spectrum by simpa [spectrum];
  constructor;
  . rintro ⟨h₁, h₂⟩ j hj;
    rcases Nat.le_iff_lt_or_eq.mp hj with (h | rfl);
    . apply h₂;
      assumption;
    . assumption;
  . intro h;
    constructor;
    . apply h; omega;
    . intro j hj;
      apply h;
      omega;

lemma def_fconj {Φ : Finset (Formula _)} (hΦ : ∀ φ ∈ Φ, φ.letterless) : (Φ.conj.spectrum (letterless.of_fconj hΦ)) = ⋂ φ ∈ Φ, φ.spectrum := by
  sorry;

lemma def_fconj' {s} {Φ : α → Formula ℕ} (hΦ : ∀ i, (Φ i).letterless) : ((⩕ i ∈ s, Φ i).spectrum (letterless.of_fconj' hΦ)) = ⋂ i ∈ s, (Φ i).spectrum (hΦ i) := by
  sorry;

end spectrum


lemma spectrum_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.letterless) : φ.spectrum.Finite ∨ φ.spectrumᶜ.Finite := by
  induction φ with
  | hfalsum => simp;
  | hatom => simp at hφ;
  | himp φ ψ ihφ ihψ =>
    rw [spectrum.def_imp];
    rcases ihφ (by grind) with (ihφ | ihφ) <;>
    rcases ihψ (by grind) with (ihψ | ihψ);
    case himp.inr.inl => left; simp_all;
    all_goals
    . right;
      simp only [Set.compl_union, compl_compl];
      first
      | apply Set.Finite.inter_of_left (by simpa);
      | apply Set.Finite.inter_of_right (by simpa);
  | hbox φ ihφ =>
    by_cases h : φ.spectrum = Set.univ;
    . right;
      rw [spectrum.def_box, h];
      simp;
    . left;
      obtain ⟨k, hk₁, hk₂⟩ := exists_minimal_of_wellFoundedLT (λ k => k ∉ φ.spectrum) $ Set.ne_univ_iff_exists_notMem _ |>.mp h;
      have : {n | ∀ i < n, i ∈ φ.spectrum} = { n | n ≤ k} := by
        ext i;
        suffices (∀ j < i, j ∈ φ.spectrum) ↔ i ≤ k by simpa [Set.mem_setOf_eq];
        constructor;
        . intro h;
          contrapose! hk₁;
          exact h k (by omega);
        . intro h j hji;
          contrapose! hk₂;
          use j;
          constructor;
          . assumption;
          . omega;
      rw [spectrum.def_box, this];
      apply Set.finite_le_nat;


/-- trace for letterless formula -/
@[grind] def trace (φ : Formula ℕ) (φ_closed : φ.letterless := by grind) := φ.spectrumᶜ

namespace trace

variable {φ ψ : Formula ℕ} (hφ : φ.letterless := by grind) (hψ : ψ.letterless := by grind)

@[simp, grind] lemma def_top : (⊤ : Formula _).trace = ∅ := by unfold trace; rw [spectrum.def_top]; tauto_set;
@[simp, grind] lemma def_bot : (⊥ : Formula _).trace = Set.univ := by unfold trace; rw [spectrum.def_bot]; tauto_set;
@[grind] lemma def_neg : (∼φ).trace = φ.traceᶜ := by unfold trace; rw [spectrum.def_neg];
@[grind] lemma def_and : (φ ⋏ ψ).trace = φ.trace ∪ ψ.trace := by unfold trace; rw [spectrum.def_and]; tauto_set;
@[grind] lemma def_or  : (φ ⋎ ψ).trace = φ.trace ∩ ψ.trace := by unfold trace; rw [spectrum.def_or]; tauto_set;

end trace

lemma neg_trace_spectrum {φ : Formula ℕ} (hφ : φ.letterless := by grind) : (∼φ).trace = φ.spectrum := by rw [trace.def_neg]; simp [trace];
lemma neg_spectrum_trace {φ : Formula ℕ} (hφ : φ.letterless := by grind) : (∼φ).spectrum = φ.trace := by rw [spectrum.def_neg]; simp [trace];

lemma trace_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.letterless := by grind) : φ.trace.Finite ∨ φ.traceᶜ.Finite := by
  simp only [trace, compl_compl];
  apply spectrum_finite_or_cofinite hφ |>.symm;


section



/-- Realization which any propositional variable maps to `⊤` -/
abbrev _root_.LO.FirstOrder.ArithmeticTheory.trivialPLRealization (T : ArithmeticTheory) [T.Δ₁] : T.PLRealization := ⟨λ _ => ⊤⟩

@[grind] def regular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ℕ ⊧ₘ₀ (T.trivialPLRealization φ)

@[grind] def singular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ¬(φ.regular T)

namespace regular

@[simp, grind] lemma def_bot : ¬((⊥ : Formula _).regular T) := by simp [Formula.regular, Realization.interpret];
@[simp, grind] lemma def_top : (⊤ : Formula _).regular T := by simp [Formula.regular, Realization.interpret];
@[grind] lemma def_neg : (∼φ).regular T ↔ ¬(φ.regular T) := by simp [Formula.regular, Realization.interpret];
@[grind] lemma def_neg' : (∼φ).regular T ↔ (φ.singular T) := Iff.trans def_neg $ by rfl
@[grind] lemma def_and : (φ ⋏ ψ).regular T ↔ (φ.regular T) ∧ (ψ.regular T) := by simp [Formula.regular, Realization.interpret];
@[grind] lemma def_or : (φ ⋎ ψ).regular T ↔ (φ.regular T) ∨ (ψ.regular T) := by simp [Formula.regular, Realization.interpret]; tauto;
@[grind] lemma def_imp : (φ ➝ ψ).regular T ↔ ((φ.regular T) → (ψ.regular T)) := by simp [Formula.regular, Realization.interpret];
@[grind] lemma def_iff : (φ ⭤ ψ).regular T ↔ ((φ.regular T) ↔ (ψ.regular T)) := by simp [Formula.regular, Realization.interpret]; tauto;
lemma def_fconj' {Φ : β → Formula _} : (⩕ i ∈ s, Φ i).regular T ↔ ∀ i ∈ s, ((Φ i).regular T) := by
  simp [Formula.regular, Realization.interpret];
  sorry;

end regular


namespace singular

@[simp, grind] lemma def_bot : (⊥ : Formula _).singular T := by grind
@[simp, grind] lemma def_top : ¬(⊤ : Formula _).singular T := by grind
@[grind] lemma def_neg : (∼φ).singular T ↔ ¬(φ.singular T) := by grind;
@[grind] lemma def_neg' : (∼φ).singular T ↔ (φ.regular T) := by grind;
@[grind] lemma def_and : (φ ⋏ ψ).singular T ↔ (φ.singular T) ∨ (ψ.singular T) := by grind
@[grind] lemma def_or : (φ ⋎ ψ).singular T ↔ (φ.singular T) ∧ (ψ.singular T) := by grind
@[grind] lemma def_imp : (φ ➝ ψ).singular T ↔ (¬(φ.singular T) ∧ (ψ.singular T)) := by grind

end singular

end

end Formula


namespace FormulaSet

abbrev letterless (X : Modal.FormulaSet ℕ) := ∀ φ ∈ X, φ.letterless

protected def regular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ∀ φ ∈ X, φ.regular T

protected def singular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ¬X.regular T

lemma exists_singular_of_singular (hX_singular : X.singular T) : ∃ φ ∈ X, φ.singular T := by
  simpa [FormulaSet.singular, FormulaSet.regular] using hX_singular;

protected def spectrum (X : Modal.FormulaSet ℕ) (_ : X.letterless := by grind) := ⋂ φ ∈ X, φ.spectrum

protected def trace (X : Modal.FormulaSet ℕ) (_ : X.letterless := by grind) := X.spectrumᶜ

variable (Xll : X.letterless := by grind) (Yll : Y.letterless := by grind)

lemma def_trace_union : X.trace = ⋃ φ ∈ X, φ.trace := by simp [FormulaSet.trace, FormulaSet.spectrum, Formula.trace]

lemma comp_trace_spectrum : X.traceᶜ = X.spectrum := by simp [FormulaSet.trace]

lemma iff_subset_spectrum_subset_trace : X.spectrum ⊆ Y.spectrum ↔ Y.trace ⊆ X.trace := by simp [FormulaSet.trace]

lemma iff_eq_spectrum_eq_trace : X.spectrum = Y.spectrum ↔ X.trace = Y.trace := by simp [FormulaSet.trace];

end FormulaSet



lemma boxbot_spectrum : (□^[n]⊥ : Formula ℕ).spectrum = { i | i < n } := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = { i | ∀ k < i, k ∈ (□^[n]⊥ : Formula ℕ).spectrum } := Formula.spectrum.def_multibox
      _ = { i | ∀ k < i, k < n }                             := by simp [ih];
      _ = { i | i < n + 1 }                                  := by
        ext i;
        suffices (∀ k < i, k < n) ↔ i < n + 1 by simpa;
        constructor;
        . contrapose!;
          intro h;
          use n;
          omega;
        . omega;

/-- boxbot instance of axiomT -/
abbrev TBB (n : ℕ) : Formula ℕ := □^[(n+1)]⊥ ➝ □^[n]⊥

@[simp, grind] lemma TBB_letterless : (TBB n).letterless := by grind

@[simp]
lemma TBB_spectrum : (TBB n).spectrum = {n}ᶜ := by
  rw [Formula.spectrum.def_imp, boxbot_spectrum, boxbot_spectrum];
  ext i;
  simp;
  omega;

@[simp]
lemma TBB_trace : (TBB n).trace = {n} := by simp [Formula.trace, TBB_spectrum, compl_compl];


namespace Kripke

open Kripke
open Formula.Kripke

variable {F : Frame} [Fintype F] {r : F} [F.IsTree r]

lemma Frame.World.finHeight_lt_of_rel {i j : F} (hij : i ≺ j) : Frame.World.finHeight i > Frame.World.finHeight j := fcwHeight_gt_of hij

lemma Frame.World.exists_of_lt_finHeight {i : F} (hn : n < Frame.World.finHeight i) : ∃ j : F, i ≺ j ∧ Frame.World.finHeight j = n := fcwHeight_lt hn

lemma iff_satisfies_mem_finHeight_spectrum
  {M : Model} [Fintype M] {r : M} [M.IsTree r] {w : M.World}
  {φ : Formula ℕ} (φ_closed : φ.letterless := by grind)
  : w ⊧ φ ↔ Frame.World.finHeight w ∈ φ.spectrum := by
  induction φ generalizing w with
  | hatom => simp at φ_closed;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    rw [Satisfies.imp_def, ihφ, ihψ, Formula.spectrum.def_imp]
    simp;
    tauto;
  | hbox φ ihφ =>
    calc
      w ⊧ □φ ↔ ∀ v, w ≺ v → v ⊧ φ                                  := by rfl;
      _      ↔ ∀ v, w ≺ v → (Frame.World.finHeight v ∈ φ.spectrum) := by
        constructor;
        . intro h v; rw [←ihφ]; apply h;
        . intro h v; rw [ihφ]; apply h;
      _      ↔ ∀ i < (Frame.World.finHeight w), i ∈ φ.spectrum := by
        constructor;
        . intro h i hi;
          obtain ⟨v, Rwv, rfl⟩ := Frame.World.exists_of_lt_finHeight hi;
          apply h;
          assumption;
        . intro h v Rwv;
          apply h;
          apply Frame.World.finHeight_lt_of_rel;
          assumption;
      _      ↔ Frame.World.finHeight w ∈ (□φ).spectrum := by
        rw [Formula.spectrum.def_box]; simp;

lemma spectrum_TFAE (_ : φ.letterless := by grind)
  : [
  n ∈ φ.spectrum,
  ∀ M : Model, ∀ r, [Fintype M] → [M.IsTree r] → ∀ w : M.World, Frame.World.finHeight w = n → w ⊧ φ,
  ∃ M : Model, ∃ r, ∃ _ : Fintype M, ∃ _ : M.IsTree r, ∃ w : M.World, Frame.World.finHeight w = n ∧ w ⊧ φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h M _ r _ w hw;
    apply iff_satisfies_mem_finHeight_spectrum (by grind) |>.mpr;
    apply hw ▸ h;
  tfae_have 2 → 3 := by
    intro h;
    sorry;
  tfae_have 3 → 1 := by
    rintro ⟨M, _, _, _, w, rfl, h⟩;
    apply iff_satisfies_mem_finHeight_spectrum (by grind) |>.mp h;
  tfae_finish;

end Kripke

section

open Formula
open LO.Entailment Modal.Entailment

variable {φ ψ : Formula ℕ} (_ : φ.letterless := by grind) (_ : ψ.letterless := by grind)

lemma iff_GL_provable_spectrum_Univ
  : Modal.GL ⊢! φ ↔ φ.spectrum = Set.univ := by
  suffices Hilbert.GL ⊢! φ ↔ φ.spectrum = Set.univ by simpa;
  have := Logic.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree (φ := φ);
  apply Iff.trans this;
  simp only [Set.eq_univ_iff_forall]
  constructor;
  . intro h n;
    apply Kripke.spectrum_TFAE (φ := φ) (by grind) |>.out 1 0 |>.mp;
    sorry;
  . intro h;
    sorry;

lemma iff_GL_provable_C_subset_spectrum : Modal.GL ⊢! (φ ➝ ψ) ↔ φ.spectrum ⊆ ψ.spectrum := by
  apply Iff.trans $ iff_GL_provable_spectrum_Univ;
  rw [Formula.spectrum.def_imp];
  suffices (∀ i, i ∉ φ.spectrum ∨ i ∈ ψ.spectrum) ↔ φ.spectrum ⊆ ψ.spectrum by
    simpa [Set.eq_univ_iff_forall];
  constructor <;>
  . intro h i;
    have := @h i;
    tauto;

lemma iff_GL_provable_E_eq_spectrum : Modal.GL ⊢! φ ⭤ ψ ↔ φ.spectrum = ψ.spectrum := by
  have hφ := iff_GL_provable_C_subset_spectrum (φ := φ) (ψ := ψ);
  have hψ := iff_GL_provable_C_subset_spectrum (φ := ψ) (ψ := φ);
  constructor;
  . intro h
    apply Set.Subset.antisymm;
    . apply hφ.mp; cl_prover [h]
    . apply hψ.mp; cl_prover [h]
  . intro h;
    replace hφ := hφ.mpr (h.subset);
    replace hψ := hψ.mpr (h.symm.subset)
    cl_prover [hφ, hψ];

lemma GL_trace_TBB_normalization (h : φ.trace.Finite) : Modal.GL ⊢! φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_spectrum (by simpa) (letterless.of_fconj' (by simp)) |>.mpr;
  calc
    φ.spectrum = ⋂ i ∈ φ.trace, (TBB i).spectrum          := by
      have : φ.trace = ⋃ i ∈ φ.trace, (TBB i).trace := by ext i; simp [TBB_trace];
      simpa [Formula.trace] using Set.compl_inj_iff.mpr this;
    _          = ((⩕ n ∈ h.toFinset, (TBB n))).spectrum _ := by
      ext i;
      rw [Formula.spectrum.def_fconj' (by simp)];
      simp;

lemma GL_spectrum_TBB_normalization (h : φ.spectrum.Finite) : Modal.GL ⊢! φ ⭤ ∼(⩕ n ∈ h.toFinset, (TBB n)) := by
  have h' : (∼φ).trace.Finite := by rwa [Formula.neg_trace_spectrum];
  replace : Modal.GL ⊢! φ ⭤ ∼⩕ n ∈ h'.toFinset, TBB n := by
    have := GL_trace_TBB_normalization (φ := ∼φ) (by grind) h';
    cl_prover [this];
  have e : h'.toFinset = h.toFinset := by simp [Formula.neg_trace_spectrum (show φ.letterless by simpa)]
  exact e ▸ this;

lemma GL_proves_letterless_axiomWeakPoint3 (_ : φ.letterless := by grind) (_ : ψ.letterless := by grind) : Modal.GL ⊢! (Axioms.WeakPoint3 φ ψ) := by
  apply iff_GL_provable_spectrum_Univ (by grind) |>.mpr;
  apply Set.eq_univ_iff_forall.mpr;
  intro n;
  rw [spectrum.def_or, spectrum.def_box, spectrum.def_box, spectrum.def_imp, spectrum.def_imp, spectrum.def_boxdot, spectrum.def_boxdot];
  suffices ∀ i < n, (∀ k ≤ i, k ∈ φ.spectrum) → i ∉ ψ.spectrum → ∀ j < n, (∀ k ≤ j, k ∈ ψ.spectrum) → j ∈ φ.spectrum by
    simpa [or_iff_not_imp_left];
  intro i _ hi hiψ j _ hj;
  apply hi;
  contrapose! hiψ;
  apply hj;
  omega;

/-- Theorem 2 in [Valentini & Solitro 1983] -/
lemma iff_provable_GLPoint3_letterless_provable_GL : Modal.GLPoint3 ⊢! φ ↔ (∀ s : ZeroSubstitution _, Modal.GL ⊢! φ⟦s.1⟧) := by
  constructor;
  . suffices Hilbert.GLPoint3 ⊢! φ → (∀ s : ZeroSubstitution _, Modal.GL ⊢! φ⟦s.1⟧) by simpa;
    intro h s;
    induction h using Hilbert.Normal.rec! with
    | axm t ht =>
      rcases ht with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply GL_proves_letterless_axiomWeakPoint3 <;>
        apply Formula.letterless_zeroSubst;
    | mdp h₁ h₂ => exact h₁ ⨀ h₂;
    | nec h => apply nec! h;
    | _ => simp;
  . contrapose!;
    suffices Hilbert.GLPoint3 ⊬ φ → (∃ s : ZeroSubstitution _, Hilbert.GL ⊬ φ⟦s.1⟧) by simpa;
    -- Kripke semantical arguments (?)
    intro h;
    sorry;

end

lemma iff_regular_of_provable_E (h : Modal.GL ⊢! φ ⭤ ψ) : φ.regular T ↔ ψ.regular T := by
  simp [Formula.regular];
  sorry;

lemma iff_singular_of_provable_E (h : Modal.GL ⊢! φ ⭤ ψ) : φ.singular T ↔ ψ.singular T := Iff.not $ iff_regular_of_provable_E h

@[simp] lemma TBB_regular : (TBB n).regular T := by
  apply Formula.regular.def_imp.mpr;
  sorry;

@[simp] lemma TBB_conj'_regular : (⩕ n ∈ s, TBB n).regular T := by
  apply Formula.regular.def_fconj'.mpr;
  simp;


variable
  (φll : φ.letterless := by grind)
  (Xll : X.letterless := by grind)
  (Yll : Y.letterless := by grind)

lemma Formula.iff_regular_trace_finite : φ.regular T ↔ φ.trace.Finite := by
  constructor;
  . contrapose!;
    intro h;
    have := GL_spectrum_TBB_normalization (by grind) $ show φ.spectrum.Finite by
      simpa [Formula.trace] using or_iff_not_imp_left.mp Formula.trace_finite_or_cofinite h;
    apply iff_regular_of_provable_E this |>.not.mpr;
    apply Formula.regular.def_neg.not.mpr;
    push_neg;
    simp;
  . intro h;
    apply iff_regular_of_provable_E (GL_trace_TBB_normalization (by grind) h) |>.mpr;
    simp;

lemma Formula.spectrum_finite_of_singular : φ.singular T → φ.spectrum.Finite := by
  contrapose!;
  suffices ¬(φ.spectrum).Finite → Formula.regular T φ by simpa [Formula.singular, not_not];
  intro h;
  apply iff_regular_trace_finite (by grind) |>.mpr;
  apply or_iff_not_imp_right.mp $ Formula.trace_finite_or_cofinite (by grind);
  simpa [Formula.trace] using h;

lemma letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : [
  φ.spectrum = Set.univ,
  Modal.GL ⊢! φ,
  T ⊢!. T.trivialPLRealization φ
].TFAE := by
  tfae_have 3 ↔ 2 := by
    apply Iff.trans ?_ $ GL.arithmetical_completeness_sound_iff (T := T);
    constructor;
    . intro h f;
      have e : T.trivialPLRealization φ = f φ := by
        clear h;
        induction φ with
        | hfalsum => simp;
        | hatom => simp_all [Formula.letterless.not_atom];
        | himp φ ψ ihφ ihψ => simp [Realization.interpret, ihφ (by grind), ihψ (by grind)];
        | hbox φ ihφ => simp [Realization.interpret, ihφ (by grind)];
      exact e ▸ h;
    . intro h;
      apply h;
  tfae_have 2 ↔ 1 := iff_GL_provable_spectrum_Univ
  tfae_finish;

lemma FormulaSet.spectrum_finite_of_singular (hX_singular : X.singular T) : X.spectrum.Finite := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_singular_of_singular hX_singular;
  suffices (X.spectrum) ⊆ (φ.spectrum) by
    apply Set.Finite.subset;
    exact Formula.spectrum_finite_of_singular (by grind) hφ₂;
    assumption;
  intro i;
  simp_all [FormulaSet.spectrum];

lemma FormulaSet.regular_of_not_trace_cofinite : ¬X.traceᶜ.Finite → X.regular T := by
  contrapose!;
  rw [comp_trace_spectrum];
  apply spectrum_finite_of_singular;
  assumption;


section

variable (Xll : X.letterless) (Yll : Y.letterless)
         {α β : Set ℕ} (hβ : βᶜ.Finite := by grind)

@[simp, grind] lemma TBBSet_letterless : FormulaSet.letterless ((λ i => TBB i) '' α) := by simp [FormulaSet.letterless]

@[simp] lemma TBBSet_trace : FormulaSet.trace (α.image (λ i => TBB i)) = α := by
  ext i;
  rw [FormulaSet.def_trace_union];
  simp [TBB_trace];

@[simp]
lemma TBBSet_regular : FormulaSet.regular T ((fun i ↦ TBB i) '' α) := by simp [FormulaSet.regular];

@[simp, grind]
lemma TBBMinus_letterless' : Formula.letterless (∼⩕ n ∈ hβ.toFinset, TBB n) := by
  apply Formula.letterless.of_neg;
  apply Formula.letterless.of_fconj';
  grind;

@[simp, grind]
lemma TBBMinus_letterless : FormulaSet.letterless {∼⩕ n ∈ hβ.toFinset, TBB n} := by simp [FormulaSet.letterless];

lemma TBBMinus_spectrum' : (∼⩕ n ∈ hβ.toFinset, TBB n).spectrum = βᶜ := by
  rw [Formula.spectrum.def_neg (Formula.letterless.of_fconj' (by grind)), Formula.spectrum.def_fconj' (by grind)];
  ext i;
  suffices (∀j ∉ β, i ≠ j) ↔ i ∈ β by simp [TBB_spectrum];
  constructor;
  . contrapose!; tauto;
  . contrapose!; rintro ⟨i, _, rfl⟩; tauto;

lemma TBBMinus_spectrum : FormulaSet.spectrum {(∼⩕ n ∈ hβ.toFinset, TBB n)} = βᶜ := by
  simp [FormulaSet.spectrum, TBBMinus_spectrum']

@[simp]
lemma TBBMinus_singular : FormulaSet.singular T {∼⩕ n ∈ hβ.toFinset, TBB n} := by
  simp [FormulaSet.singular, FormulaSet.regular];
  sorry;

open Classical in
lemma GL.iff_provable_closed_sumQuasiNormal_subset_spectrum {φ : Modal.Formula ℕ} (φll : φ.letterless) (hSR : X.singular T ∨ φ.regular T)
  : Modal.GL.sumQuasiNormal X ⊢! φ ↔ X.spectrum ⊆ φ.spectrum := by
  calc
    _ ↔ ∃ Y, (∀ ψ ∈ Y, ψ ∈ X) ∧ Modal.GL ⊢! Finset.conj Y ➝ φ := by
      sorry;
    _ ↔ ∃ Y : Finset (Formula ℕ), (∀ ψ ∈ Y, ψ ∈ X) ∧ Formula.spectrum (Finset.conj Y) (by sorry) ⊆ φ.spectrum := by
      constructor <;>
      . rintro ⟨Y, hY₁, hY₂⟩;
        have := iff_GL_provable_C_subset_spectrum (φ := Finset.conj Y) (ψ := φ) (by sorry) (by simpa);
        use Y;
        tauto;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ hY : ∀ ψ ∈ Y, ψ ∈ X, ⋂ ψ ∈ Y, Formula.spectrum ψ ⊆ φ.spectrum := by
      constructor;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y, hY₁;
        convert hY₂;
        rw [Formula.spectrum.def_fconj];
        intro ψ hψ;
        apply Xll ψ;
        apply hY₁;
        assumption;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . exact hY₁;
        . rw [Formula.spectrum.def_fconj];
          . exact hY₂;
          . intro ψ hψ;
            apply Xll;
            apply hY₁;
            assumption;
    _ ↔ (⋂ ψ ∈ X, ψ.spectrum) ⊆ φ.spectrum := by
      constructor;
      . rintro ⟨Y, hY₁, hY₂⟩ i hi;
        apply hY₂;
        simp_all;
      . intro h;
        rcases hSR with hX | hφ;
        . sorry;
        . have h₂ : ∀ i ∈ φ.trace, ∃ ψ, ∃ _ : ψ ∈ X, i ∈ ψ.trace := by
            have : φ.trace ⊆ ⋃ ψ, ⋃ (_ : ψ ∈ X), ψ.trace := by
              apply Set.compl_subset_compl.mp;
              simpa [Formula.trace]
            simpa [Set.subset_def];
          replace hφ : φ.trace.Finite := Formula.iff_regular_trace_finite (by grind) |>.mp hφ;
          use @Finset.univ (α := { i // i ∈ φ.trace }) ?_ |>.image (λ i => (h₂ i.1 i.2).choose);
          constructor;
          . sorry;
          . simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, forall_exists_index];
            rintro ψ i hi rfl;
            apply h₂ i hi |>.choose_spec.1;
          . sorry;

lemma Logic.sumQuasiNormal.iff_subset {L : Logic ℕ} {X Y} : L.sumQuasiNormal Y ⊆ L.sumQuasiNormal X ↔ ∀ ψ ∈ Y, L.sumQuasiNormal X ⊢! ψ := by
  suffices (∀ φ, L.sumQuasiNormal Y ⊢! φ → L.sumQuasiNormal X ⊢! φ) ↔ (∀ ψ ∈ Y, L.sumQuasiNormal X ⊢! ψ) by
    apply Iff.trans ?_ this;
    constructor;
    . intro h ψ; simpa using @h ψ;
    . intro h ψ; simpa using @h ψ;
  constructor;
  . intro h ψ hψ;
    apply h;
    apply Logic.sumQuasiNormal.mem₂!
    simpa using hψ;
  . intro h ψ hψ;
    induction hψ using Logic.sumQuasiNormal.rec! with
    | mem₁ hψ => apply Logic.sumQuasiNormal.mem₁! hψ;
    | mem₂ hψ => apply h; simpa using hψ;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | subst ihφ => apply Logic.subst!; assumption;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (hSR : X.singular T ∨ Y.regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ X.spectrum ⊆ Y.spectrum := by
  calc
    _ ↔ ∀ ψ ∈ Y, Modal.GL.sumQuasiNormal X ⊢! ψ := Logic.sumQuasiNormal.iff_subset
    _ ↔ ∀ ψ, (h : ψ ∈ Y) → X.spectrum ⊆ ψ.spectrum := by
      constructor;
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_spectrum (T := T) (by simpa) (by grind) (by tauto) |>.mp;
        exact h ψ (by simpa);
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_spectrum (T := T) (by simpa) (by grind) (by tauto) |>.mpr;
        apply h;
        simpa;
    _ ↔ X.spectrum ⊆ (⋂ ψ ∈ Y, ψ.spectrum) := by simp;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_trace (hSR : X.singular T ∨ Y.regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ Y.trace ⊆ X.trace :=
  Iff.trans (iff_subset_closed_sumQuasiNormal_subset_spectrum Xll Yll hSR) FormulaSet.iff_subset_spectrum_subset_trace

lemma GL.iff_eq_closed_sumQuasiNormal_eq_spectrum (hXY : (X.regular T ∧ Y.regular T) ∨ (X.singular T ∧ Y.singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.spectrum = Y.spectrum := by
  simp only [Set.Subset.antisymm_iff];
  rw [
    iff_subset_closed_sumQuasiNormal_subset_spectrum Xll Yll (by tauto),
    iff_subset_closed_sumQuasiNormal_subset_spectrum Yll Xll (by tauto)
  ];
  tauto;


protected abbrev GL_TBB (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (α.image (λ i => TBB i))

protected abbrev GL_TBBMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}

protected abbrev S_Inter_GL_TBBMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.S ∩ Modal.GL_TBBMinus β hβ

protected abbrev Dz_Inter_GL_TBBMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.Dz ∩ Modal.GL_TBBMinus β hβ


lemma GL.iff_eq_closed_sumQuasiNormal_eq_trace (hXY : (X.regular T ∧ Y.regular T) ∨ (X.singular T ∧ Y.singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.trace = Y.trace :=
  Iff.trans (iff_eq_closed_sumQuasiNormal_eq_spectrum Xll Yll hXY) FormulaSet.iff_eq_spectrum_eq_trace

lemma GL.eq_closed_regular_sumQuasiNormal_GL_TBB (X_regular : X.regular T)
  : Modal.GL.sumQuasiNormal X = Modal.GL_TBB (X.trace) := by
  apply GL.iff_eq_closed_sumQuasiNormal_eq_trace (T := T) ?_ ?_ ?_ |>.mpr;
  . simp;
  . assumption;
  . simp [FormulaSet.letterless];
  . left;
    constructor;
    . assumption;
    . simp;

lemma GL.eq_closed_singular_sumQuasiNormal_GL_TBBMinus (X_singular : X.singular T)
  : Modal.GL.sumQuasiNormal X = Modal.GL_TBBMinus (X.trace) (FormulaSet.comp_trace_spectrum Xll ▸ FormulaSet.spectrum_finite_of_singular Xll X_singular) := by
  apply GL.iff_eq_closed_sumQuasiNormal_eq_spectrum (T := T) ?_ ?_ ?_ |>.mpr;
  . simp [TBBMinus_spectrum, FormulaSet.trace];
  . assumption;
  . simp only [FormulaSet.letterless, Set.mem_singleton_iff, forall_eq];
    apply Formula.letterless.of_neg;
    apply Formula.letterless.of_fconj';
    grind;
  . right;
    constructor;
    . assumption;
    . simp;

/-- Quasi-normal extension of `Modal.GL` by closed formula set `X` is either `Modal.GL_TBB (X.trace)` or `Modal.GL_TBBMinus (X.trace)` -/
theorem GL.eq_closed_sumQuasiNormal_GL_TBB_or_GL_TBBMinus :
  (∃ _ : X.regular T, Modal.GL.sumQuasiNormal X = Modal.GL_TBB (X.trace)) ∨
  (∃ X_singular : X.singular T, Modal.GL.sumQuasiNormal X = Modal.GL_TBBMinus (X.trace) (FormulaSet.comp_trace_spectrum Xll ▸ FormulaSet.spectrum_finite_of_singular Xll X_singular)) := by
  by_cases h : X.regular T;
  . left;
    constructor;
    . apply GL.eq_closed_regular_sumQuasiNormal_GL_TBB Xll h;
    . assumption;
  . right;
    constructor;
    . apply eq_closed_singular_sumQuasiNormal_GL_TBBMinus (T := T) Xll (by grind) h;
    . assumption

lemma iff_GL_TBB_subset : Modal.GL_TBB α ⊆ Modal.GL_TBB β ↔ α ⊆ β := by
  calc
    _ ↔ FormulaSet.trace (α.image (λ i => TBB i)) ⊆ FormulaSet.trace (β.image (λ i => TBB i)) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_trace (T := 𝗣𝗔);
      simp;
    _ ↔ α ⊆ β := by simp;

lemma iff_GL_TBBMinus_subset (hα : αᶜ.Finite := by grind) (hβ : βᶜ.Finite := by grind) : Modal.GL_TBBMinus α ⊆ Modal.GL_TBBMinus β ↔ α ⊆ β := by
  calc
    _ ↔ FormulaSet.spectrum ({∼(⩕ n ∈ hβ.toFinset, (TBB n))}) ⊆ FormulaSet.spectrum ({∼(⩕ n ∈ hα.toFinset, (TBB n))}) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔);
      simp;
    _ ↔ βᶜ ⊆ αᶜ := by rw [TBBMinus_spectrum, TBBMinus_spectrum];
    _ ↔ α ⊆ β   := by simp;

lemma GL_TBB_subset_GL_TBBMinus : Modal.GL_TBB β ⊆ Modal.GL_TBBMinus β := by
  apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔) ?_ ?_ ?_ |>.mpr;
  . rw [TBBMinus_spectrum];
    simp [FormulaSet.spectrum];
  . grind;
  . grind;
  . simp;

end

end Modal

end LO
