import Foundation.Modal.Formula
import Foundation.Modal.Axioms
import Foundation.ProvabilityLogic.SolovaySentences
import Foundation.ProvabilityLogic.S.Completeness
import Foundation.Modal.Logic.S.Basic
import Foundation.Modal.Logic.Dz.Basic
import Mathlib.Tactic.TFAE

lemma Set.compl_inj_iff {a b : Set α} : aᶜ = bᶜ ↔ a = b := _root_.compl_inj_iff

namespace LO

namespace Modal

namespace Formula


namespace letterless

variable {φ ψ : Formula α}

attribute [grind] letterless.def_imp₁ letterless.def_imp₂ letterless.def_box

@[simp, grind] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]
@[simp, grind] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]

end letterless


section

variable {φ ψ : Formula α}

@[grind] lemma of_imp_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ➝ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_neg_letterless (hφ : φ.letterless) : (∼φ).letterless := by simp_all [letterless]
@[grind] lemma of_or_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋎ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_and_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋏ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_box_letterless (hφ : φ.letterless) : (□φ).letterless := by simp_all [letterless]
@[grind] lemma of_multibox_letterless (hφ : φ.letterless) : (□^[n]φ).letterless := by
  induction n with
  | zero => simpa [letterless]
  | succ n ih => simp [letterless, ih]
lemma of_fconj'_letterless {s} {Φ : β → Formula α} (h : ∀ i, (Φ i).letterless) : (⩕ i ∈ s, Φ i).letterless := by
  sorry;

end

/-- spectrum for letterless formula -/
def spectrum (φ : Formula ℕ) (φ_closed : φ.letterless := by grind) : Set ℕ :=
  match φ with
  | ⊥ => ∅
  | φ ➝ ψ => φ.spectrumᶜ ∪ ψ.spectrum
  | □φ => { n | ∀ i < n, i ∈ φ.spectrum }

namespace spectrum

variable {φ ψ : Formula ℕ} (hφ : φ.letterless := by grind) (hψ : ψ.letterless := by grind)

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


lemma def_fconj' {s} {Φ : α → Formula ℕ} (hΦ : ∀ i, (Φ i).letterless) : ((⩕ i ∈ s, Φ i).spectrum (of_fconj'_letterless hΦ)) = ⋂ i ∈ s, (Φ i).spectrum (hΦ i) := by
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
def trace (φ : Formula ℕ) (φ_closed : φ.letterless := by grind) := φ.spectrumᶜ

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

end Formula


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

@[simp] lemma TBB_letterless : (TBB n).letterless := by grind

lemma TBB_spectrum : (TBB n).spectrum = {n}ᶜ := by
  rw [Formula.spectrum.def_imp, boxbot_spectrum, boxbot_spectrum];
  ext i;
  simp;
  omega;

lemma TBB_trace : (TBB n).trace = {n} := by
  simp [Formula.trace, TBB_spectrum, compl_compl];


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

variable {φ ψ : Formula ℕ}

lemma iff_GL_provable_spectrum_Univ (_ : φ.letterless := by grind)
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

lemma iff_GL_provable_C_subset_spectrum
  (_ : φ.letterless := by grind)
  (_ : ψ.letterless := by grind)
  : Modal.GL ⊢! (φ ➝ ψ) ↔ φ.spectrum ⊆ ψ.spectrum := by
  apply Iff.trans $ iff_GL_provable_spectrum_Univ;
  rw [Formula.spectrum.def_imp];
  suffices (∀ i, i ∉ φ.spectrum ∨ i ∈ ψ.spectrum) ↔ φ.spectrum ⊆ ψ.spectrum by
    simpa [Set.eq_univ_iff_forall];
  constructor <;>
  . intro h i;
    have := @h i;
    tauto;

lemma iff_GL_provable_E_eq_spectrum
  (_ : φ.letterless := by grind)
  (_ : ψ.letterless := by grind)
  : Modal.GL ⊢! φ ⭤ ψ ↔ φ.spectrum = ψ.spectrum := by
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

lemma GL_trace_TBB_normalization (_ : φ.letterless := by grind) (h : φ.trace.Finite) : Modal.GL ⊢! φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_spectrum (by simpa) (Formula.of_fconj'_letterless (by simp)) |>.mpr;
  calc
    φ.spectrum = ⋂ i ∈ φ.trace, (TBB i).spectrum          := by
      have : φ.trace = ⋃ i ∈ φ.trace, (TBB i).trace := by ext i; simp [TBB_trace];
      simpa [Formula.trace] using Set.compl_inj_iff.mpr this;
    _          = ((⩕ n ∈ h.toFinset, (TBB n))).spectrum _ := by
      ext i;
      rw [Formula.spectrum.def_fconj' (by simp)];
      simp;

lemma GL_spectrum_TBB_normalization (_ : φ.letterless := by grind) (h : φ.spectrum.Finite) : Modal.GL ⊢! φ ⭤ ∼(⩕ n ∈ h.toFinset, (TBB n)) := by
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



section

protected def GLAlpha (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (α.image (λ i => TBB i))

protected def GLBetaMinus (β : Set ℕ) (hβ : βᶜ.Finite) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}

protected def SBeta (β : Set ℕ) (hβ : βᶜ.Finite) : Logic ℕ := Modal.S ∩ Modal.GLBetaMinus β hβ

protected def DzBeta (β : Set ℕ) (hβ : βᶜ.Finite) : Logic ℕ := Modal.Dz ∩ Modal.GLBetaMinus β hβ

end

end Modal


section

open FirstOrder ProvabilityLogic


/-- Realization which any propositional variable maps to `⊤` -/
abbrev FirstOrder.ArithmeticTheory.trivialPLRealization (T : ArithmeticTheory) [T.Δ₁] : T.PLRealization := ⟨λ _ => ⊤⟩

variable {T : ArithmeticTheory} [T.Δ₁]

namespace Modal

def Formula.regular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ℕ ⊧ₘ₀ (T.trivialPLRealization φ)

def Formula.singular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ¬(φ.regular T)

variable {φ : Modal.Formula _} (_ : φ.letterless)

lemma iff_regular_trace_finite : φ.regular T ↔ φ.trace.Finite := by
  constructor;
  . contrapose!;
    intro h;
    have := GL_spectrum_TBB_normalization (by grind) $ show φ.spectrum.Finite by
      simpa [Formula.trace] using or_iff_not_imp_left.mp Formula.trace_finite_or_cofinite h;
    sorry;
  . intro h;
    have := GL_trace_TBB_normalization (by grind) h;
    sorry;

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

end Modal

end


end LO
