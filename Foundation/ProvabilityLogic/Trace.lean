import Foundation.Modal.Formula
import Foundation.Modal.Axioms

namespace LO

namespace Modal

namespace Formula


namespace letterless

variable {φ ψ : Formula α}

attribute [grind] letterless.def_imp₁ letterless.def_imp₂ letterless.def_box

@[simp, grind] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]
@[simp, grind] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]

@[grind] lemma of_imp_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ➝ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_neg_letterless (hφ : φ.letterless) : (∼φ).letterless := by simp_all [letterless]
@[grind] lemma of_or_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋎ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_and_letterless (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋏ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_box_letterless (hφ : φ.letterless) : (□φ).letterless := by simp_all [letterless]
@[grind] lemma of_multibox_letterless (hφ : φ.letterless) : (□^[n]φ).letterless := by
  induction n with
  | zero => simpa [letterless]
  | succ n ih => simp [letterless, ih]

end letterless


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

lemma trace_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.letterless) : φ.trace.Finite ∨ φ.traceᶜ.Finite := by
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

lemma TBB_spectrum : (TBB n).spectrum = {n}ᶜ := by
  rw [Formula.spectrum.def_imp, boxbot_spectrum, boxbot_spectrum];
  ext i;
  simp;
  omega;

lemma TBB_trace : (TBB n).trace = {n} := by
  simp [Formula.trace, TBB_spectrum, compl_compl];

end Modal



end LO
