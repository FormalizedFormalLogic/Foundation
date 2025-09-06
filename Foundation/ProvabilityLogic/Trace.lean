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


namespace FirstOrder

variable {M : Type*} [Nonempty M] [s : Structure L M]

@[simp, grind]
lemma models₀_lconj₂_iff {Γ : List (Sentence L)} : M ⊧ₘ₀ Γ.conj₂ ↔ (∀ σ ∈ Γ, M ⊧ₘ₀ σ) := by
  simp [models₀_iff, List.map_conj₂_prop];

@[simp, grind]
lemma models₀_fconj_iff {Γ : Finset (Sentence L)} : M ⊧ₘ₀ Γ.conj ↔ (∀ σ ∈ Γ, M ⊧ₘ₀ σ) := by
  simp [models₀_iff];

@[simp]
lemma models₀_fconj'_iff {s : Finset α} {Γ : α → Sentence L} : M ⊧ₘ₀ (⩕ i ∈ s, Γ i) ↔ (∀ i ∈ s, M ⊧ₘ₀ (Γ i)) := by
  simp [models₀_iff];

end FirstOrder



namespace ProvabilityLogic.Realization

omit [Theory.Δ₁ T]
variable {M} [Nonempty M] [Structure ℒₒᵣ M]
         {𝔅 : Provability T₀ T} {f : Realization 𝔅}
         {A B : Modal.Formula _}

@[simp, grind] lemma interpret_models₀_top : M ⊧ₘ₀ f ⊤ := by simp [Realization.interpret];
@[simp, grind] lemma interpret_models₀_bot : ¬M ⊧ₘ₀ f ⊥ := by simp [Realization.interpret];

@[simp, grind]
lemma interpret_models₀_neg : M ⊧ₘ₀ f (∼A) ↔ ¬(M ⊧ₘ₀ (f A)) := by
  simp [Realization.interpret];

@[simp, grind]
lemma interpret_models₀_imp : M ⊧ₘ₀ f (A ➝ B) ↔ (M ⊧ₘ₀ (f A) → M ⊧ₘ₀ (f B)) := by
  simp [Realization.interpret];

@[simp, grind]
lemma interpret_models₀_and : M ⊧ₘ₀ f (A ⋏ B) ↔ M ⊧ₘ₀ (f A) ∧ M ⊧ₘ₀ (f B) := by
  simp [Realization.interpret];

@[simp, grind]
lemma interpret_models₀_or : M ⊧ₘ₀ f (A ⋎ B) ↔ M ⊧ₘ₀ (f A) ∨ M ⊧ₘ₀ (f B) := by
  simp [Realization.interpret];
  tauto;

end ProvabilityLogic.Realization



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
@[grind] lemma of_iff (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⭤ ψ).letterless := by simp_all [letterless]

@[grind]
lemma of_lconj₂ {l : List (Formula α)} (h : ∀ φ ∈ l, φ.letterless) : (l.conj₂).letterless := by
  induction l using List.induction_with_singleton <;> simp_all [letterless];

@[grind]
lemma of_lconj' {l : List β} {Φ : β → Formula α} (h : ∀ i ∈ l, (Φ i).letterless) : (l.conj' Φ).letterless := by
  induction l using List.induction_with_singleton with
  | hcons _ _ _ ih => apply of_lconj₂; grind;
  | _  => simp_all [List.conj']

@[grind]
lemma of_fconj {s : Finset (Formula α)} (h : ∀ φ ∈ s, φ.letterless) : (s.conj).letterless := by
  apply of_lconj₂;
  simpa;

lemma of_fconj' {s : Finset β} {Φ : β → Formula α} (h : ∀ i, (Φ i).letterless) : (⩕ i ∈ s, Φ i).letterless := by
  apply of_lconj';
  grind;

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

lemma def_lconj₂ {l : List (Formula ℕ)} (h : ∀ φ ∈ l, φ.letterless) : (l.conj₂).spectrum (letterless.of_lconj₂ h) = ⋂ φ ∈ l, φ.spectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (a ⋏ ⋀l).spectrum (letterless.of_and (by grind) (letterless.of_lconj₂ (by grind))) = ⋂ φ, ⋂ (_ : φ ∈ a :: l), φ.spectrum by
      convert this;
      exact List.conj₂_cons_nonempty he;
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_lconj' {l : List β} {Φ : β → Formula ℕ} (h : ∀ i ∈ l, (Φ i).letterless) : (l.conj' Φ).spectrum (letterless.of_lconj' h) = ⋂ i ∈ l, (Φ i).spectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (Φ a ⋏ (List.conj' Φ l)).spectrum (letterless.of_and (by grind) (letterless.of_lconj₂ (by grind))) = ⋂ i, ⋂ (_ : i ∈ a :: l), (Φ i).spectrum by
      convert this;
      exact List.conj₂_cons_nonempty (a := Φ a) (as := List.map Φ l) (by simpa);
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_fconj {s : Finset (Formula _)} (h : ∀ φ ∈ s, φ.letterless) : (s.conj.spectrum (letterless.of_fconj h)) = ⋂ φ ∈ s, φ.spectrum := by
  unfold Finset.conj;
  rw [def_lconj₂];
  . simp;
  . simp_all;

lemma def_fconj' {s} {Φ : α → Formula ℕ} (hΦ : ∀ i, (Φ i).letterless) : ((⩕ i ∈ s, Φ i).spectrum (letterless.of_fconj' hΦ)) = ⋂ i ∈ s, (Φ i).spectrum (hΦ i) := by
  unfold Finset.conj';
  rw [def_lconj'];
  . simp;
  . grind;

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
abbrev _root_.LO.FirstOrder.ArithmeticTheory.trivialPLRealization (T : ArithmeticTheory) [T.Δ₁] : T.StandardRealization := ⟨λ _ => ⊤⟩

/-
lemma ww {T : ArithmeticTheory} [T.Δ₁] (φll : φ.letterless := by grind) : Arithmetic.Hierarchy 𝚺 1 (T.trivialPLRealization φ) := by
  induction φ with
  | hatom => simp_all only [letterless.not_atom];
  | hfalsum => simp;
  | himp _ _ ihφ ihψ =>
    replace ihφ := ihφ (by grind);
    replace ihψ := ihψ (by grind);
    simp_all [Realization.interpret];
-/

@[grind] def Regular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ℕ ⊧ₘ₀ (T.trivialPLRealization φ)

@[grind] def Singular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ¬(φ.Regular T)

namespace Regular

@[simp, grind] lemma def_bot : ¬((⊥ : Formula _).Regular T) := by simp [Formula.Regular, Realization.interpret];
@[simp, grind] lemma def_top : (⊤ : Formula _).Regular T := by simp [Formula.Regular, Realization.interpret];
@[grind] lemma def_neg : (∼φ).Regular T ↔ ¬(φ.Regular T) := by simp [Formula.Regular, Realization.interpret];
@[grind] lemma def_neg' : (∼φ).Regular T ↔ (φ.Singular T) := Iff.trans def_neg $ by rfl
@[grind] lemma def_and : (φ ⋏ ψ).Regular T ↔ (φ.Regular T) ∧ (ψ.Regular T) := by simp [Formula.Regular, Realization.interpret];
@[grind] lemma def_or : (φ ⋎ ψ).Regular T ↔ (φ.Regular T) ∨ (ψ.Regular T) := by simp [Formula.Regular, Realization.interpret]; tauto;
@[grind] lemma def_imp : (φ ➝ ψ).Regular T ↔ ((φ.Regular T) → (ψ.Regular T)) := by simp [Formula.Regular, Realization.interpret];
@[grind] lemma def_iff : (φ ⭤ ψ).Regular T ↔ ((φ.Regular T) ↔ (ψ.Regular T)) := by simp [Formula.Regular, Realization.interpret]; tauto;

@[simp, grind]
lemma def_lconj {l : List (Formula _)} : (l.conj₂).Regular T ↔ ∀ φ ∈ l, (φ.Regular T) := by
  induction l using List.induction_with_singleton' with
  | hcons _ _ _ ih => simp_all [Regular, Realization.interpret_models₀_and];
  | _ => simp;

@[simp, grind]
lemma def_lconj' {l : List _} {Φ : β → Formula _} : (l.conj' Φ).Regular T ↔ ∀ i ∈ l, ((Φ i).Regular T) := by
  induction l using List.induction_with_singleton' with
  | hcons _ _ _ ih => simp_all [Regular, Realization.interpret_models₀_and];
  | _ => simp;

@[simp, grind]
lemma def_fconj {s : Finset (Formula _)} : (s.conj).Regular T ↔ ∀ φ ∈ s, (φ.Regular T) := by
  simp [Finset.conj];

@[simp]
lemma def_fconj' {s : Finset _} {Φ : β → Formula _} : (⩕ i ∈ s, Φ i).Regular T ↔ ∀ i ∈ s, ((Φ i).Regular T) := by
  simp [Finset.conj'];

end Regular


namespace Singular

@[simp, grind] lemma def_bot : (⊥ : Formula _).Singular T := by grind
@[simp, grind] lemma def_top : ¬(⊤ : Formula _).Singular T := by grind
@[grind] lemma def_neg : (∼φ).Singular T ↔ ¬(φ.Singular T) := by grind;
@[grind] lemma def_neg' : (∼φ).Singular T ↔ (φ.Regular T) := by grind;
@[grind] lemma def_and : (φ ⋏ ψ).Singular T ↔ (φ.Singular T) ∨ (ψ.Singular T) := by grind
@[grind] lemma def_or : (φ ⋎ ψ).Singular T ↔ (φ.Singular T) ∧ (ψ.Singular T) := by grind
@[grind] lemma def_imp : (φ ➝ ψ).Singular T ↔ (¬(φ.Singular T) ∧ (ψ.Singular T)) := by grind

end Singular

end

end Formula


namespace FormulaSet

abbrev letterless (X : Modal.FormulaSet ℕ) := ∀ φ ∈ X, φ.letterless

protected def Regular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ∀ φ ∈ X, φ.Regular T

protected def Singular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ¬X.Regular T

lemma exists_singular_of_singular (hX_singular : X.Singular T) : ∃ φ ∈ X, φ.Singular T := by
  simpa [FormulaSet.Singular, FormulaSet.Regular] using hX_singular;

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
  suffices Hilbert.GL ⊢! φ ↔ ∀ (x : ℕ), x ∈ φ.spectrum by simpa [Set.eq_univ_iff_forall];
  apply Iff.trans (Logic.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree (φ := φ));
  constructor;
  . intro h n;
    apply Kripke.spectrum_TFAE (φ := φ) (by grind) |>.out 1 0 |>.mp;
    intro M r _ _ w _;
    have := @h M r {};
    sorry;
  . intro h;
    intro M r _;
    -- have := @h (Kripke.Frame.World.finHeight r)
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
  rw [
    Set.Subset.antisymm_iff,
    ←iff_GL_provable_C_subset_spectrum (φ := φ) (ψ := ψ),
    ←iff_GL_provable_C_subset_spectrum (φ := ψ) (ψ := φ),
  ];
  constructor;
  . intro h; constructor <;> cl_prover [h];
  . rintro ⟨h₁, h₂⟩; cl_prover [h₁, h₂];

lemma GL_trace_TBB_normalization (h : φ.trace.Finite) : Modal.GL ⊢! φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_spectrum (by simpa) (letterless.of_fconj' (by simp)) |>.mpr;
  calc
    _ = ⋂ i ∈ φ.trace, (TBB i).spectrum := by
      have : φ.trace = ⋃ i ∈ φ.trace, (TBB i).trace := by ext i; simp [TBB_trace];
      simpa [Formula.trace] using Set.compl_inj_iff.mpr this;
    _ = _ := by
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

/- TODO:
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
-/

end

variable
  [ℕ ⊧ₘ* T]
  (φll : φ.letterless := by grind)
  (ψll : ψ.letterless := by grind)

lemma letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] (φll : φ.letterless := by grind)
  : Modal.GL ⊢! φ ↔ T ⊢!. T.trivialPLRealization φ := by
  apply Iff.trans (GL.arithmetical_completeness_sound_iff (T := T) |>.symm);
  constructor;
  . intro h;
    apply h;
  . intro h f;
    have e : T.trivialPLRealization φ = f φ := Realization.letterless_interpret (by grind)
    exact e ▸ h;

lemma iff_regular_of_provable_E [𝗜𝚺₁ ⪯ T] (φll : φ.letterless := by grind) (ψll : ψ.letterless := by grind) (h : Modal.GL ⊢! φ ⭤ ψ)
  : φ.Regular T ↔ ψ.Regular T := by
  have : T ⊢!. T.trivialPLRealization (φ ⭤ ψ) := letterless_arithmetical_completeness (by grind) |>.mp h;
  have : ℕ ⊧ₘ₀ T.trivialPLRealization (φ ⭤ ψ) := ArithmeticTheory.SoundOn.sound (F := λ _ => True) this (by simp);
  simp [Realization.interpret, Formula.Regular] at this ⊢;
  tauto;

lemma iff_singular_of_provable_E [𝗜𝚺₁ ⪯ T] (φll : φ.letterless := by grind) (ψll : ψ.letterless := by grind) (h : Modal.GL ⊢! φ ⭤ ψ)
  : φ.Singular T ↔ ψ.Singular T := Iff.not $ iff_regular_of_provable_E φll ψll h

-- lemma w : ¬ℕ ⊧ₘ₀ T.trivialPLRealization (□^[n]⊥) := by


@[simp]
lemma TBB_regular : (TBB n).Regular T := by
  apply Formula.Regular.def_imp.mpr;
  intro h;
  exfalso;
  have : ¬ℕ ⊧ₘ₀ T.trivialPLRealization (□^[(n + 1)]⊥) := by
    simp only [Box.multibox_succ, Realization.interpret, Realization.interpret_boxItr_def];
    apply Provability.SoundOnModel.sound.not.mpr;
    apply Provability.iIncon_unprovable_of_sigma1_sound;
  apply this;
  exact h;

@[simp, grind]
lemma TBB_conj'_regular : (⩕ n ∈ s, TBB n).Regular T := by
  apply Formula.Regular.def_fconj'.mpr;
  simp;

@[simp, grind]
lemma TBB_conj'_letterless : (⩕ n ∈ s, TBB n).letterless := by
  apply Formula.letterless.of_fconj';
  simp;

@[simp, grind]
lemma TBBSet_letterless : FormulaSet.letterless ((λ i => TBB i) '' α) := by simp [FormulaSet.letterless]

@[simp]
lemma TBBSet_trace : FormulaSet.trace (α.image (λ i => TBB i)) = α := by
  ext i;
  rw [FormulaSet.def_trace_union];
  simp [TBB_trace];

@[simp]
lemma TBBSet_regular : FormulaSet.Regular T ((fun i ↦ TBB i) '' α) := by simp [FormulaSet.Regular];


variable
  [𝗜𝚺₁ ⪯ T]
  (φll : φ.letterless := by grind)
  (Xll : X.letterless := by grind)
  (Yll : Y.letterless := by grind)

lemma Formula.iff_regular_trace_finite : φ.Regular T ↔ φ.trace.Finite := by
  constructor;
  . contrapose!;
    intro h;
    have := GL_spectrum_TBB_normalization (by grind) $ show φ.spectrum.Finite by
      simpa [Formula.trace] using or_iff_not_imp_left.mp Formula.trace_finite_or_cofinite h;
    apply iff_regular_of_provable_E (by grind) (by grind) this |>.not.mpr;
    apply Formula.Regular.def_neg.not.mpr;
    push_neg;
    simp;
  . intro h;
    apply iff_regular_of_provable_E (by grind) (by grind) (GL_trace_TBB_normalization (by grind) h) |>.mpr;
    simp;

lemma Formula.spectrum_finite_of_singular : φ.Singular T → φ.spectrum.Finite := by
  contrapose!;
  suffices ¬(φ.spectrum).Finite → Formula.Regular T φ by simpa [Formula.Singular, not_not];
  intro h;
  apply iff_regular_trace_finite (by grind) |>.mpr;
  apply or_iff_not_imp_right.mp $ Formula.trace_finite_or_cofinite (by grind);
  simpa [Formula.trace] using h;

lemma letterless_arithmetical_completeness' : [
  Modal.GL ⊢! φ,
  T ⊢!. T.trivialPLRealization φ,
  φ.spectrum = Set.univ,
].TFAE := by
  tfae_have 1 ↔ 2 := letterless_arithmetical_completeness
  tfae_have 1 ↔ 3 := iff_GL_provable_spectrum_Univ
  tfae_finish;

lemma FormulaSet.spectrum_finite_of_singular (hX_singular : X.Singular T) : X.spectrum.Finite := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_singular_of_singular hX_singular;
  suffices (X.spectrum) ⊆ (φ.spectrum) by
    apply Set.Finite.subset;
    exact Formula.spectrum_finite_of_singular (by grind) hφ₂;
    assumption;
  intro i;
  simp_all [FormulaSet.spectrum];

lemma FormulaSet.regular_of_not_trace_cofinite : ¬X.traceᶜ.Finite → X.Regular T := by
  contrapose!;
  rw [comp_trace_spectrum];
  apply spectrum_finite_of_singular;
  assumption;


section

variable (Xll : X.letterless) (Yll : Y.letterless)
         {α α₁ α₂ β β₁ β₂ : Set ℕ} (hβ : βᶜ.Finite := by grind) (hβ₁ : β₁ᶜ.Finite := by grind) (hβ₂ : β₂ᶜ.Finite := by grind)


@[simp, grind]
lemma TBBMinus_letterless' : Formula.letterless (∼⩕ n ∈ hβ.toFinset, TBB n) := by
  apply Formula.letterless.of_neg;
  apply Formula.letterless.of_fconj';
  grind;

@[simp, grind]
lemma TBBMinus_letterless : FormulaSet.letterless {∼⩕ n ∈ hβ.toFinset, TBB n} := by simp [FormulaSet.letterless];

@[simp]
lemma TBBMinus_spectrum' : (∼⩕ n ∈ hβ.toFinset, TBB n).spectrum = βᶜ := by
  rw [Formula.spectrum.def_neg (Formula.letterless.of_fconj' (by grind)), Formula.spectrum.def_fconj' (by grind)];
  ext i;
  suffices (∀j ∉ β, i ≠ j) ↔ i ∈ β by simp [TBB_spectrum];
  constructor;
  . contrapose!; tauto;
  . contrapose!; rintro ⟨i, _, rfl⟩; tauto;

omit [𝗜𝚺₁ ⪯ T] in
@[simp]
lemma TBBMinus_spectrum : FormulaSet.spectrum {(∼⩕ n ∈ hβ.toFinset, TBB n)} = βᶜ := by simp [FormulaSet.spectrum]

omit [𝗜𝚺₁ ⪯ T] in
@[simp]
lemma TBBMinus_singular : FormulaSet.Singular T {∼⩕ n ∈ hβ.toFinset, TBB n} := by
  simp [FormulaSet.Singular, FormulaSet.Regular, Formula.Regular.def_neg];

open Classical in
lemma GL.iff_provable_closed_sumQuasiNormal_subset_spectrum {φ : Modal.Formula ℕ} (φll : φ.letterless) (hSR : X.Singular T ∨ φ.Regular T)
  : Modal.GL.sumQuasiNormal X ⊢! φ ↔ X.spectrum ⊆ φ.spectrum := by
  calc
    _ ↔ ∃ Y, (∀ ψ ∈ Y, ψ ∈ X) ∧ Modal.GL ⊢! Finset.conj Y ➝ φ := by
      sorry;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, (Finset.conj Y).spectrum (Formula.letterless.of_fconj (by grind)) ⊆ φ.spectrum := by
      constructor;
      . rintro ⟨Y, _, hY₂⟩;
        use Y;
        constructor;
        . apply iff_GL_provable_C_subset_spectrum (Formula.letterless.of_fconj (by grind)) |>.mp hY₂;
        . assumption;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . assumption;
        . apply iff_GL_provable_C_subset_spectrum (Formula.letterless.of_fconj (by grind)) |>.mpr hY₂;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, ⋂ ψ ∈ Y, ψ.spectrum ⊆ φ.spectrum := by
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
        . rw [Formula.spectrum.def_fconj];
          . grind;
          . grind;
        . assumption;
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

lemma GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (hSR : X.Singular T ∨ Y.Regular T)
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

lemma GL.iff_subset_closed_sumQuasiNormal_subset_trace (hSR : X.Singular T ∨ Y.Regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ Y.trace ⊆ X.trace :=
  Iff.trans (iff_subset_closed_sumQuasiNormal_subset_spectrum Xll Yll hSR) FormulaSet.iff_subset_spectrum_subset_trace

lemma GL.iff_eq_closed_sumQuasiNormal_eq_spectrum (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.spectrum = Y.spectrum := by
  simp only [Set.Subset.antisymm_iff];
  rw [
    iff_subset_closed_sumQuasiNormal_subset_spectrum Xll Yll (by tauto),
    iff_subset_closed_sumQuasiNormal_subset_spectrum Yll Xll (by tauto)
  ];
  tauto;


protected abbrev GLα (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (α.image (λ i => TBB i))

protected abbrev GLβ (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}

protected abbrev S_Inter_GLβ (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.S ∩ Modal.GLβ β hβ

protected abbrev Dz_Inter_GLβ (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.Dz ∩ Modal.GLβ β hβ


lemma GL.iff_eq_closed_sumQuasiNormal_eq_trace (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.trace = Y.trace :=
  Iff.trans (iff_eq_closed_sumQuasiNormal_eq_spectrum Xll Yll hXY) FormulaSet.iff_eq_spectrum_eq_trace

lemma GL.eq_closed_regular_sumQuasiNormal_GLα (X_regular : X.Regular T)
  : Modal.GL.sumQuasiNormal X = Modal.GLα (X.trace) := by
  apply GL.iff_eq_closed_sumQuasiNormal_eq_trace (T := T) ?_ ?_ ?_ |>.mpr;
  . simp;
  . assumption;
  . simp [FormulaSet.letterless];
  . left;
    constructor;
    . assumption;
    . simp;

lemma GL.eq_closed_singular_sumQuasiNormal_GLβ (X_singular : X.Singular T)
  : Modal.GL.sumQuasiNormal X = Modal.GLβ (X.trace) (FormulaSet.comp_trace_spectrum Xll ▸ FormulaSet.spectrum_finite_of_singular Xll X_singular) := by
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

/--
  Quasi-normal extension of `Modal.GL` by closed formula set `X` is
  either `Modal.GLα (X.trace)` (`X` is regular) or `Modal.GLβ (X.trace)` (`X` is singular)
-/
theorem GL.eq_closed_sumQuasiNormal_GLα_or_GLβ :
  (∃ _ : X.Regular T, Modal.GL.sumQuasiNormal X = Modal.GLα (X.trace)) ∨
  (∃ X_singular : X.Singular T, Modal.GL.sumQuasiNormal X = Modal.GLβ (X.trace) (FormulaSet.comp_trace_spectrum Xll ▸ FormulaSet.spectrum_finite_of_singular Xll X_singular)) := by
  by_cases h : X.Regular T;
  . left;
    constructor;
    . apply GL.eq_closed_regular_sumQuasiNormal_GLα Xll h;
    . assumption;
  . right;
    constructor;
    . apply eq_closed_singular_sumQuasiNormal_GLβ (T := T) Xll (by grind) h;
    . assumption

lemma iff_GLα_subset : Modal.GLα α₁ ⊆ Modal.GLα α₂ ↔ α₁ ⊆ α₂ := by
  calc
    _ ↔ FormulaSet.trace (α₁.image (λ i => TBB i)) ⊆ FormulaSet.trace (α₂.image (λ i => TBB i)) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_trace (T := 𝗣𝗔);
      simp;
    _ ↔ α₁ ⊆ α₂ := by simp;

lemma iff_GLβ_subset : Modal.GLβ β₁ ⊆ Modal.GLβ β₂ ↔ β₁ ⊆ β₂ := by
  calc
    _ ↔ FormulaSet.spectrum ({∼(⩕ n ∈ hβ₂.toFinset, (TBB n))}) ⊆ FormulaSet.spectrum ({∼(⩕ n ∈ hβ₁.toFinset, (TBB n))}) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔);
      simp;
    _ ↔ β₂ᶜ ⊆ β₁ᶜ := by rw [TBBMinus_spectrum, TBBMinus_spectrum];
    _ ↔ β₁ ⊆ β₂ := by simp;

lemma GLα_subset_GLβ : Modal.GLα β ⊆ Modal.GLβ β := by
  apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔) ?_ ?_ ?_ |>.mpr;
  . rw [TBBMinus_spectrum];
    simp [FormulaSet.spectrum];
  . grind;
  . grind;
  . simp;

end

end Modal

end LO
