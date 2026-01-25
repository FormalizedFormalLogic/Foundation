import Foundation.Modal.Logic.S.Basic
import Foundation.ProvabilityLogic.GL.Completeness

namespace LO

open FirstOrder FirstOrder.ProvabilityAbstraction
open ProvabilityLogic

variable {φ ψ : Modal.Formula ℕ}
         {X Y : Modal.FormulaSet ℕ}
         {T : ArithmeticTheory} [T.Δ₁]

namespace Modal

/-- letterlessSpectrum for letterless formula -/
def Formula.letterlessSpectrum (φ : Formula ℕ) (φ_closed : φ.Letterless := by grind) : Set ℕ :=
  match φ with
  | ⊥ => ∅
  | φ ➝ ψ => φ.letterlessSpectrumᶜ ∪ ψ.letterlessSpectrum
  | □φ => { n | ∀ i < n, i ∈ φ.letterlessSpectrum }


namespace Formula.letterlessSpectrum

variable (hφ : φ.Letterless := by grind) (hψ : ψ.Letterless := by grind)

@[simp, grind =] lemma def_bot : (⊥ : Formula _).letterlessSpectrum = ∅ := by simp [letterlessSpectrum]
@[simp, grind =] lemma def_top : (⊤ : Formula _).letterlessSpectrum = Set.univ := by simp [letterlessSpectrum]
@[grind =] lemma def_imp : (φ ➝ ψ).letterlessSpectrum = φ.letterlessSpectrumᶜ ∪ ψ.letterlessSpectrum := by simp [letterlessSpectrum]
@[grind =] lemma def_neg : (∼φ).letterlessSpectrum = φ.letterlessSpectrumᶜ := by simp [letterlessSpectrum]
@[grind =] lemma def_or  : (φ ⋎ ψ).letterlessSpectrum = φ.letterlessSpectrum ∪ ψ.letterlessSpectrum := by simp [letterlessSpectrum];
@[grind =] lemma def_and : (φ ⋏ ψ).letterlessSpectrum = φ.letterlessSpectrum ∩ ψ.letterlessSpectrum := by simp [letterlessSpectrum];
@[grind =] lemma def_box : (□φ).letterlessSpectrum = { n | ∀ i < n, i ∈ φ.letterlessSpectrum } := by simp [letterlessSpectrum];
@[grind =] lemma def_boxItr : (□^[(n + 1)]φ).letterlessSpectrum = { k | ∀ i < k, i ∈ (□^[n]φ).letterlessSpectrum } := by
  apply Eq.trans ?_ $ def_box (φ := □^[n]φ);
  induction n generalizing φ with
  | zero => simp [letterlessSpectrum]
  | succ n ih =>
    suffices (□^[n](□□φ)).letterlessSpectrum = (□□^[n](□φ)).letterlessSpectrum by simpa
    simpa using ih (φ := □φ) (by grind);
@[grind =] lemma def_boxdot : (⊡φ).letterlessSpectrum = { n | ∀ i ≤ n, i ∈ φ.letterlessSpectrum } := by
  ext i;
  suffices (i ∈ φ.letterlessSpectrum ∧ ∀ j < i, j ∈ φ.letterlessSpectrum) ↔ ∀ j ≤ i, j ∈ φ.letterlessSpectrum by simpa [letterlessSpectrum];
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

lemma def_lconj₂ {l : List (Formula ℕ)} (h : ∀ φ ∈ l, φ.Letterless) : (l.conj₂).letterlessSpectrum = ⋂ φ ∈ l, φ.letterlessSpectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (a ⋏ ⋀l).letterlessSpectrum = ⋂ φ, ⋂ (_ : φ ∈ a :: l), φ.letterlessSpectrum by
      convert this;
      exact List.conj₂_cons_nonempty he;
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_lconj' {l : List β} {Φ : β → Formula ℕ} (h : ∀ i ∈ l, (Φ i).Letterless) : (l.conj' Φ).letterlessSpectrum = ⋂ i ∈ l, (Φ i).letterlessSpectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (Φ a ⋏ (List.conj' Φ l)).letterlessSpectrum = ⋂ i, ⋂ (_ : i ∈ a :: l), (Φ i).letterlessSpectrum by
      convert this;
      exact List.conj₂_cons_nonempty (a := Φ a) (as := List.map Φ l) (by simpa);
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_fconj {s : Finset (Formula _)} (h : ∀ φ ∈ s, φ.Letterless) : (s.conj.letterlessSpectrum) = ⋂ φ ∈ s, φ.letterlessSpectrum := by
  unfold Finset.conj;
  rw [def_lconj₂];
  . simp;
  . simp_all;

lemma def_fconj' {s} {Φ : α → Formula ℕ} (hΦ : ∀ i, (Φ i).Letterless) : ((⩕ i ∈ s, Φ i).letterlessSpectrum (letterless_fconj' hΦ)) = ⋂ i ∈ s, (Φ i).letterlessSpectrum (hΦ i) := by
  unfold Finset.conj';
  rw [def_lconj'];
  . simp;
  . grind;

end Formula.letterlessSpectrum


/-- letterlessTrace for letterless formula -/
@[grind] def Formula.letterlessTrace (φ : Formula ℕ) (φ_closed : φ.Letterless := by grind) := (φ.letterlessSpectrum)ᶜ

namespace Formula.letterlessTrace

variable {φ ψ : Formula ℕ} (hφ : φ.Letterless := by grind) (hψ : ψ.Letterless := by grind)

@[simp, grind =] lemma def_top : (⊤ : Formula _).letterlessTrace = ∅ := by unfold letterlessTrace; rw [letterlessSpectrum.def_top]; tauto_set;
@[simp, grind =] lemma def_bot : (⊥ : Formula _).letterlessTrace = Set.univ := by unfold letterlessTrace; rw [letterlessSpectrum.def_bot]; tauto_set;
@[grind =] lemma def_neg : (∼φ).letterlessTrace = φ.letterlessTraceᶜ := by unfold letterlessTrace; rw [letterlessSpectrum.def_neg];
@[grind =] lemma def_and : (φ ⋏ ψ).letterlessTrace = φ.letterlessTrace ∪ ψ.letterlessTrace := by unfold letterlessTrace; rw [letterlessSpectrum.def_and]; tauto_set;
@[grind =] lemma def_or  : (φ ⋎ ψ).letterlessTrace = φ.letterlessTrace ∩ ψ.letterlessTrace := by unfold letterlessTrace; rw [letterlessSpectrum.def_or]; tauto_set;

end Formula.letterlessTrace


namespace Formula

@[grind =] lemma neg_letterlessTrace_letterlessSpectrum {φ : Formula ℕ} (hφ : φ.Letterless := by grind) : (∼φ).letterlessTrace = φ.letterlessSpectrum := by rw [letterlessTrace.def_neg]; simp [letterlessTrace];
@[grind =] lemma neg_letterlessSpectrum_letterlessTrace {φ : Formula ℕ} (hφ : φ.Letterless := by grind) : (∼φ).letterlessSpectrum = φ.letterlessTrace := by rw [letterlessSpectrum.def_neg]; simp [letterlessTrace];


lemma letterlessSpectrum_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.Letterless) : φ.letterlessSpectrum.Finite ∨ φ.letterlessSpectrum.Cofinite := by
  induction φ with
  | hfalsum => simp;
  | hatom => grind;
  | himp φ ψ ihφ ihψ =>
    rw [letterlessSpectrum.def_imp];
    rcases ihφ (by grind) with (ihφ | ihφ) <;>
    rcases ihψ (by grind) with (ihψ | ihψ);
    case himp.inr.inl =>
      left;
      grind [Set.Finite.union];
    . right;
      apply Set.cofinite_union_left;
      simpa [Set.Cofinite]
    . grind;
    . grind;
  | hbox φ ihφ =>
    by_cases h : φ.letterlessSpectrum = Set.univ;
    . right;
      rw [letterlessSpectrum.def_box, h];
      simp;
    . left;
      obtain ⟨k, hk₁, hk₂⟩ := exists_minimal_of_wellFoundedLT (λ k => k ∉ φ.letterlessSpectrum) $ Set.ne_univ_iff_exists_notMem _ |>.mp h;
      have : {n | ∀ i < n, i ∈ φ.letterlessSpectrum} = { n | n ≤ k} := by
        ext i;
        suffices (∀ j < i, j ∈ φ.letterlessSpectrum) ↔ i ≤ k by simpa [Set.mem_setOf_eq];
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
      rw [letterlessSpectrum.def_box, this];
      apply Set.finite_le_nat;

@[grind .]
lemma letterlessTrace_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.Letterless) : φ.letterlessTrace.Finite ∨ φ.letterlessTrace.Cofinite := by
  suffices φ.letterlessSpectrum.Finite ∨ φ.letterlessSpectrum.Cofinite by
    simp [Formula.letterlessTrace, Set.iff_cofinite_comp_finite];
    tauto;
  apply letterlessSpectrum_finite_or_cofinite hφ;

@[grind →]
lemma letterlessTrace_cofinite_of_letterlessSpectrum_infinite (hφ : φ.Letterless) : φ.letterlessTrace.Infinite → φ.letterlessTrace.Cofinite := by
  have := or_iff_not_imp_left.mp $ letterlessTrace_finite_or_cofinite hφ;
  grind [Set.Infinite];

@[grind →]
lemma letterlessTrace_finite_of_letterlessSpectrum_cofinite (hφ : φ.Letterless) : φ.letterlessTrace.Coinfinite → φ.letterlessTrace.Finite := by
  have := or_iff_not_imp_right.mp $ letterlessTrace_finite_or_cofinite hφ;
  simp only [Set.iff_coinfinite_not_cofinite];
  assumption;

@[simp, grind =]
lemma boxbot_letterlessSpectrum : (□^[n]⊥ : Formula ℕ).letterlessSpectrum = { i | i < n } := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = { i | ∀ k < i, k ∈ (□^[n]⊥ : Formula ℕ).letterlessSpectrum } := Formula.letterlessSpectrum.def_boxItr
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

end Formula


/-- Realization which any propositional variable maps to `⊤` -/
abbrev _root_.LO.FirstOrder.ArithmeticTheory.LetterlessStandardRealization (T : ArithmeticTheory) [T.Δ₁] : T.StandardRealization := ⟨λ _ => ⊤⟩


namespace Formula

@[grind] def Regular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ℕ ⊧ₘ (T.LetterlessStandardRealization φ)

@[grind] def Singular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ¬(φ.Regular T)

namespace Regular

@[simp] lemma def_bot : ¬((⊥ : Formula _).Regular T) := by simp [Formula.Regular, Realization.interpret];
@[simp] lemma def_top : (⊤ : Formula _).Regular T := by simp [Formula.Regular, Realization.interpret];
lemma def_neg : (∼φ).Regular T ↔ ¬(φ.Regular T) := by simp [Formula.Regular, Realization.interpret];
lemma def_neg' : (∼φ).Regular T ↔ (φ.Singular T) := Iff.trans def_neg $ by rfl
lemma def_and : (φ ⋏ ψ).Regular T ↔ (φ.Regular T) ∧ (ψ.Regular T) := by simp [Formula.Regular, Realization.interpret];
lemma def_or : (φ ⋎ ψ).Regular T ↔ (φ.Regular T) ∨ (ψ.Regular T) := by simp [Formula.Regular, Realization.interpret]; tauto;
lemma def_imp : (φ ➝ ψ).Regular T ↔ ((φ.Regular T) → (ψ.Regular T)) := by simp [Formula.Regular, Realization.interpret];
lemma def_iff : (φ ⭤ ψ).Regular T ↔ ((φ.Regular T) ↔ (ψ.Regular T)) := by simp [Formula.Regular, Realization.interpret]; tauto;

attribute [simp, grind .]
  def_bot
  def_top
  def_neg def_neg'
  def_and
  def_or
  def_imp
  def_iff

@[simp, grind =]
lemma def_lconj {l : List (Formula _)} : (l.conj₂).Regular T ↔ ∀ φ ∈ l, (φ.Regular T) := by
  induction l using List.induction_with_singleton' with
  | hcons _ _ _ ih => simp_all [Regular];
  | _ => simp;

@[simp, grind =]
lemma def_lconj' {l : List _} {Φ : β → Formula _} : (l.conj' Φ).Regular T ↔ ∀ i ∈ l, ((Φ i).Regular T) := by
  induction l using List.induction_with_singleton' with
  | hcons _ _ _ ih => simp_all [Regular];
  | _ => simp;

@[simp, grind =]
lemma def_fconj {s : Finset (Formula _)} : (s.conj).Regular T ↔ ∀ φ ∈ s, (φ.Regular T) := by
  simp [Finset.conj];

@[simp]
lemma def_fconj' {s : Finset _} {Φ : β → Formula _} : (⩕ i ∈ s, Φ i).Regular T ↔ ∀ i ∈ s, ((Φ i).Regular T) := by
  simp [Finset.conj'];

end Regular


namespace Singular

@[simp] lemma def_bot : (⊥ : Formula _).Singular T := by grind
@[simp] lemma def_top : ¬(⊤ : Formula _).Singular T := by grind
lemma def_neg : (∼φ).Singular T ↔ ¬(φ.Singular T) := by grind;
lemma def_neg' : (∼φ).Singular T ↔ (φ.Regular T) := by grind;
lemma def_and : (φ ⋏ ψ).Singular T ↔ (φ.Singular T) ∨ (ψ.Singular T) := by grind
lemma def_or : (φ ⋎ ψ).Singular T ↔ (φ.Singular T) ∧ (ψ.Singular T) := by grind
lemma def_imp : (φ ➝ ψ).Singular T ↔ (¬(φ.Singular T) ∧ (ψ.Singular T)) := by grind

attribute [grind .]
  def_bot
  def_top
  def_neg def_neg'
  def_and
  def_or
  def_imp

end Singular

end Formula


def FormulaSet.Regular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ∀ φ ∈ X, φ.Regular T
def FormulaSet.Singular (T : ArithmeticTheory) [T.Δ₁] (X : Modal.FormulaSet ℕ) := ¬X.Regular T

def FormulaSet.letterlessSpectrum (X : Modal.FormulaSet ℕ) (X_c : X.Letterless := by grind) := ⋂ φ ∈ X, φ.letterlessSpectrum
def FormulaSet.letterlessTrace (X : Modal.FormulaSet ℕ) (_ : X.Letterless := by grind [FormulaSet.Letterless]) := X.letterlessSpectrumᶜ

namespace FormulaSet

lemma exists_singular_of_singular (hX_singular : X.Singular T) : ∃ φ ∈ X, φ.Singular T := by
  simpa [FormulaSet.Singular, FormulaSet.Regular] using hX_singular;

variable (Xll : X.Letterless := by grind) (Yll : Y.Letterless := by grind)

lemma def_letterlessTrace_union : X.letterlessTrace = ⋃ φ ∈ X, φ.letterlessTrace := by simp [FormulaSet.letterlessTrace, FormulaSet.letterlessSpectrum, Formula.letterlessTrace]

lemma comp_letterlessTrace_letterlessSpectrum : X.letterlessTraceᶜ = X.letterlessSpectrum := by simp [FormulaSet.letterlessTrace]

lemma iff_subset_letterlessSpectrum_subset_letterlessTrace : X.letterlessSpectrum ⊆ Y.letterlessSpectrum ↔ Y.letterlessTrace ⊆ X.letterlessTrace := by simp [FormulaSet.letterlessTrace]

lemma iff_eq_letterlessSpectrum_eq_letterlessTrace : X.letterlessSpectrum = Y.letterlessSpectrum ↔ X.letterlessTrace = Y.letterlessTrace := by simp [FormulaSet.letterlessTrace];

end FormulaSet


/-- boxbot instance of axiomT -/
abbrev TBB (n : ℕ) : Formula ℕ := □^[(n + 1)]⊥ ➝ □^[n]⊥

section

variable {α α₁ α₂ β β₁ β₂ : Set ℕ} (hβ : β.Cofinite := by grind) (hβ₁ : β₁.Cofinite := by grind) (hβ₂ : β₂.Cofinite := by grind)

@[simp, grind .] lemma TBB_letterless : (TBB n).Letterless := by grind

@[simp]
lemma TBB_injective : Function.Injective TBB := by
  rintro i j;
  wlog hij : i < j; rcases (show i = j ∨ i > j by omega) <;> grind;
  suffices (□^[i]⊥ : Formula ℕ) = □^[j]⊥ → i = j by grind [Formula.inj_imp];
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij;
  simp [show ((i + k) + 1) = i + (k + 1) by omega, ←Box.boxItr_add (n := i) (m := (k + 1)), InjectiveBox.inj_multibox.eq_iff];

@[simp, grind .]
lemma TBB_letterlessSpectrum : (TBB n).letterlessSpectrum = {n}ᶜ := by
  ext i;
  rw [Formula.letterlessSpectrum.def_imp, Formula.boxbot_letterlessSpectrum, Formula.boxbot_letterlessSpectrum];
  simp;
  omega;

@[simp, grind .]
lemma TBB_letterlessTrace : (TBB n).letterlessTrace = {n} := by simp [Formula.letterlessTrace, TBB_letterlessSpectrum, compl_compl];
variable {α α₁ α₂ β β₁ β₂ : Set ℕ} (hβ : β.Cofinite := by grind) (hβ₁ : β₁.Cofinite := by grind) (hβ₂ : β₂.Cofinite := by grind)

@[simp, grind .]
lemma TBB_conj'_letterless : (⩕ n ∈ s, TBB n).Letterless := by
  apply Formula.letterless_fconj';
  grind;

@[simp, grind .]
lemma TBBSet_letterless : FormulaSet.Letterless ((λ i => TBB i) '' α) := by simp [FormulaSet.Letterless]

@[simp]
lemma TBBSet_letterlessTrace : FormulaSet.letterlessTrace (α.image (λ i => TBB i)) = α := by
  simp [FormulaSet.def_letterlessTrace_union];

@[simp, grind .]
lemma TBBMinus_letterless' : Formula.Letterless (∼⩕ n ∈ hβ.toFinset, TBB n) := by
  apply Formula.letterless_neg.mpr;
  apply Formula.letterless_fconj';
  grind;

@[simp, grind .]
lemma TBBMinus_letterless : FormulaSet.Letterless {∼⩕ n ∈ hβ.toFinset, TBB n} := by simp [FormulaSet.Letterless];

@[simp, grind .]
lemma TBBMinus_letterlessSpectrum' : (∼⩕ n ∈ hβ.toFinset, TBB n).letterlessSpectrum TBBMinus_letterless' = βᶜ := by
  rw [Formula.letterlessSpectrum.def_neg (Formula.letterless_fconj' (by grind)), Formula.letterlessSpectrum.def_fconj' (by grind)];
  ext i;
  suffices (∀j ∉ β, i ≠ j) ↔ i ∈ β by simp [TBB_letterlessSpectrum];
  constructor;
  . contrapose!; tauto;
  . contrapose!; rintro ⟨i, _, rfl⟩; tauto;

@[simp, grind .]
lemma TBBMinus_letterlessSpectrum : FormulaSet.letterlessSpectrum {(∼⩕ n ∈ hβ.toFinset, TBB n)} (by simp) = βᶜ := by simp [FormulaSet.letterlessSpectrum]


section

variable [ℕ ⊧ₘ* T]

@[simp high, grind .]
lemma TBB_regular : (TBB n).Regular T := by
  apply Formula.Regular.def_imp.mpr;
  intro h;
  exfalso;
  have : ¬ℕ ⊧ₘ T.LetterlessStandardRealization (□^[(n + 1)]⊥) := by
    simp only [Box.boxItr_succ, Realization.interpret.def_box, Realization.interpret.def_boxItr, Realization.interpret.def_bot];
    apply sound_on_model.not.mpr;
    apply iIncon_unprovable_of_sigma1_sound;
  apply this;
  exact h;

@[simp, grind .]
lemma TBB_conj'_regular : (⩕ n ∈ s, TBB n).Regular T := by
  apply Formula.Regular.def_fconj'.mpr;
  grind;

@[simp high]
lemma TBBSet_regular : FormulaSet.Regular T ((fun i ↦ TBB i) '' α) := by
  rintro _ ⟨_, _, rfl⟩;
  grind;


@[simp]
lemma TBBMinus_singular : FormulaSet.Singular T {∼⩕ n ∈ hβ.toFinset, TBB n} := by
  simp [FormulaSet.Singular, FormulaSet.Regular, Formula.Regular.def_neg];

end

end


namespace Kripke

open Kripke
open Formula.Kripke

variable {F : Frame} {r : F} [F.IsTree r] [Fintype F]

lemma iff_satisfies_mem_rank_letterlessSpectrum
  {M : Model} {r : M} [Fintype M] [M.IsTree r] {w : M}
  {φ : Formula ℕ} (φ_closed : φ.Letterless := by grind)
  : w ⊧ φ ↔ Frame.rank w ∈ φ.letterlessSpectrum := by
  induction φ generalizing w with
  | hbox φ ihφ =>
    calc
      w ⊧ □φ ↔ ∀ v, w ≺ v → v ⊧ φ                                  := by rfl;
      _      ↔ ∀ v, w ≺ v → (Frame.rank v ∈ φ.letterlessSpectrum) := by
        constructor;
        . intro h v; rw [←ihφ (by grind)]; apply h;
        . intro h v; rw [ihφ (by grind)]; apply h;
      _      ↔ ∀ i < (Frame.rank w), i ∈ φ.letterlessSpectrum := by
        constructor;
        . intro h i hi;
          obtain ⟨v, Rwv, rfl⟩ := Frame.exists_of_lt_height hi;
          apply h;
          assumption;
        . intro h v Rwv;
          apply h;
          apply Frame.rank_lt_of_rel;
          assumption;
      _      ↔ Frame.rank w ∈ (□φ).letterlessSpectrum := by
        rw [Formula.letterlessSpectrum.def_box]; simp;
  | _ => grind;

lemma iff_satisfies_TBB_ne_rank
  {M : Model} {r : M} [Fintype M] [M.IsTree r] {w : M} {n : ℕ}
  : w ⊧ TBB n ↔ Frame.rank w ≠ n := by
  apply Iff.trans iff_satisfies_mem_rank_letterlessSpectrum;
  simp;

abbrev Frame.finiteLinear (n : ℕ) : Kripke.Frame where
  World := Fin (n + 1)
  Rel := (· < ·)

namespace Frame.finiteLinear

abbrev of (i : Fin (n + 1)) : Frame.finiteLinear n := i

instance : (Frame.finiteLinear n) |>.IsFiniteTree 0 where
  asymm := by apply Fin.lt_asymm;
  root_generates := by simp [Frame.finiteLinear, Fin.pos_iff_ne_zero]

lemma rank_of_eq_sub (i : Fin (n + 1)) : Frame.rank (of i) = n - i := by
  induction i using Fin.reverseInduction
  case last =>
    suffices rank (of (Fin.last n)) = 0 by simpa
    apply fcwHeight_eq_zero_iff.mpr
    intro j
    show ¬(Fin.last n) < j
    simp [Fin.le_last]
  case cast i ih =>
    suffices rank (of i.castSucc) = rank (of i.succ) + 1 by
      rw [this, ih]
      simp; omega
    apply fcwHeight_eq_succ_fcwHeight
    · show i.castSucc < i.succ
      exact Fin.castSucc_lt_succ;
    · suffices ∀ j : Fin (n + 1), i.castSucc < j → i.succ ≤ j by
        simpa [le_iff_lt_or_eq] using this
      intro j
      exact id

@[simp] lemma rank_zero : Frame.rank (0 : Frame.finiteLinear n) = n := by simpa using rank_of_eq_sub 0

end Frame.finiteLinear

lemma letterlessSpectrum_TFAE (_ : φ.Letterless) : [
  n ∈ φ.letterlessSpectrum,
  ∀ M : Model, ∀ r, [M.IsTree r] → [Fintype M] → ∀ w : M.World, Frame.rank w = n → w ⊧ φ,
  ∃ M : Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M.World, Frame.rank w = n ∧ w ⊧ φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h M r _ _ w hw;
    apply iff_satisfies_mem_rank_letterlessSpectrum (by grind) |>.mpr;
    apply hw ▸ h;
  tfae_have 2 → 3 := by
    intro h;
    refine ⟨⟨Frame.finiteLinear n, λ p i => True⟩, 0, inferInstance, inferInstance, ⟨0, ?_, ?_⟩⟩;
    . simp;
    . apply h; simp;
  tfae_have 3 → 1 := by
    rintro ⟨M, r, _, _, w, rfl, hw⟩;
    apply iff_satisfies_mem_rank_letterlessSpectrum (by grind) |>.mp hw;
  tfae_finish;

end Kripke

section

open Formula
open LO.Entailment Modal.Entailment

variable {φ ψ : Formula ℕ} (φ_letterless : φ.Letterless) (ψ_letterless : ψ.Letterless)

lemma iff_GL_provable_letterlessSpectrum_Univ
  : Modal.GL ⊢ φ ↔ φ.letterlessSpectrum = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  constructor;
  . intro h n;
    apply Kripke.letterlessSpectrum_TFAE (φ := φ) (by grind) |>.out 1 0 |>.mp;
    intro M r _ _ w _;
    have := GL.Kripke.tree_completeness_TFAE.out 0 2 |>.mp h;
    apply @this M.toFrame r $ by constructor;
  . intro h;
    apply GL.Kripke.tree_completeness_TFAE.out 2 0 |>.mp;
    intro F r _ V w;
    have : Fintype (⟨F, V⟩ : Kripke.Model).World := Fintype.ofFinite _
    have := Kripke.letterlessSpectrum_TFAE (φ := φ) (n := Kripke.Frame.rank w) (by grind) |>.out 0 1 |>.mp;
    apply this (by grind) _ r w rfl;

lemma iff_GL_provable_C_subset_letterlessSpectrum : Modal.GL ⊢ (φ ➝ ψ) ↔ φ.letterlessSpectrum ⊆ ψ.letterlessSpectrum := by
  apply Iff.trans $ iff_GL_provable_letterlessSpectrum_Univ (by grind);
  rw [Formula.letterlessSpectrum.def_imp];
  suffices (∀ i, i ∉ φ.letterlessSpectrum ∨ i ∈ ψ.letterlessSpectrum) ↔ φ.letterlessSpectrum ⊆ ψ.letterlessSpectrum by
    simpa [Set.eq_univ_iff_forall];
  constructor <;>
  . intro h i;
    have := @h i;
    tauto;

lemma iff_GL_provable_E_eq_letterlessSpectrum : Modal.GL ⊢ φ ⭤ ψ ↔ φ.letterlessSpectrum = ψ.letterlessSpectrum := by
  rw [
    Set.Subset.antisymm_iff,
    ←iff_GL_provable_C_subset_letterlessSpectrum φ_letterless ψ_letterless,
    ←iff_GL_provable_C_subset_letterlessSpectrum ψ_letterless φ_letterless,
  ];
  constructor;
  . intro h; constructor <;> cl_prover [h];
  . rintro ⟨h₁, h₂⟩; cl_prover [h₁, h₂];

lemma GL_letterlessTrace_TBB_normalization (h : φ.letterlessTrace.Finite) : Modal.GL ⊢ φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_letterlessSpectrum φ_letterless (by grind) |>.mpr;
  calc
    _ = ⋂ i ∈ φ.letterlessTrace, (TBB i).letterlessSpectrum := by
      have : φ.letterlessTrace = ⋃ i ∈ φ.letterlessTrace, (TBB i).letterlessTrace := by ext i; simp [TBB_letterlessTrace];
      simpa [Formula.letterlessTrace] using compl_inj_iff.mpr this;
    _ = _ := by
      ext i;
      rw [Formula.letterlessSpectrum.def_fconj' (by simp)];
      simp;

lemma GL_letterlessSpectrum_TBB_normalization (h : φ.letterlessSpectrum.Finite) : Modal.GL ⊢ φ ⭤ ∼(⩕ n ∈ h.toFinset, (TBB n)) := by
  have h' : (∼φ).letterlessTrace.Finite := by rwa [Formula.neg_letterlessTrace_letterlessSpectrum];
  replace : Modal.GL ⊢ φ ⭤ ∼⩕ n ∈ h'.toFinset, TBB n := by
    have := GL_letterlessTrace_TBB_normalization (φ := ∼φ) (by grind) h';
    cl_prover [this];
  have e : h'.toFinset = h.toFinset := by simp [Formula.neg_letterlessTrace_letterlessSpectrum (show φ.Letterless by simpa)]
  exact e ▸ this;

lemma GL_proves_letterless_axiomWeakPoint3 (φ_letterless : φ.Letterless) (ψ_letterless : ψ.Letterless) : Modal.GL ⊢ (Axioms.WeakPoint3 φ ψ) := by
  apply iff_GL_provable_letterlessSpectrum_Univ (by grind) |>.mpr;
  apply Set.eq_univ_iff_forall.mpr;
  intro n;
  rw [letterlessSpectrum.def_or, letterlessSpectrum.def_box, letterlessSpectrum.def_box, letterlessSpectrum.def_imp, letterlessSpectrum.def_imp, letterlessSpectrum.def_boxdot, letterlessSpectrum.def_boxdot];
  suffices ∀ i < n, (∀ k ≤ i, k ∈ φ.letterlessSpectrum) → i ∉ ψ.letterlessSpectrum → ∀ j < n, (∀ k ≤ j, k ∈ ψ.letterlessSpectrum) → j ∈ φ.letterlessSpectrum by
    simpa [or_iff_not_imp_left];
  intro i _ hi hiψ j _ hj;
  apply hi;
  contrapose! hiψ;
  apply hj;
  omega;

/- TODO:
/-- Theorem 2 in [Valentini & Solitro 1983] -/
lemma iff_provable_GLPoint3_letterless_provable_GL : Modal.GLPoint3 ⊢ φ ↔ (∀ s : ZeroSubstitution _, Modal.GL ⊢ φ⟦s.1⟧) := by
  constructor;
  . suffices Modal.GLPoint3 ⊢ φ → (∀ s : ZeroSubstitution _, Modal.GL ⊢ φ⟦s.1⟧) by simpa;
    intro h s;
    induction h using Hilbert.Normal.rec! with
    | axm t ht =>
      rcases ht with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply GL_proves_letterless_axiomWeakPoint3 <;>
        apply Formula.Letterless_zeroSubst;
    | mdp h₁ h₂ => exact h₁ ⨀ h₂;
    | nec h => apply nec! h;
    | _ => simp;
  . contrapose!;
    suffices Modal.GLPoint3 ⊬ φ → (∃ s : ZeroSubstitution _, Modal.GL ⊬ φ⟦s.1⟧) by simpa;
    -- Kripke semantical arguments (?)
    intro h;
    sorry;
-/

end

variable
  [ℕ ⊧ₘ* T]
  (φ_letterless : φ.Letterless) (ψ_letterless : ψ.Letterless)
  (X_letterless : X.Letterless) (Y_letterless : Y.Letterless)

lemma letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.Letterless)
  : Modal.GL ⊢ φ ↔ T ⊢ T.LetterlessStandardRealization φ := by
  apply Iff.trans (GL.arithmetical_completeness_sound_iff (T := T) |>.symm);
  constructor;
  . intro h;
    apply h;
  . intro h f;
    have e : T.LetterlessStandardRealization φ = f φ := Realization.letterless_interpret φ_letterless
    exact e ▸ h;

lemma iff_regular_of_provable_E [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.Letterless) (ψ_letterless : ψ.Letterless) (h : Modal.GL ⊢ φ ⭤ ψ)
  : φ.Regular T ↔ ψ.Regular T := by
  have : T ⊢ T.LetterlessStandardRealization (φ ⭤ ψ) := letterless_arithmetical_completeness (by grind) |>.mp h;
  have : ℕ ⊧ₘ T.LetterlessStandardRealization (φ ⭤ ψ) := ArithmeticTheory.SoundOn.sound (F := λ _ => True) this (by simp);
  simp [Realization.interpret, Formula.Regular] at this ⊢;
  tauto;

lemma iff_singular_of_provable_E [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.Letterless) (ψ_letterless : ψ.Letterless) (h : Modal.GL ⊢ φ ⭤ ψ)
  : φ.Singular T ↔ ψ.Singular T := Iff.not $ iff_regular_of_provable_E φ_letterless ψ_letterless h


variable [𝗜𝚺₁ ⪯ T]

lemma Formula.iff_regular_letterlessTrace_finite : φ.Regular T ↔ φ.letterlessTrace.Finite := by
  constructor;
  . contrapose!;
    intro h;
    have : φ.letterlessSpectrum.Finite := by
      have := letterlessTrace_cofinite_of_letterlessSpectrum_infinite (by grind) h;
      have : (φ.letterlessTrace)ᶜ.Finite := Set.iff_cofinite_comp_finite.mp this;
      simpa [Formula.letterlessTrace] using this;
    apply iff_regular_of_provable_E ?_ ?_ (GL_letterlessSpectrum_TBB_normalization (by assumption) this) |>.not.mpr;
    . apply Formula.Regular.def_neg.not.mpr;
      push_neg;
      exact TBB_conj'_regular;
    . assumption;
    . convert @TBBMinus_letterless' φ.letterlessTrace $ by simpa [Formula.letterlessTrace, Set.Cofinite]
      simp [Formula.letterlessTrace]
  . intro h;
    apply iff_regular_of_provable_E (by grind) (by simp) (GL_letterlessTrace_TBB_normalization (by grind) h) |>.mpr;
    simp;

lemma Formula.letterlessSpectrum_finite_of_singular : φ.Singular T → φ.letterlessSpectrum.Finite := by
  contrapose!;
  suffices ¬(φ.letterlessSpectrum).Finite → Formula.Regular T φ by simpa [Formula.Singular, not_not];
  intro h;
  apply iff_regular_letterlessTrace_finite (by grind) |>.mpr;
  apply or_iff_not_imp_right.mp $ Formula.letterlessTrace_finite_or_cofinite (by grind);
  simpa [Formula.letterlessTrace] using h;

lemma letterless_arithmetical_completeness' : [
  Modal.GL ⊢ φ,
  T ⊢ T.LetterlessStandardRealization φ,
  φ.letterlessSpectrum = Set.univ,
].TFAE := by
  tfae_have 1 ↔ 2 := letterless_arithmetical_completeness (by grind)
  tfae_have 1 ↔ 3 := iff_GL_provable_letterlessSpectrum_Univ (by grind)
  tfae_finish;

lemma FormulaSet.letterlessSpectrum_finite_of_singular (X_singular : X.Singular T) : X.letterlessSpectrum.Finite := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_singular_of_singular X_singular;
  suffices (X.letterlessSpectrum) ⊆ (φ.letterlessSpectrum) by
    apply Set.Finite.subset ?_ this;
    exact Formula.letterlessSpectrum_finite_of_singular (by grind) hφ₂;
  intro i;
  simp_all [FormulaSet.letterlessSpectrum];

lemma FormulaSet.regular_of_not_letterlessTrace_cofinite : ¬X.letterlessTrace.Cofinite → X.Regular T := by
  contrapose!;
  suffices ¬X.Regular T → (X.letterlessSpectrum).Finite by simpa [FormulaSet.letterlessTrace, Set.Cofinite];
  apply letterlessSpectrum_finite_of_singular;
  assumption;

section

open Classical LO.Entailment in
lemma GL.iff_provable_closed_sumQuasiNormal_subset_letterlessSpectrum (hSR : X.Singular T ∨ φ.Regular T)
  : Modal.GL.sumQuasiNormal X ⊢ φ ↔ X.letterlessSpectrum ⊆ φ.letterlessSpectrum := by
  calc
    _ ↔ ∃ Y, (∀ ψ ∈ Y, ψ ∈ X) ∧ Modal.GL ⊢ Finset.conj Y ➝ φ := Logic.sumQuasiNormal.iff_provable_finite_provable_letterless X_letterless
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, (Finset.conj Y).letterlessSpectrum (Formula.letterless_fconj (by grind)) ⊆ φ.letterlessSpectrum := by
      constructor;
      . rintro ⟨Y, _, hY₂⟩;
        use Y;
        constructor;
        . apply iff_GL_provable_C_subset_letterlessSpectrum (Formula.letterless_fconj (by grind)) (by grind) |>.mp hY₂;
        . assumption;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . assumption;
        . apply iff_GL_provable_C_subset_letterlessSpectrum (Formula.letterless_fconj (by grind)) (by grind) |>.mpr hY₂;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, ⋂ ψ ∈ Y, ψ.letterlessSpectrum ⊆ φ.letterlessSpectrum := by
      constructor;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y, hY₁;
        suffices Y.conj.letterlessSpectrum = ⋂ ψ ∈ Y, ψ.letterlessSpectrum by simpa [this] using hY₂;
        rw [Formula.letterlessSpectrum.def_fconj];
        grind;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . rw [Formula.letterlessSpectrum.def_fconj];
          . grind;
          . grind;
        . assumption;
    _ ↔ (⋂ ψ ∈ X, ψ.letterlessSpectrum) ⊆ φ.letterlessSpectrum := by
      constructor;
      . rintro ⟨Y, hY₁, hY₂⟩ i hi;
        apply hY₂;
        simp_all;
      . intro h;
        rcases hSR with X_singular | φ_regular;
        . wlog X_infinite : X.Infinite
          . replace X_infinite := Set.not_infinite.mp X_infinite;
            use X_infinite.toFinset;
            refine ⟨?_, ?_⟩
            . simp;
            . intro i hi;
              apply h;
              simpa using hi;

          obtain ⟨ψ, hψX, ψ_singular⟩ : ∃ ψ ∈ X, ψ.Singular T := FormulaSet.exists_singular_of_singular X_singular;

          obtain ⟨f, f0, f_monotone, fX, f_inv⟩ := Set.infinitely_finset_approximate (Countable.to_set inferInstance) X_infinite hψX;
          have f_conj_letterless : ∀ i, (f i).conj.Letterless := λ i => Formula.letterless_fconj $ λ ξ hξ => X_letterless _ $ fX _ hξ;

          let sf := λ i => ⋂ ξ, ⋂ (h : ξ ∈ f i), ξ.letterlessSpectrum (X_letterless ξ $ fX _ $ by assumption);
          have sf_eq : ∀ i, sf i = Formula.letterlessSpectrum ((f i).conj) (f_conj_letterless _) := by
            intro i;
            rw [Formula.letterlessSpectrum.def_fconj (λ ξ hξ => X_letterless _ $ fX _ hξ)];
          have sf_monotone : ∀ i, sf (i + 1) ⊆ sf i := by
            intro i;
            rw [sf_eq (i + 1), sf_eq i];
            apply iff_GL_provable_C_subset_letterlessSpectrum (f_conj_letterless _) (f_conj_letterless _) |>.mp;
            -- TODO: `Γ ⊇ Δ` → `⊢ Γ.conj → Δ.conj`
            apply right_Fconj!_intro;
            intro χ hχ;
            apply left_Fconj!_intro;
            apply f_monotone _ |>.1 hχ;
          replace sf_monotone : ∀ i j, i ≤ j → sf j ⊆ sf i := by
            intro i j hij;
            have : ∀ k, (sf (i + k)) ⊆ sf i := by
              intro k;
              induction k with
              | zero => simp;
              | succ k ih =>
                rw [show i + (k + 1) = (i + k) + 1 by omega];
                exact Set.Subset.trans (sf_monotone (i + k)) ih;
            rw [(show j = i + (j - i) by omega)];
            apply this;

          have sf0_eq : sf 0 = ψ.letterlessSpectrum := by simp [sf, f0];
          have sf0_finite : (sf 0).Finite := by rw [sf0_eq]; exact Formula.letterlessSpectrum_finite_of_singular (by grind) ψ_singular;
          have sf_finite : ∀ i, (sf i).Finite := by
            intro i;
            apply Set.Finite.subset sf0_finite;
            apply sf_monotone _ _ (by omega);

          have sf_X : ∀ i, sf i ⊇ X.letterlessSpectrum := by
            intro i n;
            suffices (∀ (ξ : Formula ℕ) (_ : ξ ∈ X), n ∈ ξ.letterlessSpectrum _) → ∀ (ξ : Formula ℕ) (_ : ξ ∈ f i), n ∈ ξ.letterlessSpectrum _ by
              simpa [sf, FormulaSet.letterlessSpectrum];
            intro h ξ hξ;
            apply h;
            apply fX i hξ;

          obtain ⟨k, hk⟩ : ∃ k, sf k = X.letterlessSpectrum := by
            by_contra! hC;
            have : ∀ i, ∃ n, n ∈ sf i ∧ n ∉ X.letterlessSpectrum := by
              intro i;
              exact Set.ssubset_iff_exists.mp (Set.ssubset_of_subset_ne (sf_X i) (hC i).symm) |>.2;

            apply Finset.no_ssubset_descending_chain (f := λ i => sf_finite i |>.toFinset);

            intro i;
            obtain ⟨n, hn₁, hn₂⟩ := this i;
            obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ, ∃ (_ : ξ ∈ X), n ∉ ξ.letterlessSpectrum _ := by simpa [FormulaSet.letterlessSpectrum] using hn₂;
            obtain ⟨j, hj⟩ := f_inv ξ hξ₁;

            have : i < j := by
              by_contra hC;
              have := Set.Subset.trans (sf_monotone j i (by omega)) $ show sf j ⊆ ξ.letterlessSpectrum by
                intro _ hn;
                apply hn;
                use ξ;
                simp_all;
              apply hξ₂;
              apply this;
              apply hn₁;
            use j;
            constructor;
            . assumption;
            . suffices (sf j) ⊂ (sf i) by simpa [sf_finite]
              exact Set.ssubset_iff_exists.mpr ⟨sf_monotone i j (by omega), by
                use n;
                constructor;
                . assumption;
                . suffices ∃ χ, ∃ _ : χ ∈ f j, n ∉ χ.letterlessSpectrum _ by simpa [sf];
                  use ξ;
                  simp_all;
              ⟩;

          use (f k)
          refine ⟨?_, ?_⟩;
          . apply fX;
          . apply Set.Subset.trans ?_ h;
            rw [←FormulaSet.letterlessSpectrum, ←hk];
            assumption;
        . have H : ∀ i ∈ φ.letterlessTrace, ∃ ψ, ∃ _ : ψ ∈ X, i ∈ ψ.letterlessTrace := by
            have : φ.letterlessTrace ⊆ ⋃ ψ ∈ X, ψ.letterlessTrace := by
              apply Set.compl_subset_compl.mp;
              simpa [Formula.letterlessTrace]
            simpa [Set.subset_def];

          let ξ := λ i (hi : i ∈ φ.letterlessTrace) => (H i hi |>.choose);
          have ξ_in_X : ∀ {i hi}, (ξ i hi) ∈ X := by
            intro i hi;
            apply (H i hi |>.choose_spec).1;
          have ξ_letterless : ∀ {i hi}, (ξ i hi).Letterless := by
            intro i hi;
            apply X_letterless _  $ ξ_in_X;
            assumption
          have H₂ : ⋂ i ∈ φ.letterlessTrace, (ξ i (by assumption)).letterlessSpectrum ⊆ φ.letterlessSpectrum := by
            suffices φ.letterlessTrace ⊆ ⋃ i ∈ φ.letterlessTrace, (ξ i (by assumption)).letterlessTrace by
              apply Set.compl_subset_compl.mp;
              simpa;
            intro j hj;
            simp only [Set.mem_iUnion, ξ];
            use j, hj;
            apply H j hj |>.choose_spec.2;
          use @Finset.univ (α := { i // i ∈ φ.letterlessTrace }) ?_ |>.image (λ i => (ξ i.1 i.2));
          . refine ⟨?_, ?_⟩;
            . simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, forall_exists_index];
              rintro ψ i hi rfl;
              apply ξ_in_X;
              assumption
            . intro i hi;
              apply H₂;
              simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, Set.iInter_exists, Set.mem_iInter] at hi ⊢;
              intro j hj;
              apply hi (ξ j hj) j hj rfl;
          . apply Set.Finite.fintype (s := φ.letterlessTrace);
            exact Formula.iff_regular_letterlessTrace_finite (by grind) |>.mp φ_regular;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum (hSR : X.Singular T ∨ Y.Regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ X.letterlessSpectrum ⊆ Y.letterlessSpectrum := by
  calc
    _ ↔ ∀ ψ ∈ Y, Modal.GL.sumQuasiNormal X ⊢ ψ := Logic.sumQuasiNormal.iff_subset
    _ ↔ ∀ ψ, (h : ψ ∈ Y) → X.letterlessSpectrum ⊆ ψ.letterlessSpectrum := by
      constructor;
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_letterlessSpectrum (T := T) (by grind) (by grind) (by tauto) |>.mp;
        exact h ψ (by simpa);
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_letterlessSpectrum (T := T) (by grind) (by grind) (by tauto) |>.mpr;
        apply h;
        simpa;
    _ ↔ X.letterlessSpectrum ⊆ (⋂ ψ ∈ Y, ψ.letterlessSpectrum) := by simp;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_letterlessTrace (hSR : X.Singular T ∨ Y.Regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ Y.letterlessTrace ⊆ X.letterlessTrace :=
  Iff.trans (iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum X_letterless Y_letterless hSR) FormulaSet.iff_subset_letterlessSpectrum_subset_letterlessTrace

lemma GL.iff_eq_closed_sumQuasiNormal_eq_letterlessSpectrum (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.letterlessSpectrum = Y.letterlessSpectrum := by
  simp only [Set.Subset.antisymm_iff];
  rw [
    iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum X_letterless Y_letterless (by tauto),
    iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum Y_letterless X_letterless (by tauto)
  ];
  tauto;



protected abbrev GLα (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (α.image (λ i => TBB i))

protected abbrev GLβMinus (β : Set ℕ) (hβ : β.Cofinite := by grind) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}


lemma GL.iff_eq_closed_sumQuasiNormal_eq_letterlessTrace (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.letterlessTrace = Y.letterlessTrace :=
  Iff.trans (iff_eq_closed_sumQuasiNormal_eq_letterlessSpectrum X_letterless Y_letterless hXY) FormulaSet.iff_eq_letterlessSpectrum_eq_letterlessTrace

lemma GL.eq_closed_regular_sumQuasiNormal_GLα (X_regular : X.Regular T)
  : Modal.GL.sumQuasiNormal X = Modal.GLα (X.letterlessTrace) := by
  apply GL.iff_eq_closed_sumQuasiNormal_eq_letterlessTrace (T := T) ?_ ?_ ?_ |>.mpr;
  . simp;
  . assumption;
  . simp [FormulaSet.Letterless];
  . left;
    constructor;
    . assumption;
    . simp;


@[grind! <=]
lemma FormulaSet.comp_letterlessTrace_finite_of_singular (X_singular : X.Singular T) : (X.letterlessTrace).Cofinite := by
  have := FormulaSet.letterlessSpectrum_finite_of_singular X_letterless X_singular;
  have := FormulaSet.comp_letterlessTrace_letterlessSpectrum X_letterless;
  grind;

lemma GL.eq_closed_singular_sumQuasiNormal_GLβMinus (X_singular : X.Singular T) : Modal.GL.sumQuasiNormal X = Modal.GLβMinus (X.letterlessTrace) := by
  apply GL.iff_eq_closed_sumQuasiNormal_eq_letterlessSpectrum (T := T) ?_ ?_ ?_ |>.mpr;
  . simp [TBBMinus_letterlessSpectrum, FormulaSet.letterlessTrace];
  . assumption;
  . grind;
  . right;
    constructor;
    . assumption;
    . simp;

/--
  Quasi-normal extension of `Modal.GL` by closed formula set `X` is
  either `Modal.GLα (X.letterlessTrace)` (`X` is regular) or `Modal.GLβMinus (X.letterlessTrace)` (`X` is singular)
-/
theorem GL.eq_closed_sumQuasiNormal_GLα_or_GLβMinus :
  (∃ _ : X.Regular T, Modal.GL.sumQuasiNormal X = Modal.GLα (X.letterlessTrace)) ∨
  (∃ _ : X.Singular T, Modal.GL.sumQuasiNormal X = Modal.GLβMinus (X.letterlessTrace)) := by
  by_cases h : X.Regular T;
  . left;
    constructor;
    . apply GL.eq_closed_regular_sumQuasiNormal_GLα X_letterless h;
    . assumption;
  . right;
    constructor;
    . apply eq_closed_singular_sumQuasiNormal_GLβMinus (T := T) X_letterless h;
    . assumption

lemma iff_GLα_subset : Modal.GLα α₁ ⊆ Modal.GLα α₂ ↔ α₁ ⊆ α₂ := by
  calc
    _ ↔ FormulaSet.letterlessTrace (α₁.image (λ i => TBB i)) ⊆ FormulaSet.letterlessTrace (α₂.image (λ i => TBB i)) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_letterlessTrace (T := 𝗣𝗔) (by grind) (by grind);
      simp;
    _ ↔ α₁ ⊆ α₂ := by simp;

lemma iff_GLβMinus_subset (hβ₁ : β₁.Cofinite) (hβ₂ : β₂.Cofinite) : Modal.GLβMinus β₁ ⊆ Modal.GLβMinus β₂ ↔ β₁ ⊆ β₂ := by
  calc
    _ ↔ FormulaSet.letterlessSpectrum ({∼(⩕ n ∈ hβ₂.toFinset, (TBB n))}) ⊆ FormulaSet.letterlessSpectrum ({∼(⩕ n ∈ hβ₁.toFinset, (TBB n))}) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum (T := 𝗣𝗔) (by grind) (by grind);
      simp;
    _ ↔ β₂ᶜ ⊆ β₁ᶜ := by rw [TBBMinus_letterlessSpectrum, TBBMinus_letterlessSpectrum];
    _ ↔ β₁ ⊆ β₂ := by simp;

lemma GLα_subset_GLβMinus (hβ : β.Cofinite) : Modal.GLα β ⊆ Modal.GLβMinus β := by
  apply GL.iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum (T := 𝗣𝗔) ?_ ?_ ?_ |>.mpr;
  . simp [FormulaSet.letterlessSpectrum];
  . grind;
  . grind;
  . simp;

end

end Modal

end LO
