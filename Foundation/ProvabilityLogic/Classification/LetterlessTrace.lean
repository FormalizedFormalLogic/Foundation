module

public import Foundation.Modal.Logic.S.Basic
public import Foundation.ProvabilityLogic.GL.Uniform
public import Foundation.Vorspiel.Set.Cofinite

@[expose] public section

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
  | φ ➝ ψ => (φ.letterlessSpectrum)ᶜ ∪ ψ.letterlessSpectrum
  | □φ => { n | ∀ i < n, i ∈ φ.letterlessSpectrum }


namespace Formula.letterlessSpectrum

-- variable {hφ : φ.Letterless}{hψ : ψ.Letterless}

@[simp, grind =] lemma def_bot : (⊥ : Formula _).letterlessSpectrum = ∅ := by simp [letterlessSpectrum]
@[simp, grind =] lemma def_top : (⊤ : Formula _).letterlessSpectrum = Set.univ := by simp [letterlessSpectrum]
@[grind =] lemma def_imp {hφψ : Letterless (φ ➝ ψ)} : (φ ➝ ψ).letterlessSpectrum hφψ = φ.letterlessSpectrumᶜ ∪ ψ.letterlessSpectrum := by simp [letterlessSpectrum]
@[grind =] lemma def_neg {hφ : Letterless (∼φ)} : (∼φ).letterlessSpectrum hφ = φ.letterlessSpectrumᶜ := by simp [letterlessSpectrum]
@[grind =] lemma def_or {hφψ : Letterless (φ ⋎ ψ)}  : (φ ⋎ ψ).letterlessSpectrum hφψ = φ.letterlessSpectrum ∪ ψ.letterlessSpectrum := by simp [letterlessSpectrum];
@[grind =] lemma def_and {hφψ : Letterless (φ ⋏ ψ)} : (φ ⋏ ψ).letterlessSpectrum hφψ = φ.letterlessSpectrum ∩ ψ.letterlessSpectrum := by simp [letterlessSpectrum];
@[grind =] lemma def_box {hφ : Letterless (□φ)} : (□φ).letterlessSpectrum hφ = { n | ∀ i < n, i ∈ φ.letterlessSpectrum } := by simp [letterlessSpectrum];
@[grind =] lemma def_boxItr {n} {hφ : Letterless (□^[(n + 1)]φ)} : (□^[(n + 1)]φ).letterlessSpectrum hφ = { k | ∀ i < k, i ∈ (□^[n]φ).letterlessSpectrum } := by
  apply Eq.trans ?_ $ def_box (φ := □^[n]φ);
  . grind;
  . induction n generalizing φ with
    | zero => grind;
    | succ n ih =>
      suffices (□^[n](□□φ)).letterlessSpectrum = (□□^[n](□φ)).letterlessSpectrum by grind;
      simpa using @ih (φ := □φ) (by grind);
@[grind =] lemma def_boxdot {hφ : Letterless (⊡φ)} : (⊡φ).letterlessSpectrum hφ = { n | ∀ i ≤ n, i ∈ φ.letterlessSpectrum } := by
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

lemma def_lconj₂ {l : List (Formula ℕ)} (h : (l.conj₂).Letterless) : (l.conj₂).letterlessSpectrum = ⋂ φ ∈ l, φ.letterlessSpectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (a ⋏ ⋀l).letterlessSpectrum = ⋂ φ, ⋂ (_ : φ ∈ a :: l), φ.letterlessSpectrum by
      convert this;
      exact List.conj₂_cons_nonempty he;
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_lconj' {l : List β} {Φ : β → Formula ℕ} (h : (l.conj' Φ).Letterless) : (l.conj' Φ).letterlessSpectrum = ⋂ i ∈ l, (Φ i).letterlessSpectrum := by
  induction l using List.induction_with_singleton with
  | hcons a l he ih =>
    suffices (Φ a ⋏ (List.conj' Φ l)).letterlessSpectrum = ⋂ i, ⋂ (_ : i ∈ a :: l), (Φ i).letterlessSpectrum by
      convert this;
      exact List.conj₂_cons_nonempty (a := Φ a) (as := List.map Φ l) (by simpa);
    rw [def_and];
    simp [ih (by grind)];
  | _ => simp;

lemma def_fconj {s : Finset (Formula _)} (h : (s.conj).Letterless) : (s.conj.letterlessSpectrum) = ⋂ φ ∈ s, φ.letterlessSpectrum := by
  unfold Finset.conj;
  rw [def_lconj₂];
  . simp;
  . simpa;

lemma def_fconj' {s} {Φ : α → Formula ℕ} (hΦ : ((⩕ i ∈ s, Φ i)).Letterless) : (⩕ i ∈ s, Φ i).letterlessSpectrum = ⋂ i ∈ s, (Φ i).letterlessSpectrum (by apply letterless_fconj'.mp hΦ _; assumption;) := by
  unfold Finset.conj';
  rw [def_lconj'];
  . simp;
  . simpa;

end Formula.letterlessSpectrum


/-- letterlessTrace for letterless formula -/
@[grind] def Formula.letterlessTrace (φ : Formula ℕ) (φ_closed : φ.Letterless := by grind) := (φ.letterlessSpectrum)ᶜ

namespace Formula.letterlessTrace

variable {φ ψ : Formula ℕ} {hφ : φ.Letterless} {hψ : ψ.Letterless}

@[simp, grind =] lemma def_top : (⊤ : Formula _).letterlessTrace = ∅ := by grind;
@[simp, grind =] lemma def_bot : (⊥ : Formula _).letterlessTrace = Set.univ := by grind;
@[grind =] lemma def_neg : (∼φ).letterlessTrace = φ.letterlessTraceᶜ := by grind;
@[grind =] lemma def_and : (φ ⋏ ψ).letterlessTrace = φ.letterlessTrace ∪ ψ.letterlessTrace := by grind;
@[grind =] lemma def_or  : (φ ⋎ ψ).letterlessTrace = φ.letterlessTrace ∩ ψ.letterlessTrace := by grind;

end Formula.letterlessTrace


namespace Formula

@[grind =] lemma neg_letterlessTrace_letterlessSpectrum {φ : Formula ℕ} {hφ : φ.Letterless} : (∼φ).letterlessTrace = φ.letterlessSpectrum := by grind;
@[grind =] lemma neg_letterlessSpectrum_letterlessTrace {φ : Formula ℕ} {hφ : φ.Letterless} : (∼φ).letterlessSpectrum = φ.letterlessTrace := by grind;


lemma letterlessSpectrum_finite_or_cofinite {φ : Formula ℕ} (hφ : φ.Letterless) : φ.letterlessSpectrum.Finite ∨ φ.letterlessSpectrum.Cofinite := by
  induction φ with
  | hfalsum => simp;
  | hatom => grind;
  | himp φ ψ ihφ ihψ =>
    rw [letterlessSpectrum.def_imp];
    . rcases ihφ (by grind) with (ihφ | ihφ) <;>
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

-- variable (Xll : X.Letterless := by grind) (Yll : Y.Letterless := by grind)

lemma def_letterlessTrace_union (hX) : X.letterlessTrace hX = ⋃ φ ∈ X, φ.letterlessTrace := by simp [FormulaSet.letterlessTrace, FormulaSet.letterlessSpectrum, Formula.letterlessTrace]

lemma comp_letterlessTrace_letterlessSpectrum (hX) : (X.letterlessTrace hX)ᶜ = X.letterlessSpectrum := by simp [FormulaSet.letterlessTrace]

lemma iff_subset_letterlessSpectrum_subset_letterlessTrace (hX hY) : X.letterlessSpectrum hX ⊆ Y.letterlessSpectrum hY ↔ Y.letterlessTrace ⊆ X.letterlessTrace := by simp [FormulaSet.letterlessTrace]

lemma iff_eq_letterlessSpectrum_eq_letterlessTrace (hX hY)  : X.letterlessSpectrum hX = Y.letterlessSpectrum hY ↔ X.letterlessTrace = Y.letterlessTrace := by simp [FormulaSet.letterlessTrace];

end FormulaSet

/-- boxbot instance of axiomT -/
abbrev TBB (n : ℕ) : Formula ℕ := □^[(n + 1)]⊥ ➝ □^[n]⊥

section

variable {α α₁ α₂ β β₁ β₂ : Set ℕ} {hβ : β.Cofinite} {hβ₁ : β₁.Cofinite} {hβ₂ : β₂.Cofinite}

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

@[simp, grind .]
lemma TBB_conj'_letterless : (⩕ n ∈ s, TBB n).Letterless := by
  apply Formula.letterless_fconj'.mpr;
  grind;

@[simp, grind .]
lemma TBBSet_letterless : FormulaSet.Letterless (TBB '' α) := by simp [FormulaSet.Letterless]

@[simp]
lemma TBBSet_letterlessTrace : FormulaSet.letterlessTrace (TBB '' α) = α := by
  simp [FormulaSet.def_letterlessTrace_union];

@[simp, grind .]
lemma TBBMinus_letterless' : Formula.Letterless (∼⩕ n ∈ hβ.toFinset, TBB n) := by
  apply Formula.letterless_neg.mpr;
  apply Formula.letterless_fconj'.mpr;
  grind;

@[simp, grind .]
lemma TBBMinus_letterless : FormulaSet.Letterless {∼⩕ n ∈ hβ.toFinset, TBB n} := by simp [FormulaSet.Letterless];

@[simp, grind .]
lemma TBBMinus_letterlessSpectrum' : (∼⩕ n ∈ hβ.toFinset, TBB n).letterlessSpectrum TBBMinus_letterless' = βᶜ := by
  simp only [Formula.letterlessSpectrum.def_neg, compl_inj_iff];
  rw [Formula.letterlessSpectrum.def_fconj' ?_];
  . ext j;
    suffices (∀ i ∉ β, j ≠ i) ↔ j ∈ β by simpa [TBB_letterlessSpectrum];
    grind;
  . apply Formula.letterless_fconj'.mpr
    grind;

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
    apply not_imp_not.mpr $ Provability.sound_on;
    apply iIncon_unprovable_of_sigma1_sound;
  apply this;
  exact h;

@[simp, grind .]
lemma TBB_conj'_regular : (⩕ n ∈ s, TBB n).Regular T := by
  apply Formula.Regular.def_fconj'.mpr;
  grind;

@[simp high]
lemma TBBSet_regular : FormulaSet.Regular T (TBB '' α) := by
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

variable {F : Frame} [F.IsPointRooted] [Fintype F]

lemma iff_satisfies_mem_rank_letterlessSpectrum
  {M : Model} [Fintype M] [M.IsIrreflexive] [M.IsTransitive] [M.IsPointRooted] {w : M}
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
  {M : Model} [Fintype M] [M.IsIrreflexive] [M.IsTransitive] [M.IsPointRooted] {w : M} {n : ℕ}
  : w ⊧ TBB n ↔ Frame.rank w ≠ n := by
  apply Iff.trans iff_satisfies_mem_rank_letterlessSpectrum;
  simp;

abbrev Frame.finiteLinear (n : ℕ) : Kripke.Frame where
  World := Fin (n + 1)
  Rel := (· < ·)

namespace Frame.finiteLinear

abbrev of (i : Fin (n + 1)) : Frame.finiteLinear n := i

instance : (Frame.finiteLinear n) |>.IsPointRooted where
  default := ⟨of 0, by grind⟩
  uniq {r} := by
    by_contra! hC;
    have := r.2 0 (by grind);
    grind;

instance : (Frame.finiteLinear n) |>.IsIrreflexive where
  irrefl := by simp [Frame.finiteLinear]

instance : (Frame.finiteLinear n) |>.IsTransitive where
  trans := by simp [Frame.finiteLinear]; grind;

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

@[simp] lemma rank_zero : (Frame.finiteLinear n).height = n := by simpa using rank_of_eq_sub _

end Frame.finiteLinear

lemma letterlessSpectrum_TFAE (_ : φ.Letterless) : [
  n ∈ φ.letterlessSpectrum,
  ∀ M : Model, [Fintype M] → [M.IsIrreflexive] → [M.IsTransitive] → [M.IsPointRooted] → ∀ w : M.World, Frame.rank w = n → w ⊧ φ,
  ∃ M : Model, ∃ _ : Fintype M, ∃ _ : M.IsIrreflexive, ∃ _ : M.IsTransitive, ∃ _ : M.IsPointRooted, ∃ w : M.World, Frame.rank w = n ∧ w ⊧ φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h M _ _ _ _ w hw;
    apply iff_satisfies_mem_rank_letterlessSpectrum (by grind) |>.mpr;
    apply hw ▸ h;
  tfae_have 2 → 3 := by
    intro h;
    let M : Kripke.Model := ⟨Frame.finiteLinear n, λ p i => True⟩;
    use ⟨Frame.finiteLinear n, λ p i => True⟩;
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩;
    . use M.root;
      constructor;
      . exact Frame.finiteLinear.rank_zero;
      . apply h;
        exact Frame.finiteLinear.rank_zero;
  tfae_have 3 → 1 := by
    rintro ⟨M, _, _, _, _, w, rfl, hw⟩;
    apply iff_satisfies_mem_rank_letterlessSpectrum (by grind) |>.mp hw;
  tfae_finish;

end Kripke

section

open Formula
open LO.Entailment Modal.Entailment

variable {φ ψ : Formula ℕ} (hφ : φ.Letterless) (hψ : ψ.Letterless)

lemma iff_GL_provable_letterlessSpectrum_Univ : Modal.GL ⊢ φ ↔ φ.letterlessSpectrum = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  constructor;
  . intro h n;
    apply Kripke.letterlessSpectrum_TFAE (φ := φ) (by grind) |>.out 1 0 |>.mp;
    intro M _ _ _ _ _ w;
    have := GL.Kripke.fintype_completeness_TFAE.out 0 1 |>.mp h;
    apply @this M.toFrame;
  . intro h;
    apply GL.Kripke.fintype_completeness_TFAE.out 1 0 |>.mp;
    intro M _ _ _ _ V x;
    have := Kripke.letterlessSpectrum_TFAE (φ := φ) (n := Kripke.Frame.rank x) (by grind) |>.out 0 1 |>.mp;
    apply this (by grind) _ x rfl;

lemma iff_GL_provable_C_subset_letterlessSpectrum : Modal.GL ⊢ (φ ➝ ψ) ↔ φ.letterlessSpectrum hφ ⊆ ψ.letterlessSpectrum hψ := by
  apply Iff.trans $ iff_GL_provable_letterlessSpectrum_Univ (show (φ ➝ ψ).Letterless by grind);
  rw [Formula.letterlessSpectrum.def_imp];
  suffices (∀ i, i ∉ φ.letterlessSpectrum ∨ i ∈ ψ.letterlessSpectrum) ↔ φ.letterlessSpectrum ⊆ ψ.letterlessSpectrum by
    simpa [Set.eq_univ_iff_forall];
  constructor <;>
  . intro h i;
    have := @h i;
    tauto;

lemma iff_GL_provable_E_eq_letterlessSpectrum : Modal.GL ⊢ (φ ⭤ ψ) ↔ φ.letterlessSpectrum = ψ.letterlessSpectrum := by
  rw [
    Set.Subset.antisymm_iff,
    ←iff_GL_provable_C_subset_letterlessSpectrum,
    ←iff_GL_provable_C_subset_letterlessSpectrum,
  ];
  constructor;
  . intro h; constructor <;> cl_prover [h];
  . rintro ⟨h₁, h₂⟩; cl_prover [h₁, h₂];

lemma GL_letterlessTrace_TBB_normalization (h : φ.letterlessTrace.Finite) : Modal.GL ⊢ φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_letterlessSpectrum _ _ |>.mpr;
  . calc
      _ = ⋂ i ∈ φ.letterlessTrace, (TBB i).letterlessSpectrum := by
        have : φ.letterlessTrace = ⋃ i ∈ φ.letterlessTrace, (TBB i).letterlessTrace := by ext i; simp [TBB_letterlessTrace];
        simpa [Formula.letterlessTrace] using compl_inj_iff.mpr this;
      _ = _ := by
        ext i;
        rw [Formula.letterlessSpectrum.def_fconj' (by simp)];
        simp;
  . show φ.Letterless;
    assumption;
  . show (⩕ n ∈ h.toFinset, TBB n).Letterless;
    grind;

lemma GL_letterlessSpectrum_TBB_normalization (h : φ.letterlessSpectrum.Finite) : Modal.GL ⊢ φ ⭤ ∼(⩕ n ∈ h.toFinset, (TBB n)) := by
  have h' : (∼φ).letterlessTrace.Finite := by grind;
  have := GL_letterlessTrace_TBB_normalization (show (∼φ).Letterless by grind) h';
  rw [show h.toFinset = h'.toFinset by grind];
  cl_prover [this];

lemma GL_proves_letterless_axiomWeakPoint3 (hφ : φ.Letterless) (hψ : ψ.Letterless) : Modal.GL ⊢ (Axioms.WeakPoint3 φ ψ) := by
  apply iff_GL_provable_letterlessSpectrum_Univ (by grind) |>.mpr;
  apply Set.eq_univ_iff_forall.mpr;
  intro n;
  rw [
    letterlessSpectrum.def_or,
    letterlessSpectrum.def_box,
    letterlessSpectrum.def_box,
    letterlessSpectrum.def_imp,
    letterlessSpectrum.def_imp,
    letterlessSpectrum.def_boxdot,
    letterlessSpectrum.def_boxdot
  ];
  grind;

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
  (hφ : φ.Letterless) (hψ : ψ.Letterless)
  (X_letterless : X.Letterless) (Y_letterless : Y.Letterless)

lemma letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] (hφ : φ.Letterless)
  : Modal.GL ⊢ φ ↔ T ⊢ T.LetterlessStandardRealization φ := by
  apply Iff.trans (GL.arithmetical_completeness_sound_iff (T := T) |>.symm);
  constructor;
  . intro h;
    apply h;
  . intro h f;
    have e : T.LetterlessStandardRealization φ = f φ := Realization.letterless_interpret hφ
    exact e ▸ h;

lemma iff_regular_of_provable_E [𝗜𝚺₁ ⪯ T] (hφ : φ.Letterless) (hψ : ψ.Letterless) (h : Modal.GL ⊢ φ ⭤ ψ)
  : φ.Regular T ↔ ψ.Regular T := by
  have : T ⊢ T.LetterlessStandardRealization (φ ⭤ ψ) := letterless_arithmetical_completeness (by grind) |>.mp h;
  have : ℕ ⊧ₘ T.LetterlessStandardRealization (φ ⭤ ψ) := ArithmeticTheory.SoundOn.sound (F := λ _ => True) this (by simp);
  simp [Realization.interpret, Formula.Regular] at this ⊢;
  tauto;

lemma iff_singular_of_provable_E [𝗜𝚺₁ ⪯ T] (hφ : φ.Letterless) (hψ : ψ.Letterless) (h : Modal.GL ⊢ φ ⭤ ψ)
  : φ.Singular T ↔ ψ.Singular T := Iff.not $ iff_regular_of_provable_E hφ hψ h


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
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, (Finset.conj Y).letterlessSpectrum ⊆ φ.letterlessSpectrum := by
      constructor;
      . rintro ⟨Y, _, hY₂⟩;
        use Y;
        constructor;
        . apply iff_GL_provable_C_subset_letterlessSpectrum (by grind) (by grind) |>.mp hY₂;
        . assumption;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . assumption;
        . apply iff_GL_provable_C_subset_letterlessSpectrum (by grind) (by grind) |>.mpr hY₂;
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
          have f_conj_letterless : ∀ i, (f i).conj.Letterless := λ i => Formula.letterless_fconj.mpr $ λ ξ hξ => X_letterless _ $ fX _ hξ;

          let sf := λ i => ⋂ ξ, ⋂ (h : ξ ∈ f i), ξ.letterlessSpectrum (X_letterless ξ $ fX _ $ by assumption);
          have sf_eq : ∀ i, sf i = Formula.letterlessSpectrum ((f i).conj) (f_conj_letterless _) := by
            intro i;
            rw [Formula.letterlessSpectrum.def_fconj (f_conj_letterless i)];
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
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ Y.letterlessTrace ⊆ X.letterlessTrace := by
  apply Iff.trans (iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum X_letterless Y_letterless hSR);
  apply FormulaSet.iff_subset_letterlessSpectrum_subset_letterlessTrace;

lemma GL.iff_eq_closed_sumQuasiNormal_eq_letterlessSpectrum (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.letterlessSpectrum = Y.letterlessSpectrum := by
  simp only [Set.Subset.antisymm_iff];
  rw [
    iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum X_letterless Y_letterless (by tauto),
    iff_subset_closed_sumQuasiNormal_subset_letterlessSpectrum Y_letterless X_letterless (by tauto)
  ];
  tauto;



protected abbrev GLα (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (TBB '' α)

protected abbrev GLαω : Logic ℕ := Modal.GLα Set.univ

protected abbrev GLβMinus (β : Set ℕ) (hβ : β.Cofinite := by grind) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}


lemma GL.iff_eq_closed_sumQuasiNormal_eq_letterlessTrace (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.letterlessTrace = Y.letterlessTrace := by
  apply Iff.trans (iff_eq_closed_sumQuasiNormal_eq_letterlessSpectrum X_letterless Y_letterless hXY);
  apply FormulaSet.iff_eq_letterlessSpectrum_eq_letterlessTrace;

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
  have := FormulaSet.comp_letterlessTrace_letterlessSpectrum (hX := X_letterless);
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
    _ ↔ FormulaSet.letterlessTrace (α₁.image TBB) ⊆ FormulaSet.letterlessTrace (α₂.image TBB) := by
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


namespace FirstOrder.Theory

open LO.Entailment

variable
  {L : Language} [L.DecidableEq]
  {T U : Theory L} [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
  {φ : Sentence L}

lemma compact_add_right (h : (T + U) ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ U }), T ⊢ s.1.conj ➝ φ := by
  obtain ⟨⟨s, hsTU⟩, hs⟩ := Theory.compact' h;
  let sT := { ψ ∈ s | ψ ∈ T };
  let sU := { ψ ∈ s | ψ ∈ U };

  use ⟨sU, λ _ => by simp [sU]⟩;

  have : (∅ : Theory _) ⊢ sT.conj ➝ sU.conj ➝ φ := CK!_iff_CC!.mp $ C!_trans CKFconjFconjUnion! $ by
    have : sT ∪ sU = s:= by
      ext ψ;
      constructor;
      . grind;
      . intro hψ; rcases hsTU hψ with (hψT | hψU) <;> grind;
    rwa [this];
  apply Entailment.mdp! $ Axiomatized.weakening! (λ _ => by simp) this;
  apply Entailment.FConj!_iff_forall_provable.mpr;
  intro ψ hψ;
  apply Axiomatized.provable_axm;
  grind;

lemma compact_add_left (h : (T + U) ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T }), U ⊢ s.1.conj ➝ φ := by
  rw [show (T + U = U + T) by simp [add_def, Set.union_comm]] at h
  simpa using compact_add_right h;

end FirstOrder.Theory



namespace ProvabilityLogic

open LO.Entailment
open FirstOrder.ArithmeticTheory
open Classical

lemma _root_.finite_preimage_choice (s : Finset α) (X : Set β) (f : β → α) (hs : ∀ a ∈ s, ∃ b ∈ X, f b = a) :
  ∃ t : Finset β, ↑t ⊆ X ∧ ∀ a ∈ s, ∃ b ∈ t, f b = a := by
  classical
  choose g hga hgb using hs;
  use Finset.univ.image (λ (a : { b // b ∈ s}) => g a.1 (by simp));
  constructor;
  . intro b hb;
    grind;
  . intro h b;
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, ↓existsAndEq];
    grind;

theorem letterless_provabilityLogic
  {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [T.Δ₁] [ℕ ⊧ₘ* T]
  (X : Modal.FormulaSet ℕ) (X_letterless : X.Letterless) :
  (Modal.GL.sumQuasiNormal X).IsProvabilityLogic T (T + (T.LetterlessStandardRealization '' X)) := by
  intro A;
  rw [
    (show T.LetterlessStandardRealization '' X = (GL.uniformStandardRealization T) '' X by ext φ; grind [Realization.letterless_interpret]),
    Modal.Logic.sumQuasiNormal.iff_provable_finite_provable_letterless X_letterless
  ];

  constructor;
  . rintro ⟨Γ, hΓ₁, hΓ₂⟩ f;
    have H : T ⊢ (f Γ.conj) ➝ (f A) := GL.arithmetical_soundness hΓ₂;
    rw [
      show f Γ.conj = (GL.uniformStandardRealization T) Γ.conj from
        Realization.letterless_interpret $ Modal.Formula.letterless_fconj.mpr λ B hB ↦ X_letterless B $ hΓ₁ hB
    ] at H;
    apply Entailment.mdp! $ WeakerThan.pbl H;
    apply Realization.interpret.iff_provable_fconj.mpr;
    intro B hB;
    apply Axiomatized.provable_axm;
    right;
    use B;
    tauto;
  . intro h;
    obtain ⟨Γ, hΓX, H⟩ :
      ∃ Γ : Finset (Modal.Formula ℕ), ↑Γ ⊆ X ∧ T ⊢ (Γ.image (GL.uniformStandardRealization T)).conj ➝ (GL.uniformStandardRealization T) A := by
      obtain ⟨⟨s, hs₁⟩, hs₂⟩ := Theory.compact_add_right $ h (GL.uniformStandardRealization T);
      obtain ⟨t, ht₁, ht₂⟩ := finite_preimage_choice s X (GL.uniformStandardRealization T) hs₁;
      use t;
      constructor;
      . assumption;
      . apply Entailment.C!_trans ?_ hs₂;
        apply Entailment.CFConj_FConj!_of_subset;
        intro φ hφ;
        obtain ⟨B, hB, rfl⟩ := ht₂ _ hφ;
        grind;
    use Γ;
    constructor;
    . assumption;
    . apply GL.uniformStandardRealization_spec (T := T) |>.mp;
      apply C!_trans ?_ H;
      exact C_of_E_mp! $ Realization.interpret.iff_provable_fconj_inside (f := GL.uniformStandardRealization T);

end ProvabilityLogic

@[simp, grind .]
lemma Modal.GLα.isProvabilityLogic {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [T.Δ₁] [ℕ ⊧ₘ* T] {α : Set ℕ}
  : (Modal.GLα α).IsProvabilityLogic T (T + ((T.LetterlessStandardRealization ∘ Modal.TBB) '' α)) := by
  suffices (T.LetterlessStandardRealization ∘ Modal.TBB) '' α = T.LetterlessStandardRealization '' (Modal.TBB '' α) by
    rw [this];
    apply letterless_provabilityLogic;
    simp;
  ext i;
  simp;

@[simp, grind .]
lemma Modal.GLαω.isProvabilityLogic {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [T.Δ₁] [ℕ ⊧ₘ* T]
  : Modal.GLαω.IsProvabilityLogic T (T + ((T.LetterlessStandardRealization ∘ Modal.TBB) '' Set.univ)) := by
  apply Modal.GLα.isProvabilityLogic;

/-
-- TODO: probably not use.
lemma Modal.GLβMinus.isProvabilityLogic {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [T.Δ₁] [ℕ ⊧ₘ* T] {β : Set ℕ} (hβ : β.Cofinite)
  : (Modal.GLβMinus β).IsProvabilityLogic T (T + { ∼⩕ n ∈ hβ.toFinset, T.LetterlessStandardRealization $ Modal.TBB n }) := by sorry;
-/

end LO

end
