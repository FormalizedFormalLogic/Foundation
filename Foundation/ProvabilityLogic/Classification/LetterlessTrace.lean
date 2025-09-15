import Foundation.Modal.Formula
import Foundation.Modal.Axioms
import Foundation.ProvabilityLogic.SolovaySentences
import Foundation.ProvabilityLogic.S.Completeness
import Foundation.Modal.Logic.S.Basic
import Foundation.Modal.Logic.D.Basic
import Mathlib.Tactic.TFAE
import Foundation.Propositional.Logic.PostComplete
import Mathlib.Order.WellFounded

section

lemma Set.compl_inj_iff {a b : Set α} : aᶜ = bᶜ ↔ a = b := _root_.compl_inj_iff

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539292838
-/
lemma Set.infinitely_finset_approximate {α : Type*} {X : Set α} (count : X.Countable) (inf : X.Infinite) {a : α} (ha : a ∈ X) :
  ∃ f : ℕ → Finset α, ((f 0) = {a}) ∧ (∀ i, f i ⊂ f (i + 1)) ∧ (∀ i, ↑(f i) ⊆ X) ∧ (∀ b ∈ X, ∃ i, b ∈ f i) := by
  let X' := X \ {a}
  have count' : Countable X' := (count.mono Set.diff_subset).to_subtype
  have inf' : Infinite X' := (inf.diff (Set.finite_singleton a)).to_subtype
  obtain ⟨eq⟩ : Nonempty (Nat ≃ X') := nonempty_equiv_of_countable
  refine ⟨
    fun n => Finset.cons a ((Finset.range n).map
    (eq.toEmbedding.trans (Function.Embedding.subtype _))) ?_, ?_, ?_, ?_, ?_
  ⟩
  · suffices ∀ x < n, ¬↑(eq x) = a by simpa;
    intro x _
    exact (eq x).prop.right
  · rfl
  · simp [Finset.ssubset_def]
  · suffices ∀ (i : ℕ), Set.Iio i ⊆ (fun a ↦ ↑(eq a)) ⁻¹' X by simpa [Set.insert_subset_iff, ha]
    intro i x _;
    exact (eq x).prop.left
  · intro b hb
    by_cases hba : b = a
    · exact ⟨0, by simp [hba]⟩
    · refine ⟨eq.symm ⟨b, hb, hba⟩ + 1, ?_⟩
      apply Finset.mem_cons_of_mem;
      suffices ∃ a_1 < eq.symm ⟨b, _⟩ + 1, ↑(eq _) = b by simpa;
      exact ⟨eq.symm ⟨b, hb, hba⟩, by simp⟩

end


section

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539367015
-/
lemma Finset.no_ssubset_descending_chain  {f : ℕ → Finset α} : ¬(∀ i, ∃ j > i, f j ⊂ f i) := by
  intro h
  have n := 0
  induction hf : f n using WellFoundedLT.fix generalizing n with subst hf | _ _ ih
  obtain ⟨m, -, hy⟩ := h n
  exact ih (f m) hy m rfl

end



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

namespace Modal

namespace Formula


@[simp, grind]
lemma subst.subst_letterless {φ : Formula α} {s : Substitution α} (hφ : φ.letterless) : φ⟦s⟧ = φ := by
  induction φ <;> simp_all [letterless];


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
abbrev _root_.LO.FirstOrder.ArithmeticTheory.letterlessStandardRealization (T : ArithmeticTheory) [T.Δ₁] : T.StandardRealization := ⟨λ _ => ⊤⟩


@[grind] def Regular (T : ArithmeticTheory) [T.Δ₁] (φ : Modal.Formula ℕ) := ℕ ⊧ₘ₀ (T.letterlessStandardRealization φ)

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
  | hcons _ _ _ ih => simp_all [Regular];
  | _ => simp;

@[simp, grind]
lemma def_lconj' {l : List _} {Φ : β → Formula _} : (l.conj' Φ).Regular T ↔ ∀ i ∈ l, ((Φ i).Regular T) := by
  induction l using List.induction_with_singleton' with
  | hcons _ _ _ ih => simp_all [Regular];
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

section

variable {α α₁ α₂ β β₁ β₂ : Set ℕ} (hβ : βᶜ.Finite := by grind) (hβ₁ : β₁ᶜ.Finite := by grind) (hβ₂ : β₂ᶜ.Finite := by grind)

@[simp, grind] lemma TBB_letterless : (TBB n).letterless := by grind

@[simp]
lemma TBB_spectrum : (TBB n).spectrum = {n}ᶜ := by
  rw [Formula.spectrum.def_imp, boxbot_spectrum, boxbot_spectrum];
  ext i;
  simp;
  omega;

@[simp]
lemma TBB_trace : (TBB n).trace = {n} := by simp [Formula.trace, TBB_spectrum, compl_compl];
variable {α α₁ α₂ β β₁ β₂ : Set ℕ} (hβ : βᶜ.Finite := by grind) (hβ₁ : β₁ᶜ.Finite := by grind) (hβ₂ : β₂ᶜ.Finite := by grind)

@[simp, grind]
lemma TBB_conj'_letterless : (⩕ n ∈ s, TBB n).letterless := by
  apply Formula.letterless.of_fconj';
  grind;

@[simp, grind]
lemma TBBSet_letterless : FormulaSet.letterless ((λ i => TBB i) '' α) := by simp [FormulaSet.letterless]

@[simp]
lemma TBBSet_trace : FormulaSet.trace (α.image (λ i => TBB i)) = α := by
  ext i;
  rw [FormulaSet.def_trace_union];
  simp [TBB_trace];

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

@[simp]
lemma TBBMinus_spectrum : FormulaSet.spectrum {(∼⩕ n ∈ hβ.toFinset, TBB n)} = βᶜ := by simp [FormulaSet.spectrum]


section

variable [ℕ ⊧ₘ* T]

@[simp, grind]
lemma TBB_regular : (TBB n).Regular T := by
  apply Formula.Regular.def_imp.mpr;
  intro h;
  exfalso;
  have : ¬ℕ ⊧ₘ₀ T.letterlessStandardRealization (□^[(n + 1)]⊥) := by
    simp only [Box.multibox_succ, Realization.interpret.def_box, Realization.interpret.def_boxItr, Realization.interpret.def_bot];
    apply Provability.SoundOnModel.sound.not.mpr;
    apply Provability.iIncon_unprovable_of_sigma1_sound;
  apply this;
  exact h;

@[simp, grind]
lemma TBB_conj'_regular : (⩕ n ∈ s, TBB n).Regular T := by
  apply Formula.Regular.def_fconj'.mpr;
  grind;

@[simp] lemma TBBSet_regular : FormulaSet.Regular T ((fun i ↦ TBB i) '' α) := by simp [FormulaSet.Regular];

@[simp]
lemma TBBMinus_singular : FormulaSet.Singular T {∼⩕ n ∈ hβ.toFinset, TBB n} := by
  simp [FormulaSet.Singular, FormulaSet.Regular, Formula.Regular.def_neg];

end

end


namespace Kripke

open Kripke
open Formula.Kripke

variable {F : Frame} {r : F} [F.IsTree r] [Fintype F]

lemma Frame.World.finHeight_lt_of_rel {i j : F} (hij : i ≺ j) : Frame.World.finHeight i > Frame.World.finHeight j := fcwHeight_gt_of hij

lemma Frame.World.exists_of_lt_finHeight {i : F} (hn : n < Frame.World.finHeight i) : ∃ j : F, i ≺ j ∧ Frame.World.finHeight j = n := fcwHeight_lt hn

lemma iff_satisfies_mem_finHeight_spectrum
  {M : Model} {r : M} [Fintype M] [M.IsTree r] {w : M}
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


abbrev Frame.finiteLinear (n : ℕ) : Kripke.Frame where
  World := Fin (n + 1)
  Rel := (· < ·)

namespace Frame.finiteLinear

abbrev of (i : Fin (n + 1)) : Frame.finiteLinear n := i

instance : (Frame.finiteLinear n) |>.IsFiniteTree 0 where
  asymm := by apply Fin.lt_asymm;
  root_generates := by simp [Frame.finiteLinear, Fin.pos_iff_ne_zero]

lemma eq_height (i : Fin (n + 1)) : Frame.World.finHeight (of i) = n - i := by {
  induction i using Fin.reverseInduction
  case last =>
    suffices World.finHeight (of (Fin.last n)) = 0 by simpa
    apply fcwHeight_eq_zero_iff.mpr
    intro j
    show ¬(Fin.last n) < j
    simp [Fin.le_last]
  case cast i ih =>



}


/--/
lemma eq_height_0 : Frame.World.finHeight (0 : Frame.finiteLinear n) = n := by
  dsimp [Frame.World.finHeight];
  sorry;

end Frame.finiteLinear



lemma spectrum_TFAE (_ : φ.letterless) : [
  n ∈ φ.spectrum,
  ∀ M : Model, ∀ r, [M.IsTree r] → [Fintype M] → ∀ w : M.World, Frame.World.finHeight w = n → w ⊧ φ,
  ∃ M : Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M.World, Frame.World.finHeight w = n ∧ w ⊧ φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h M r _ _ w hw;
    apply iff_satisfies_mem_finHeight_spectrum (by grind) |>.mpr;
    apply hw ▸ h;
  tfae_have 2 → 3 := by
    intro h;
    refine ⟨⟨Frame.finiteLinear n, λ p i => True⟩, 0, inferInstance, inferInstance, ⟨0, ?_, ?_⟩⟩;
    . simp;
    . apply h; simp;
  tfae_have 3 → 1 := by
    rintro ⟨M, r, _, _, w, rfl, hw⟩;
    apply iff_satisfies_mem_finHeight_spectrum (by grind) |>.mp hw;
  tfae_finish;

end Kripke

section

open Formula
open LO.Entailment Modal.Entailment

variable {φ ψ : Formula ℕ} (φ_letterless : φ.letterless) (ψ_letterless : ψ.letterless)

lemma iff_GL_provable_spectrum_Univ
  : Modal.GL ⊢! φ ↔ φ.spectrum = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  constructor;
  . intro h n;
    apply Kripke.spectrum_TFAE (φ := φ) (by grind) |>.out 1 0 |>.mp;
    intro M r _ _ w _;
    have := GL.Kripke.tree_completeness_TFAE.out 0 2 |>.mp h;
    apply @this M.toFrame r $ by constructor;
  . intro h;
    apply GL.Kripke.tree_completeness_TFAE.out 2 0 |>.mp;
    intro F r _ V w;
    have : Fintype (⟨F, V⟩ : Kripke.Model).World := Fintype.ofFinite _
    have := Kripke.spectrum_TFAE (φ := φ) (n := Kripke.Frame.World.finHeight w) (by grind) |>.out 0 1 |>.mp;
    apply this (by grind) _ r w rfl;

lemma iff_GL_provable_C_subset_spectrum : Modal.GL ⊢! (φ ➝ ψ) ↔ φ.spectrum ⊆ ψ.spectrum := by
  apply Iff.trans $ iff_GL_provable_spectrum_Univ (by grind);
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
    ←iff_GL_provable_C_subset_spectrum φ_letterless ψ_letterless,
    ←iff_GL_provable_C_subset_spectrum ψ_letterless φ_letterless,
  ];
  constructor;
  . intro h; constructor <;> cl_prover [h];
  . rintro ⟨h₁, h₂⟩; cl_prover [h₁, h₂];

lemma GL_trace_TBB_normalization (h : φ.trace.Finite) : Modal.GL ⊢! φ ⭤ (⩕ n ∈ h.toFinset, (TBB n)) := by
  apply iff_GL_provable_E_eq_spectrum φ_letterless (letterless.of_fconj' (by simp)) |>.mpr;
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

lemma GL_proves_letterless_axiomWeakPoint3 (φ_letterless : φ.letterless) (ψ_letterless : ψ.letterless) : Modal.GL ⊢! (Axioms.WeakPoint3 φ ψ) := by
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
  (φ_letterless : φ.letterless) (ψ_letterless : ψ.letterless)
  (X_letterless : X.letterless) (Y_letterless : Y.letterless)

lemma letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.letterless)
  : Modal.GL ⊢! φ ↔ T ⊢!. T.letterlessStandardRealization φ := by
  apply Iff.trans (GL.arithmetical_completeness_sound_iff (T := T) |>.symm);
  constructor;
  . intro h;
    apply h;
  . intro h f;
    have e : T.letterlessStandardRealization φ = f φ := Realization.letterless_interpret φ_letterless
    exact e ▸ h;

lemma iff_regular_of_provable_E [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.letterless) (ψ_letterless : ψ.letterless) (h : Modal.GL ⊢! φ ⭤ ψ)
  : φ.Regular T ↔ ψ.Regular T := by
  have : T ⊢!. T.letterlessStandardRealization (φ ⭤ ψ) := letterless_arithmetical_completeness (by grind) |>.mp h;
  have : ℕ ⊧ₘ₀ T.letterlessStandardRealization (φ ⭤ ψ) := ArithmeticTheory.SoundOn.sound (F := λ _ => True) this (by simp);
  simp [Realization.interpret, Formula.Regular] at this ⊢;
  tauto;

lemma iff_singular_of_provable_E [𝗜𝚺₁ ⪯ T] (φ_letterless : φ.letterless) (ψ_letterless : ψ.letterless) (h : Modal.GL ⊢! φ ⭤ ψ)
  : φ.Singular T ↔ ψ.Singular T := Iff.not $ iff_regular_of_provable_E φ_letterless ψ_letterless h


variable [𝗜𝚺₁ ⪯ T]

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
  T ⊢!. T.letterlessStandardRealization φ,
  φ.spectrum = Set.univ,
].TFAE := by
  tfae_have 1 ↔ 2 := letterless_arithmetical_completeness (by grind)
  tfae_have 1 ↔ 3 := iff_GL_provable_spectrum_Univ (by grind)
  tfae_finish;

lemma FormulaSet.spectrum_finite_of_singular (X_singular : X.Singular T) : X.spectrum.Finite := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_singular_of_singular X_singular;
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

open Classical LO.Entailment in
lemma GL.iff_provable_closed_sumQuasiNormal_subset_spectrum (hSR : X.Singular T ∨ φ.Regular T)
  : Modal.GL.sumQuasiNormal X ⊢! φ ↔ X.spectrum ⊆ φ.spectrum := by
  calc
    _ ↔ ∃ Y, (∀ ψ ∈ Y, ψ ∈ X) ∧ Modal.GL ⊢! Finset.conj Y ➝ φ := Logic.sumQuasiNormal.iff_provable_finite_provable $ by
      rintro Y hY s ψ;
      suffices ∀ ξ ∈ Y, ξ⟦s⟧ = ψ → ψ ∈ X by simpa;
      rintro ξ hξ rfl;
      rw [Formula.subst.subst_letterless (X_letterless _ $ hY hξ)];
      apply hY;
      simpa;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, (Finset.conj Y).spectrum (Formula.letterless.of_fconj (by grind)) ⊆ φ.spectrum := by
      constructor;
      . rintro ⟨Y, _, hY₂⟩;
        use Y;
        constructor;
        . apply iff_GL_provable_C_subset_spectrum (Formula.letterless.of_fconj (by grind)) (by grind) |>.mp hY₂;
        . assumption;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y;
        constructor;
        . assumption;
        . apply iff_GL_provable_C_subset_spectrum (Formula.letterless.of_fconj (by grind)) (by grind) |>.mpr hY₂;
    _ ↔ ∃ Y : Finset (Formula ℕ), ∃ _ : ∀ ψ ∈ Y, ψ ∈ X, ⋂ ψ ∈ Y, ψ.spectrum ⊆ φ.spectrum := by
      constructor;
      . rintro ⟨Y, hY₁, hY₂⟩;
        use Y, hY₁;
        suffices Y.conj.spectrum = ⋂ ψ ∈ Y, ψ.spectrum by simpa [this] using hY₂;
        rw [Formula.spectrum.def_fconj];
        grind;
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
          have f_conj_letterless : ∀ i, (f i).conj.letterless := λ i => Formula.letterless.of_fconj $ λ ξ hξ => X_letterless _ $ fX _ hξ;

          let sf := λ i => ⋂ ξ, ⋂ (h : ξ ∈ f i), ξ.spectrum (X_letterless ξ $ fX _ $ by assumption);
          have sf_eq : ∀ i, sf i = Formula.spectrum ((f i).conj) (f_conj_letterless _) := by
            intro i;
            rw [Formula.spectrum.def_fconj (λ ξ hξ => X_letterless _ $ fX _ hξ)];
          have sf_monotone : ∀ i, sf (i + 1) ⊆ sf i := by
            intro i;
            rw [sf_eq (i + 1), sf_eq i];
            apply iff_GL_provable_C_subset_spectrum (f_conj_letterless _) (f_conj_letterless _) |>.mp;
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

          have sf0_eq : sf 0 = ψ.spectrum := by simp [sf, f0];
          have sf0_finite : (sf 0).Finite := by rw [sf0_eq]; exact Formula.spectrum_finite_of_singular (by grind) ψ_singular;
          have sf_finite : ∀ i, (sf i).Finite := by
            intro i;
            apply Set.Finite.subset sf0_finite;
            apply sf_monotone _ _ (by omega);

          have sf_X : ∀ i, sf i ⊇ X.spectrum := by
            intro i n;
            suffices (∀ (ξ : Formula ℕ) (_ : ξ ∈ X), n ∈ ξ.spectrum _) → ∀ (ξ : Formula ℕ) (_ : ξ ∈ f i), n ∈ ξ.spectrum _ by
              simpa [sf, FormulaSet.spectrum];
            intro h ξ hξ;
            apply h;
            apply fX i hξ;

          obtain ⟨k, hk⟩ : ∃ k, sf k = X.spectrum := by
            by_contra! hC;
            have : ∀ i, ∃ n, n ∈ sf i ∧ n ∉ X.spectrum := by
              intro i;
              exact Set.ssubset_iff_exists.mp (Set.ssubset_of_subset_ne (sf_X i) (hC i).symm) |>.2;

            apply Finset.no_ssubset_descending_chain (f := λ i => sf_finite i |>.toFinset);

            intro i;
            obtain ⟨n, hn₁, hn₂⟩ := this i;
            obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ, ∃ (_ : ξ ∈ X), n ∉ ξ.spectrum _ := by simpa [FormulaSet.spectrum] using hn₂;
            obtain ⟨j, hj⟩ := f_inv ξ hξ₁;

            have : i < j := by
              by_contra hC;
              have := Set.Subset.trans (sf_monotone j i (by omega)) $ show sf j ⊆ ξ.spectrum by
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
                . suffices ∃ χ, ∃ _ : χ ∈ f j, n ∉ χ.spectrum _ by simpa [sf];
                  use ξ;
                  simp_all;
              ⟩;

          use (f k)
          refine ⟨?_, ?_⟩;
          . apply fX;
          . apply Set.Subset.trans ?_ h;
            rw [←FormulaSet.spectrum, ←hk];
        . have H : ∀ i ∈ φ.trace, ∃ ψ, ∃ _ : ψ ∈ X, i ∈ ψ.trace := by
            have : φ.trace ⊆ ⋃ ψ ∈ X, ψ.trace := by
              apply Set.compl_subset_compl.mp;
              simpa [Formula.trace]
            simpa [Set.subset_def];

          let ξ := λ i (hi : i ∈ φ.trace) => (H i hi |>.choose);
          have ξ_in_X : ∀ {i hi}, (ξ i hi) ∈ X := by
            intro i hi;
            apply (H i hi |>.choose_spec).1;
          have ξ_letterless : ∀ {i hi}, (ξ i hi).letterless := by
            intro i hi;
            apply X_letterless _  $ ξ_in_X;
            assumption
          have H₂ : ⋂ i ∈ φ.trace, (ξ i (by assumption)).spectrum ⊆ φ.spectrum := by
            suffices φ.trace ⊆ ⋃ i ∈ φ.trace, (ξ i (by assumption)).trace by
              apply Set.compl_subset_compl.mp;
              simpa;
            intro j hj;
            simp only [Set.mem_iUnion, ξ];
            use j, hj;
            apply H j hj |>.choose_spec.2;
          use @Finset.univ (α := { i // i ∈ φ.trace }) ?_ |>.image (λ i => (ξ i.1 i.2));
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
          . apply Set.Finite.fintype (s := φ.trace);
            exact Formula.iff_regular_trace_finite (by grind) |>.mp φ_regular;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (hSR : X.Singular T ∨ Y.Regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ X.spectrum ⊆ Y.spectrum := by
  calc
    _ ↔ ∀ ψ ∈ Y, Modal.GL.sumQuasiNormal X ⊢! ψ := Logic.sumQuasiNormal.iff_subset
    _ ↔ ∀ ψ, (h : ψ ∈ Y) → X.spectrum ⊆ ψ.spectrum := by
      constructor;
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_spectrum (T := T) (by grind) (by grind) (by tauto) |>.mp;
        exact h ψ (by simpa);
      . intro h ψ _;
        apply GL.iff_provable_closed_sumQuasiNormal_subset_spectrum (T := T) (by grind) (by grind) (by tauto) |>.mpr;
        apply h;
        simpa;
    _ ↔ X.spectrum ⊆ (⋂ ψ ∈ Y, ψ.spectrum) := by simp;

lemma GL.iff_subset_closed_sumQuasiNormal_subset_trace (hSR : X.Singular T ∨ Y.Regular T)
  : Modal.GL.sumQuasiNormal Y ⊆ Modal.GL.sumQuasiNormal X ↔ Y.trace ⊆ X.trace :=
  Iff.trans (iff_subset_closed_sumQuasiNormal_subset_spectrum X_letterless Y_letterless hSR) FormulaSet.iff_subset_spectrum_subset_trace

lemma GL.iff_eq_closed_sumQuasiNormal_eq_spectrum (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.spectrum = Y.spectrum := by
  simp only [Set.Subset.antisymm_iff];
  rw [
    iff_subset_closed_sumQuasiNormal_subset_spectrum X_letterless Y_letterless (by tauto),
    iff_subset_closed_sumQuasiNormal_subset_spectrum Y_letterless X_letterless (by tauto)
  ];
  tauto;



protected abbrev GLα (α : Set ℕ) : Logic ℕ := Modal.GL.sumQuasiNormal (α.image (λ i => TBB i))

protected abbrev GLβMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) : Logic ℕ := Modal.GL.sumQuasiNormal {∼(⩕ n ∈ hβ.toFinset, (TBB n))}


lemma GL.iff_eq_closed_sumQuasiNormal_eq_trace (hXY : (X.Regular T ∧ Y.Regular T) ∨ (X.Singular T ∧ Y.Singular T))
  : Modal.GL.sumQuasiNormal X = Modal.GL.sumQuasiNormal Y ↔ X.trace = Y.trace :=
  Iff.trans (iff_eq_closed_sumQuasiNormal_eq_spectrum X_letterless Y_letterless hXY) FormulaSet.iff_eq_spectrum_eq_trace

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


@[grind]
lemma FormulaSet.comp_trace_finite_of_singular (X_singular : X.Singular T) : (X.trace)ᶜ.Finite :=
  FormulaSet.comp_trace_spectrum X_letterless ▸ FormulaSet.spectrum_finite_of_singular X_letterless X_singular


lemma GL.eq_closed_singular_sumQuasiNormal_GLβMinus (X_singular : X.Singular T) : Modal.GL.sumQuasiNormal X = Modal.GLβMinus (X.trace) := by
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
  either `Modal.GLα (X.trace)` (`X` is regular) or `Modal.GLβMinus (X.trace)` (`X` is singular)
-/
theorem GL.eq_closed_sumQuasiNormal_GLα_or_GLβMinus :
  (∃ _ : X.Regular T, Modal.GL.sumQuasiNormal X = Modal.GLα (X.trace)) ∨
  (∃ _ : X.Singular T, Modal.GL.sumQuasiNormal X = Modal.GLβMinus (X.trace)) := by
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
    _ ↔ FormulaSet.trace (α₁.image (λ i => TBB i)) ⊆ FormulaSet.trace (α₂.image (λ i => TBB i)) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_trace (T := 𝗣𝗔) (by grind) (by grind);
      simp;
    _ ↔ α₁ ⊆ α₂ := by simp;

lemma iff_GLβMinus_subset (hβ₁ : β₁ᶜ.Finite) (hβ₂ : β₂ᶜ.Finite) : Modal.GLβMinus β₁ ⊆ Modal.GLβMinus β₂ ↔ β₁ ⊆ β₂ := by
  calc
    _ ↔ FormulaSet.spectrum ({∼(⩕ n ∈ hβ₂.toFinset, (TBB n))}) ⊆ FormulaSet.spectrum ({∼(⩕ n ∈ hβ₁.toFinset, (TBB n))}) := by
      apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔) (by grind) (by grind);
      simp;
    _ ↔ β₂ᶜ ⊆ β₁ᶜ := by rw [TBBMinus_spectrum, TBBMinus_spectrum];
    _ ↔ β₁ ⊆ β₂ := by simp;

lemma GLα_subset_GLβMinus (hβ : βᶜ.Finite) : Modal.GLα β ⊆ Modal.GLβMinus β := by
  apply GL.iff_subset_closed_sumQuasiNormal_subset_spectrum (T := 𝗣𝗔) ?_ ?_ ?_ |>.mpr;
  . rw [TBBMinus_spectrum];
    simp [FormulaSet.spectrum];
  . grind;
  . grind;
  . simp;

end

end Modal

end LO
