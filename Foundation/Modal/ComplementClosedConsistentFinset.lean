import Mathlib.Data.Set.Finite.Powerset
import Foundation.Modal.MaximalConsistentSet
import Foundation.Modal.Complement

namespace LO.Modal

open Entailment

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}

namespace FormulaFinset

variable {Φ Φ₁ Φ₂ : FormulaFinset α} {φ ψ : Formula α}

abbrev Consistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := Φ *⊬[𝓢] ⊥

abbrev Inconsistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := ¬(Consistent 𝓢 Φ)

omit [DecidableEq α] in
lemma iff_theory_consistent_formulae_consistent {Φ : FormulaFinset α} : FormulaSet.Consistent 𝓢 Φ ↔ FormulaFinset.Consistent 𝓢 Φ := by
  simp [Consistent, FormulaSet.Consistent]

omit [DecidableEq α] in
lemma iff_inconsistent_inconsistent {Φ : FormulaFinset α} : FormulaSet.Inconsistent 𝓢 Φ ↔ FormulaFinset.Inconsistent 𝓢 Φ := by
  simp [Inconsistent, FormulaSet.Inconsistent]

section

variable [Entailment.Classical 𝓢]

@[simp]
lemma empty_conisistent [Entailment.Consistent 𝓢] : FormulaFinset.Consistent 𝓢 ∅ := by
  convert FormulaSet.emptyset_consistent (α := α) <;> simpa;

lemma provable_iff_insert_neg_not_consistent : FormulaFinset.Inconsistent 𝓢 (insert (∼φ) Φ) ↔ ↑Φ *⊢[𝓢]! φ := by
  convert @FormulaSet.provable_iff_insert_neg_not_consistent α _ _ _ _ (𝓢 := 𝓢) (T := ↑Φ) (φ := φ);
  simp;

lemma neg_provable_iff_insert_not_consistent : FormulaFinset.Inconsistent 𝓢 (insert (φ) Φ) ↔ ↑Φ *⊢[𝓢]! ∼φ := by
  convert @FormulaSet.neg_provable_iff_insert_not_consistent α _ _ _ _ (𝓢 := 𝓢) (T := ↑Φ) (φ := φ);
  simp;

lemma unprovable_iff_singleton_neg_consistent : FormulaFinset.Consistent 𝓢 ({∼φ}) ↔ 𝓢 ⊬ φ := by
  convert @FormulaSet.unprovable_iff_singleton_neg_consistent α _ _ _ _ (𝓢 := 𝓢) (φ := φ);
  simp;

lemma unprovable_iff_singleton_compl_consistent : FormulaFinset.Consistent 𝓢 ({-φ}) ↔ 𝓢 ⊬ φ := by
  rcases (Formula.complement.or φ) with (hp | ⟨ψ, rfl⟩);
  . rw [hp];
    convert FormulaSet.unprovable_iff_singleton_neg_consistent (𝓢 := 𝓢) (φ := φ);
    simp;
  . simp only [Formula.complement];
    convert FormulaSet.unprovable_iff_singleton_consistent (𝓢 := 𝓢) (φ := ψ);
    simp;

lemma provable_iff_singleton_compl_inconsistent : (FormulaFinset.Inconsistent 𝓢 ({-φ})) ↔ 𝓢 ⊢! φ := by
  constructor;
  . contrapose;
    unfold Inconsistent;
    push_neg;
    apply unprovable_iff_singleton_compl_consistent.mpr;
  . contrapose;
    unfold Inconsistent;
    push_neg;
    apply unprovable_iff_singleton_compl_consistent.mp;

lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) → 𝓢 ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ➝ ⊥)
  : FormulaFinset.Consistent 𝓢 (P₁ ∪ P₂) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using FormulaSet.intro_union_consistent h;

lemma intro_triunion_consistent
  (h : ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) ∧ (∀ φ ∈ Γ₃, φ ∈ P₃) → 𝓢 ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃ ➝ ⊥)
  : FormulaFinset.Consistent 𝓢 (P₁ ∪ P₂ ∪ P₃) := by
  rw [←iff_theory_consistent_formulae_consistent];
  convert FormulaSet.intro_triunion_consistent h;
  ext;
  constructor;
  . simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe];
    rintro ((hp₁ | hp₂) | hp₃);
    . left; left; assumption;
    . left; right; assumption;
    . right; assumption;
  . simp only [Set.mem_union, Finset.coe_union, Finset.mem_coe];
    rintro ((hp₁ | hp₂) | hp₃);
    . left; left; assumption;
    . left; right; assumption;
    . right; assumption;

end


namespace exists_consistent_complementary_closed

open Classical

noncomputable def next (𝓢 : S) (φ : Formula α) (Φ : FormulaFinset α) : FormulaFinset α :=
  if FormulaFinset.Consistent 𝓢 (insert φ Φ) then insert φ Φ else insert (-φ) Φ

noncomputable def enum (𝓢 : S) (Φ : FormulaFinset α) : (List (Formula α)) → FormulaFinset α
  | [] => Φ
  | ψ :: qs => next 𝓢 ψ (enum 𝓢 Φ qs)
local notation:max t"[" l "]" => enum 𝓢 t l

lemma next_consistent [Entailment.Classical 𝓢]
  (Φ_consis : FormulaFinset.Consistent 𝓢 Φ) (φ : Formula α)
  : FormulaFinset.Consistent 𝓢 (next 𝓢 φ Φ) := by
  simp only [next];
  split;
  . simpa;
  . rename_i h;
    by_contra hC;
    have h₁ : ↑Φ *⊢[𝓢]! ∼φ := FormulaFinset.neg_provable_iff_insert_not_consistent (𝓢 := 𝓢) (Φ := Φ) (φ := φ) |>.mp h;
    have h₂ : ↑Φ *⊢[𝓢]! ∼-φ := @FormulaFinset.neg_provable_iff_insert_not_consistent α _ (𝓢 := 𝓢) _ _ (Φ := Φ) (-φ) |>.mp $ by
      unfold FormulaFinset.Inconsistent;
      simpa using hC;
    have : ↑Φ *⊢[𝓢]! ⊥ := neg_complement_derive_bot h₁ h₂;
    contradiction;

lemma enum_consistent [Entailment.Classical 𝓢]
  (Φ_consis : Φ.Consistent 𝓢) {l : List (Formula α)} : FormulaFinset.Consistent 𝓢 (Φ[l]) := by
  induction l with
  | nil => exact Φ_consis;
  | cons ψ qs ih =>
    simp only [enum];
    apply next_consistent;
    exact ih;

@[simp] lemma enum_nil {Φ : FormulaFinset α} : (Φ[[]]) = Φ := by simp [enum]

lemma enum_subset_step {l : List (Formula α)} : (Φ[l]) ⊆ (Φ[(ψ :: l)]) := by
  simp [enum, next];
  split <;> simp;

lemma enum_subset {l : List (Formula α)} : Φ ⊆ Φ[l] := by
  induction l with
  | nil => simp;
  | cons ψ qs ih => exact Set.Subset.trans ih $ by apply enum_subset_step;

lemma either {l : List (Formula α)} (hp : φ ∈ l) : φ ∈ Φ[l] ∨ -φ ∈ Φ[l] := by
  induction l with
  | nil => simp_all;
  | cons ψ qs ih =>
    simp at hp;
    simp [enum, next];
    rcases hp with (rfl | hp);
    . split <;> simp [Finset.mem_insert];
    . split <;> {
        simp [Finset.mem_insert];
        rcases (ih hp) with (_ | _) <;> tauto;
      }

lemma subset {l : List (Formula α)} {φ : Formula α} (h : φ ∈ Φ[l])
  : φ ∈ Φ ∨ φ ∈ l ∨ (∃ ψ ∈ l, -ψ = φ)  := by
  induction l generalizing φ with
  | nil =>
    simp_all;
  | cons ψ qs ih =>
    simp_all [enum, next];
    split at h;
    . rcases Finset.mem_insert.mp h with (rfl | h)
      . tauto;
      . rcases ih h <;> tauto;
    . rcases Finset.mem_insert.mp h with (rfl | h)
      . tauto;
      . rcases ih h <;> tauto;

end exists_consistent_complementary_closed

open exists_consistent_complementary_closed in
lemma exists_consistent_complementary_closed
  [Entailment.Classical 𝓢]
  {S : FormulaFinset α}
  (h_sub : P ⊆ S⁻) (P_consis : FormulaFinset.Consistent 𝓢 P)
  : ∃ P', P ⊆ P' ∧ FormulaFinset.Consistent 𝓢 P' ∧ P'.ComplementaryClosed S := by
  use exists_consistent_complementary_closed.enum 𝓢 P S.toList;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply enum_subset;
  . exact enum_consistent P_consis;
  . simp only [FormulaFinset.complementary];
    intro φ hp;
    simp only [Finset.mem_union, Finset.mem_image];
    rcases subset hp with (h | h | ⟨ψ, hq₁, hq₂⟩);
    . replace h := h_sub h;
      simp [complementary] at h;
      rcases h with (_ | ⟨a, b, rfl⟩);
      . tauto;
      . right;
        use a;
    . left;
      exact Finset.mem_toList.mp h;
    . right;
      use ψ;
      constructor;
      . exact Finset.mem_toList.mp hq₁;
      . assumption;
  . intro φ hp;
    exact either (by simpa);

end FormulaFinset


section

open Entailment
open Formula (atom)
open FormulaFinset

variable {Φ Ψ : FormulaFinset α}

abbrev ComplementClosedConsistentFinset (𝓢 : S) (Ψ : FormulaFinset α) := { T : FormulaFinset α // (Consistent 𝓢 T) ∧ (T.ComplementaryClosed Ψ)}

namespace ComplementClosedConsistentFinset

instance : Membership (Formula α) (ComplementClosedConsistentFinset 𝓢 Ψ) := ⟨λ X φ => φ ∈ X.1⟩

lemma consistent (X : ComplementClosedConsistentFinset 𝓢 Ψ) : Consistent 𝓢 X := X.2.1

lemma closed (X : ComplementClosedConsistentFinset 𝓢 Ψ) : ComplementaryClosed X Ψ := X.2.2

variable {X X₁ X₂ : ComplementClosedConsistentFinset 𝓢 Ψ}

@[simp] lemma unprovable_falsum : X.1 *⊬[𝓢] ⊥ := X.consistent

lemma mem_compl_of_not_mem (hs : ψ ∈ Ψ) : ψ ∉ X → -ψ ∈ X := by
  intro h;
  rcases X.closed.either ψ (by assumption) with (h | h);
  . contradiction;
  . assumption;

lemma mem_of_not_mem_compl (hs : ψ ∈ Ψ) : -ψ ∉ X → ψ ∈ X := by
  apply Not.imp_symm;
  exact mem_compl_of_not_mem hs;

lemma equality_def : X₁ = X₂ ↔ X₁.1 = X₂.1 := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases X₁; cases X₂; simp_all;

variable [Entailment.Classical 𝓢]

lemma lindenbaum
  {Φ Ψ : FormulaFinset α}
  (X_sub : Φ ⊆ Ψ⁻) (X_consis : Φ.Consistent 𝓢)
  : ∃ X' : ComplementClosedConsistentFinset 𝓢 Ψ, Φ ⊆ X'.1 := by
  obtain ⟨Y, ⟨_, _, _⟩⟩ := FormulaFinset.exists_consistent_complementary_closed X_sub X_consis;
  use ⟨Y, (by assumption), (by assumption)⟩;

noncomputable instance [Entailment.Consistent 𝓢] : Inhabited (ComplementClosedConsistentFinset 𝓢 Ψ) := ⟨lindenbaum (Φ := ∅) (Ψ := Ψ) (by simp) (FormulaFinset.empty_conisistent) |>.choose⟩

lemma membership_iff (hq_sub : ψ ∈ Ψ) : (ψ ∈ X) ↔ (X *⊢[𝓢]! ψ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices -ψ ∉ X by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact X.closed.either ψ hq_sub;
    by_contra hC;
    have hnp : X *⊢[𝓢]! -ψ := Context.by_axm! hC;
    have := complement_derive_bot hp hnp;
    simpa;

lemma mem_verum (h : ⊤ ∈ Ψ) : ⊤ ∈ X := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp] lemma mem_falsum : ⊥ ∉ X := FormulaSet.not_mem_falsum_of_consistent X.consistent

lemma iff_mem_compl (hq_sub : ψ ∈ Ψ) : (ψ ∈ X) ↔ (-ψ ∉ X) := by
  constructor;
  . intro hq; replace hq := membership_iff hq_sub |>.mp hq;
    by_contra hnq;
    induction ψ using Formula.cases_neg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a =>
      simp only [Formula.complement] at hnq;
      have : ↑X *⊢[𝓢]! ∼(atom a) := Context.by_axm! hnq;
      have : ↑X *⊢[𝓢]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hbox ψ =>
      simp only [Formula.complement] at hnq;
      have : ↑X *⊢[𝓢]! ∼(□ψ) := Context.by_axm! hnq;
      have : ↑X *⊢[𝓢]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hneg ψ =>
      simp only [Formula.complement] at hnq;
      have : ↑X *⊢[𝓢]! ψ := Context.by_axm! hnq;
      have : ↑X *⊢[𝓢]! ⊥ := complement_derive_bot hq this;
      simpa;
    | himp ψ χ h =>
      simp only [Formula.complement.imp_def₁ h] at hnq;
      have : ↑X *⊢[𝓢]! ∼(ψ ➝ χ) := Context.by_axm! hnq;
      have : ↑X *⊢[𝓢]! ⊥ := this ⨀ hq;
      simpa;
  . intro h; exact mem_of_not_mem_compl (by assumption) h;

lemma iff_mem_imp
  (hsub_qr : (ψ ➝ χ) ∈ Ψ) (hsub_q : ψ ∈ Ψ)  (hsub_r : χ ∈ Ψ)
  : ((ψ ➝ χ) ∈ X) ↔ (ψ ∈ X) → (-χ ∉ X) := by
  constructor;
  . intro hqr hq;
    apply iff_mem_compl hsub_r |>.mp;
    replace hqr := membership_iff hsub_qr |>.mp hqr;
    replace hq := membership_iff hsub_q |>.mp hq;
    exact membership_iff hsub_r |>.mpr $ hqr ⨀ hq;
  . intro hqr; replace hqr := not_or_of_imp hqr
    rcases hqr with (hq | hr);
    . apply membership_iff hsub_qr |>.mpr;
      replace hq := mem_compl_of_not_mem hsub_q hq;
      induction ψ using Formula.cases_neg with
      | hfalsum => exact efq!;
      | hatom a => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hbox ψ => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hneg ψ =>
        simp only [Formula.complement.neg_def] at hq;
        exact efq_of_neg₂! $ Context.by_axm! hq;
      | himp ψ χ h =>
        simp only [Formula.complement.imp_def₁ h] at hq;
        exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
    . apply membership_iff (by assumption) |>.mpr;
      exact imply₁'! $ membership_iff (by assumption) |>.mp $ iff_mem_compl (by assumption) |>.mpr hr;

lemma iff_not_mem_imp
  (hsub_qr : (ψ ➝ χ) ∈ Ψ) (hsub_q : ψ ∈ Ψ)  (hsub_r : χ ∈ Ψ)
  : ((ψ ➝ χ) ∉ X) ↔ (ψ ∈ X) ∧ (-χ ∈ X) := by
  simpa using @iff_mem_imp α (𝓢 := 𝓢) _ _ _ Ψ X _ ψ χ hsub_qr hsub_q hsub_r |>.not;

instance : Finite (ComplementClosedConsistentFinset 𝓢 Ψ) := by
  let f : ComplementClosedConsistentFinset 𝓢 Ψ → (Finset.powerset (Ψ⁻)) := λ X => ⟨X, by simpa using X.closed.subset⟩
  have hf : Function.Injective f := by
    intro X₁ X₂ h;
    apply equality_def.mpr;
    simpa [f] using h;
  exact Finite.of_injective f hf;

end ComplementClosedConsistentFinset

end


end LO.Modal
