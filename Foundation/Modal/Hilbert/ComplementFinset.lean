import Mathlib.Data.Set.Finite.Powerset
import Foundation.Modal.Complement
import Foundation.Modal.Hilbert.MaximalConsistentSet

namespace LO.Modal


section

variable {H : Hilbert α}
variable {φ ψ : Formula α}

lemma complement_derive_bot [DecidableEq α] (hp : H ⊢! φ) (hcp : H ⊢! -φ) : H ⊢! ⊥ := by
  induction φ using Formula.cases_neg with
  | hfalsum => assumption;
  | hatom a => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | hneg => unfold Formula.complement at hcp; exact hp ⨀ hcp;
  | hbox φ => unfold Formula.complement at hcp; exact hcp ⨀ hp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;

lemma neg_complement_derive_bot [DecidableEq α] (hp : H ⊢! ∼φ) (hcp : H ⊢! ∼(-φ)) : H ⊢! ⊥ := by
  induction φ using Formula.cases_neg with
  | hfalsum =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hatom a =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    unfold Formula.complement at hcp;
    exact hp ⨀ hcp;
  | himp φ ψ h =>
    simp only [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox φ =>
    unfold Formula.complement at hcp;
    exact hcp ⨀ hp;

end


def FormulaFinset.Consistent (H : Hilbert α) (P : FormulaFinset α) : Prop := P *⊬[H] ⊥

variable {P : FormulaFinset α} {φ : Formula α}

/-
@[simp]
lemma iff_theory_consistent_formulae_consistent {P : FormulaFinset α} : Theory.Consistent H P ↔ FormulaFinset.Consistent H P := by
  simp [Consistent, Theory.Consistent]
-/

/-
@[simp]
lemma empty_conisistent [Entailment.Consistent H] : FormulaFinset.Consistent H ∅ := by
  rw [←iff_theory_consistent_formulae_consistent];
  convert Theory.emptyset_consistent (α := α);
  . simp;
  . assumption;
-/

lemma provable_iff_insert_neg_not_consistent : P *⊢[H]! φ ↔ ¬(FormulaFinset.Consistent H (insert (∼φ) P)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.provable_iff_insert_neg_not_consistent;

lemma neg_provable_iff_insert_not_consistent : ↑P *⊢[H]! ∼φ ↔ ¬(FormulaFinset.Consistent H (insert (φ) P)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.neg_provable_iff_insert_not_consistent;

lemma unprovable_iff_singleton_neg_consistent : H ⊬ φ ↔ FormulaFinset.Consistent H ({∼φ}) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.unprovable_iff_singleton_neg_consistent;

lemma unprovable_iff_singleton_compl_consistent : H ⊬ φ ↔ FormulaFinset.Consistent H ({-φ}) := by
  rcases (Formula.complement.or φ) with (hp | ⟨ψ, rfl⟩);
  . rw [hp];
    convert Theory.unprovable_iff_singleton_neg_consistent (H := H) (φ := φ);
    simp;
  . simp only [Formula.complement];
    convert Theory.unprovable_iff_singleton_consistent (H := H) (φ := ψ);
    simp;

lemma provable_iff_singleton_compl_inconsistent : H ⊢! φ ↔ ¬(FormulaFinset.Consistent H ({-φ})) := by
  constructor;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mpr;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mp;

lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) → H ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ➝ ⊥)
  : FormulaFinset.Consistent H (P₁ ∪ P₂) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.intro_union_consistent h;

lemma intro_triunion_consistent
  (h : ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ P₁) ∧ (∀ φ ∈ Γ₂, φ ∈ P₂) ∧ (∀ φ ∈ Γ₃, φ ∈ P₃) → H ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃ ➝ ⊥)
  : FormulaFinset.Consistent H (P₁ ∪ P₂ ∪ P₃) := by
  rw [←iff_theory_consistent_formulae_consistent];
  convert Theory.intro_triunion_consistent h;
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


namespace exists_consistent_complementary_closed

open Classical

variable (H)

noncomputable def next (φ : Formula α) (P : FormulaFinset α) : FormulaFinset α :=
  if FormulaFinset.Consistent H (insert φ P) then insert φ P else insert (-φ) P

noncomputable def enum (P : FormulaFinset α) : (List (Formula α)) → FormulaFinset α
  | [] => P
  | ψ :: qs => next H ψ (enum P qs)
local notation:max t"[" l "]" => enum H t l

lemma next_consistent
  (P_consis : FormulaFinset.Consistent H P) (φ : Formula α)
  : FormulaFinset.Consistent H (next H φ P) := by
  simp only [next];
  split;
  . simpa;
  . rename_i h;
    by_contra hC;
    have h₁ := FormulaFinset.neg_provable_iff_insert_not_consistent (H := H) (P := P) (φ := φ) |>.mpr h;
    have h₂ := FormulaFinset.neg_provable_iff_insert_not_consistent (H := H) (P := P) (φ := -φ) |>.mpr hC;
    have := neg_complement_derive_bot h₁ h₂;
    contradiction;

lemma enum_consistent
  (P_consis : P.Consistent H )
  {l : List (Formula α)}
  : FormulaFinset.Consistent H (P[l]) := by
  induction l with
  | nil => exact P_consis;
  | cons ψ qs ih =>
    simp only [enum];
    apply next_consistent;
    exact ih;

@[simp] lemma enum_nil {P : FormulaFinset α} : (P[[]]) = P := by simp [enum]

lemma enum_subset_step {l : List (Formula α)} : (P[l]) ⊆ (P[(ψ :: l)]) := by
  simp [enum, next];
  split <;> simp;

lemma enum_subset {l : List (Formula α)} : P ⊆ P[l] := by
  induction l with
  | nil => simp;
  | cons ψ qs ih => exact Set.Subset.trans ih $ by apply enum_subset_step;

lemma either {l : List (Formula α)} (hp : φ ∈ l) : φ ∈ P[l] ∨ -φ ∈ P[l] := by
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

lemma subset {l : List (Formula α)} {φ : Formula α} (h : φ ∈ P[l])
  : φ ∈ P ∨ φ ∈ l ∨ (∃ ψ ∈ l, -ψ = φ)  := by
  induction l generalizing φ with
  | nil => simp_all;
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
  (S : FormulaFinset α)
  (h_sub : P ⊆ S⁻) (P_consis : FormulaFinset.Consistent H P)
  : ∃ P', P ⊆ P' ∧ FormulaFinset.Consistent H P' ∧ P'.ComplementaryClosed S := by
  use exists_consistent_complementary_closed.enum H P S.toList;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply enum_subset;
  . exact enum_consistent H P_consis;
  . simp only [FormulaFinset.complementary];
    intro φ hp;
    simp only [Finset.mem_union, Finset.mem_image];
    rcases subset H hp with (h | h | ⟨ψ, hq₁, hq₂⟩);
    . replace h := h_sub h;
      simp [complementary] at h;
      rcases h with (_ | ⟨a, b, rfl⟩);
      . tauto;
      . right;
        use a;
    . left; exact Finset.mem_toList.mp h;
    . right;
      use ψ;
      constructor;
      . exact Finset.mem_toList.mp hq₁;
      . assumption;
  . intro φ hp;
    exact either H (by simpa);

end Consistent

end FormulaFinset


variable [DecidableEq α]

structure ComplementaryClosedConsistentFormulaFinset (H) (S : FormulaFinset α) where
  formulae : FormulaFinset α
  consistent : formulae.Consistent H
  closed : formulae.ComplementaryClosed S
alias CCF := ComplementaryClosedConsistentFormulaFinset

namespace ComplementaryClosedConsistentFormulaFinset

open Entailment
open Formula (atom)
variable {H : Hilbert α}

lemma lindenbaum
  (S : FormulaFinset α)
  {X : FormulaFinset α} (X_sub : X ⊆ S⁻) (X_consis : X.Consistent H)
  : ∃ X' : CCF H S, X ⊆ X'.formulae := by
  obtain ⟨X', ⟨X'_sub, x, b⟩⟩ := FormulaFinset.exists_consistent_complementary_closed S X_sub X_consis;
  use ⟨X', (by assumption), (by assumption)⟩;

noncomputable instance [Entailment.Consistent H] : Inhabited (CCF H S) := ⟨lindenbaum (X := ∅) S (by simp) (by simp) |>.choose⟩

variable {S} {X X₁ X₂ : CCF H S}

@[simp] lemma unprovable_falsum : X.formulae *⊬[H] ⊥ := X.consistent

lemma mem_compl_of_not_mem (hs : ψ ∈ S) : ψ ∉ X.formulae → -ψ ∈ X.formulae := by
  intro h;
  rcases X.closed.either ψ (by assumption) with (h | h);
  . contradiction;
  . assumption;

lemma mem_of_not_mem_compl (hs : ψ ∈ S) : -ψ ∉ X.formulae → ψ ∈ X.formulae := by
  apply Not.imp_symm;
  exact mem_compl_of_not_mem hs;

lemma membership_iff (hq_sub : ψ ∈ S) : (ψ ∈ X.formulae) ↔ (X.formulae *⊢[H]! ψ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices -ψ ∉ X.formulae by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact X.closed.either ψ hq_sub;
    by_contra hC;
    have hnp : X.formulae *⊢[H]! -ψ := Context.by_axm! hC;
    have := complement_derive_bot hp hnp;
    simpa;

lemma mem_verum (h : ⊤ ∈ S) : ⊤ ∈ X.formulae := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp]
lemma mem_falsum : ⊥ ∉ X.formulae := Theory.not_mem_falsum_of_consistent X.consistent

lemma iff_mem_compl (hq_sub : ψ ∈ S) : (ψ ∈ X.formulae) ↔ (-ψ ∉ X.formulae) := by
  constructor;
  . intro hq; replace hq := membership_iff hq_sub |>.mp hq;
    by_contra hnq;
    induction ψ using Formula.cases_neg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[H]! ∼(atom a) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[H]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hbox ψ =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[H]! ∼(□ψ) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[H]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hneg ψ =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[H]! ψ := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[H]! ⊥ := complement_derive_bot hq this;
      simpa;
    | himp ψ χ h =>
      simp only [Formula.complement.imp_def₁ h] at hnq;
      have : ↑X.formulae *⊢[H]! ∼(ψ ➝ χ) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[H]! ⊥ := this ⨀ hq;
      simpa;
  . intro h; exact mem_of_not_mem_compl (by assumption) h;

lemma iff_mem_imp
  (hsub_qr : (ψ ➝ χ) ∈ S) (hsub_q : ψ ∈ S := by trivial)  (hsub_r : χ ∈ S := by trivial)
  : ((ψ ➝ χ) ∈ X.formulae) ↔ (ψ ∈ X.formulae) → (-χ ∉ X.formulae) := by
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
  (hsub_qr : (ψ ➝ χ) ∈ S) (hsub_q : ψ ∈ S := by trivial)  (hsub_r : χ ∈ S := by trivial)
  : ((ψ ➝ χ) ∉ X.formulae) ↔ (ψ ∈ X.formulae) ∧ (-χ ∈ X.formulae) := by
  simpa using @iff_mem_imp α _ H S X ψ χ hsub_qr hsub_q hsub_r |>.not;

lemma equality_def : X₁ = X₂ ↔ X₁.formulae = X₂.formulae := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases X₁; cases X₂; simp_all;

instance : Finite (CCF H S) := by
  let f : CCF H S → (Finset.powerset (S⁻)) := λ X => ⟨X.formulae, by simpa using X.closed.subset⟩
  have hf : Function.Injective f := by
    intro X₁ X₂ h;
    apply equality_def.mpr;
    simpa [f] using h;
  exact Finite.of_injective f hf;

end ComplementaryClosedConsistentFormulaFinset


end LO.Modal
