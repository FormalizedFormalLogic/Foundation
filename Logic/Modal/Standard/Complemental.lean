import Logic.Modal.Standard.ConsistentTheory

namespace LO.Modal.Standard

variable [DecidableEq α]
variable {Λ : DeductionParameter α}

namespace Formula

def complement : Formula α → Formula α
  | ~p => p
  | p  => ~p
prefix:80 "-" => complement

namespace complement

variable {p q : Formula α}

@[simp] lemma neg_def : -(~p) = p := by
  induction p using Formula.rec' <;> simp_all [complement]

@[simp] lemma bot_def : -(⊥ : Formula α) = ~(⊥) := by simp only [complement, imp_inj, and_true]; rfl;

@[simp] lemma box_def : -(□p) = ~(□p) := by simp only [complement, imp_inj, and_true]; rfl;

lemma imp_def₁ (hq : q ≠ ⊥) : -(p ⟶ q) = ~(p ⟶ q) := by
  simp only [complement];
  split;
  . rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  . rfl;

lemma imp_def₂ (hq : q = ⊥) : -(p ⟶ q) = p := by
  subst_vars;
  apply neg_def;

lemma resort_box (h : -p = □q) : p = ~□q := by
  simp [complement] at h;
  split at h;
  . subst_vars; rfl;
  . contradiction;

lemma or (p : Formula α) : -p = ~p ∨ ∃ q, ~q = p := by
  induction p using Formula.cases_neg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox p => simp [complement]; rfl;

end complement

end Formula

section

variable [System (Formula α) S] {𝓢 : S}
variable [System.ModusPonens 𝓢]
variable {p q : Formula α}

lemma complement_derive_bot (hp : 𝓢 ⊢! p) (hcp : 𝓢 ⊢! -p) : 𝓢 ⊢! ⊥ := by
  induction p using Formula.cases_neg with
  | hfalsum => assumption;
  | hatom a =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    simp [Formula.complement] at hcp;
    exact hp ⨀ hcp;
  | himp p q h =>
    simp [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox p =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;

lemma neg_complement_derive_bot (hp : 𝓢 ⊢! ~p) (hcp : 𝓢 ⊢! ~(-p)) : 𝓢 ⊢! ⊥ := by
  induction p using Formula.cases_neg with
  | hfalsum =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hatom a =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    simp [Formula.complement] at hcp;
    exact hp ⨀ hcp;
  | himp p q h =>
    simp [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox p =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;

end


namespace Formulae

def complementary (P : Formulae α) : Formulae α := P ∪ (P.image (Formula.complement))
postfix:80 "⁻" => Formulae.complementary

variable {P P₁ P₂ : Formulae α} {p q r: Formula α}

lemma complementary_mem (h : p ∈ P) : p ∈ P⁻ := by simp [complementary]; tauto;
macro_rules | `(tactic| trivial) => `(tactic| apply complementary_mem $ by assumption)

lemma complementary_comp (h : p ∈ P) : -p ∈ P⁻ := by simp [complementary]; tauto;
macro_rules | `(tactic| trivial) => `(tactic| apply complementary_comp $ by assumption)

lemma complementary_mem_box [P.SubformulaClosed] : □p ∈ P⁻ → □p ∈ P := by
  simp [complementary];
  intro h;
  rcases h with (h | ⟨q, hq, eq⟩);
  . assumption;
  . replace eq := Formula.complement.resort_box eq;
    subst eq;
    trivial;

class ComplementaryClosed (P : Formulae α) (S : Formulae α) : Prop where
  subset : P ⊆ S⁻
  either : ∀ p ∈ S, p ∈ P ∨ -p ∈ P

def SubformulaeComplementaryClosed (P : Formulae α) (p : Formula α) : Prop := P.ComplementaryClosed (𝒮 p)



section Consistent

def Consistent (Λ : DeductionParameter α) (P : Formulae α) : Prop :=  P *⊬[Λ]! ⊥

open Theory

@[simp]
lemma iff_theory_consistent_formulae_consistent {P : Formulae α}
  : Theory.Consistent Λ P ↔ Formulae.Consistent Λ P := by simp [Consistent, Theory.Consistent]

lemma provable_iff_insert_neg_not_consistent : ↑P *⊢[Λ]! p ↔ ¬(Formulae.Consistent Λ (insert (~p) P)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.provable_iff_insert_neg_not_consistent;

lemma neg_provable_iff_insert_not_consistent : ↑P *⊢[Λ]! ~p ↔ ¬(Formulae.Consistent Λ (insert (p) P)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.neg_provable_iff_insert_not_consistent;

lemma unprovable_iff_singleton_neg_consistent : Λ ⊬! p ↔ Formulae.Consistent Λ ({~p}) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.unprovable_iff_singleton_neg_consistent;

lemma unprovable_iff_singleton_compl_consistent : Λ ⊬! p ↔ Formulae.Consistent Λ ({-p}) := by
  rcases (Formula.complement.or p) with (hp | ⟨q, rfl⟩);
  . rw [hp];
    convert Theory.unprovable_iff_singleton_neg_consistent (Λ := Λ) (p := p);
    simp;
  . simp only [Formula.complement];
    convert Theory.unprovable_iff_singleton_consistent (Λ := Λ) (p := q);
    simp;

lemma provable_iff_singleton_compl_inconsistent : Λ ⊢! p ↔ ¬(Formulae.Consistent Λ ({-p})) := by
  constructor;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mpr;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mp;

lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ P₁) ∧ (∀ p ∈ Γ₂, p ∈ P₂) → Λ ⊬! ⋀Γ₁ ⋏ ⋀Γ₂ ⟶ ⊥)
  : Formulae.Consistent Λ (P₁ ∪ P₂) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.intro_union_consistent h;

lemma intro_triunion_consistent
  (h : ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ P₁) ∧ (∀ p ∈ Γ₂, p ∈ P₂) ∧ (∀ p ∈ Γ₃, p ∈ P₃) → Λ ⊬! ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃ ⟶ ⊥)
  : Formulae.Consistent Λ (P₁ ∪ P₂ ∪ P₃) := by
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

@[simp]
lemma empty_conisistent [System.Consistent Λ] : Formulae.Consistent Λ ∅ := by
  rw [←iff_theory_consistent_formulae_consistent];
  convert Theory.emptyset_consistent (α := α);
  . simp;
  . assumption;


namespace exists_consistent_complementary_closed

open Classical

variable (Λ)

noncomputable def next (p : Formula α) (P : Formulae α) : Formulae α :=
  if Formulae.Consistent Λ (insert p P) then insert p P else insert (-p) P

noncomputable def enum (P : Formulae α) : (List (Formula α)) → Formulae α
  | [] => P
  | q :: qs => next Λ q (enum P qs)
local notation:max t"[" l "]" => enum Λ t l

lemma next_consistent
  (P_consis : Formulae.Consistent Λ P) (p : Formula α)
  : Formulae.Consistent Λ (next Λ p P) := by
  simp only [next];
  split;
  . simpa;
  . rename_i h;
    have h₁ := Formulae.neg_provable_iff_insert_not_consistent (Λ := Λ) (P := P) (p := p) |>.mpr h;
    by_contra hC;
    have h₂ := Formulae.neg_provable_iff_insert_not_consistent (Λ := Λ) (P := P) (p := -p) |>.mpr hC;
    have := neg_complement_derive_bot h₁ h₂;
    contradiction;

lemma enum_consistent
  (P_consis : Formulae.Consistent Λ P)
  {l : List (Formula α)}
  : Formulae.Consistent Λ (P[l]) := by
  induction l with
  | nil => exact P_consis;
  | cons q qs ih =>
    simp only [enum];
    apply next_consistent;
    exact ih;

@[simp] lemma enum_nil {P : Formulae α} : (P[[]]) = P := by simp [enum]

lemma enum_subset_step {l : List (Formula α)} : (P[l]) ⊆ (P[(q :: l)]) := by
  simp [enum, next];
  split <;> simp;

lemma enum_subset {l : List (Formula α)} : P ⊆ P[l] := by
  induction l with
  | nil => simp;
  | cons q qs ih => exact Set.Subset.trans ih $ by apply enum_subset_step;

lemma either {l : List (Formula α)} (hp : p ∈ l) : p ∈ P[l] ∨ -p ∈ P[l] := by
  induction l with
  | nil => simp_all;
  | cons q qs ih =>
    simp at hp;
    simp [enum, next];
    rcases hp with (rfl | hp);
    . split <;> simp [Finset.mem_insert];
    . split <;> {
        simp [Finset.mem_insert];
        rcases (ih hp) with (_ | _) <;> tauto;
      }

lemma subset {l : List (Formula α)} {p : Formula α} (h : p ∈ P[l])
  : p ∈ P ∨ p ∈ l ∨ (∃ q ∈ l, -q = p)  := by
  induction l generalizing p with
  | nil => simp_all;
  | cons q qs ih =>
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
  (S : Formulae α)
  (h_sub : P ⊆ S⁻) (P_consis : Formulae.Consistent Λ P)
  : ∃ P', P ⊆ P' ∧ Formulae.Consistent Λ P' ∧ P'.ComplementaryClosed S := by
  use exists_consistent_complementary_closed.enum Λ P S.toList;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply enum_subset;
  . exact enum_consistent Λ P_consis;
  . simp [Formulae.complementary];
    intro p hp;
    simp only [Finset.mem_union, Finset.mem_image];
    rcases subset Λ hp with (h | h | ⟨q, hq₁, hq₂⟩);
    . replace h := h_sub h;
      simp [complementary] at h;
      rcases h with (_ | ⟨a, b, rfl⟩);
      . tauto;
      . right; use a;
    . left; exact Finset.mem_toList.mp h;
    . right;
      use q;
      constructor;
      . exact Finset.mem_toList.mp hq₁;
      . assumption;
  . intro p hp;
    exact either Λ (by simpa);

end Consistent

end Formulae



structure ComplementaryClosedConsistentFormulae (Λ) (S : Formulae α) where
  formulae : Formulae α
  consistent : formulae.Consistent Λ
  closed : formulae.ComplementaryClosed S
alias CCF := ComplementaryClosedConsistentFormulae

namespace ComplementaryClosedConsistentFormulae

open System
open Formula (atom)
variable {Λ : DeductionParameter α}

lemma lindenbaum
  (S : Formulae α)
  {X : Formulae α} (X_sub : X ⊆ S⁻) (X_consis : X.Consistent Λ)
  : ∃ X' : CCF Λ S, X ⊆ X'.formulae := by
  obtain ⟨X', ⟨X'_sub, x, b⟩⟩ := Formulae.exists_consistent_complementary_closed S X_sub X_consis;
  use ⟨X', (by assumption), (by assumption)⟩;

noncomputable instance [System.Consistent Λ] : Inhabited (CCF Λ S) := ⟨lindenbaum (X := ∅) S (by simp) (by simp) |>.choose⟩

variable {S} {X X₁ X₂ : CCF Λ S}

@[simp] lemma unprovable_falsum : X.formulae *⊬[Λ]! ⊥ := X.consistent

lemma mem_compl_of_not_mem (hs : q ∈ S) : q ∉ X.formulae → -q ∈ X.formulae := by
  intro h;
  rcases X.closed.either q (by assumption) with (h | h);
  . contradiction;
  . assumption;

lemma mem_of_not_mem_compl (hs : q ∈ S) : -q ∉ X.formulae → q ∈ X.formulae := by
  apply Not.imp_symm;
  exact mem_compl_of_not_mem hs;

lemma membership_iff (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (X.formulae *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices -q ∉ X.formulae by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact X.closed.either q hq_sub;
    by_contra hC;
    have hnp : X.formulae *⊢[Λ]! -q := Context.by_axm! hC;
    have := complement_derive_bot hp hnp;
    simpa;

lemma mem_verum (h : ⊤ ∈ S) : ⊤ ∈ X.formulae := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp]
lemma mem_falsum : ⊥ ∉ X.formulae := Theory.not_mem_falsum_of_consistent X.consistent

lemma iff_mem_compl (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (-q ∉ X.formulae) := by
  constructor;
  . intro hq; replace hq := membership_iff hq_sub |>.mp hq;
    by_contra hnq;
    induction q using Formula.cases_neg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(atom a) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hbox q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(□q) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hneg q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! q := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | himp q r h =>
      simp only [Formula.complement.imp_def₁ h] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(q ⟶ r) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := this ⨀ hq;
      simpa;
  . intro h; exact mem_of_not_mem_compl (by assumption) h;

lemma iff_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∈ X.formulae) ↔ (q ∈ X.formulae) → (-r ∉ X.formulae) := by
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
      induction q using Formula.cases_neg with
      | hfalsum => exact efq!;
      | hatom a => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hbox q => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hneg q =>
        simp only [Formula.complement.neg_def] at hq;
        exact efq_of_neg₂! $ Context.by_axm! hq;
      | himp q r h =>
        simp only [Formula.complement.imp_def₁ h] at hq;
        exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
    . apply membership_iff (by assumption) |>.mpr;
      exact dhyp! $ membership_iff (by assumption) |>.mp $ iff_mem_compl (by assumption) |>.mpr hr;

lemma iff_not_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∉ X.formulae) ↔ (q ∈ X.formulae) ∧ (-r ∈ X.formulae) := by
  simpa using @iff_mem_imp α _ Λ S X q r hsub_qr hsub_q hsub_r |>.not;

lemma equality_def : X₁ = X₂ ↔ X₁.formulae = X₂.formulae := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases X₁; cases X₂; simp_all;

instance : Finite (CCF Λ S) := by
  let f : CCF Λ S → (Finset.powerset (S⁻)) := λ X => ⟨X.formulae, by simpa using X.closed.subset⟩
  have hf : Function.Injective f := by
    intro X₁ X₂ h;
    apply equality_def.mpr;
    simpa [f] using h;
  exact Finite.of_injective f hf;

end ComplementaryClosedConsistentFormulae


end LO.Modal.Standard
