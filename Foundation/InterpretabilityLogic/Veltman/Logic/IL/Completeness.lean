import Foundation.InterpretabilityLogic.Veltman.Logic.IL.Soundness


namespace LO

class Compl (F : Type*) [Tilde F] where
  compl : F → F

prefix:120 "-" => Compl.compl



namespace Entailment

class ComplEquiv [LogicalConnective F] [Compl F] [Entailment S F] (𝓢 : S) where
  compl_equiv! {φ : F} : 𝓢 ⊢! ∼φ ⭤ -φ
export ComplEquiv (compl_equiv!)


section

variable {F S : Type*} [LogicalConnective F] [Compl F] [Entailment S F]
         {𝓢 : S} {φ : F} [ComplEquiv 𝓢]

@[simp] lemma compl_equiv : 𝓢 ⊢ ∼φ ⭤ -φ := ⟨compl_equiv!⟩


section

variable [Entailment.Minimal 𝓢]

def compl_of_neg! [Entailment.Minimal 𝓢] (h : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! -φ := K_left compl_equiv! ⨀ h
@[grind] lemma compl_of_neg : 𝓢 ⊢ ∼φ → 𝓢 ⊢ -φ := λ ⟨a⟩ => ⟨compl_of_neg! a⟩

def neg_of_compl! [Entailment.Minimal 𝓢] (h : 𝓢 ⊢! -φ) : 𝓢 ⊢! ∼φ := K_right compl_equiv! ⨀ h
@[grind] lemma neg_of_compl : 𝓢 ⊢ -φ → 𝓢 ⊢ ∼φ := λ ⟨a⟩ => ⟨neg_of_compl! a⟩

def O_of_compl! (h₁ : 𝓢 ⊢! φ) (h₂ : 𝓢 ⊢! -φ) : 𝓢 ⊢! ⊥ := negMDP (neg_of_compl! h₂) h₁
@[grind] lemma O_of_compl : 𝓢 ⊢ φ → 𝓢 ⊢ -φ → 𝓢 ⊢ ⊥ := λ ⟨a⟩ ⟨b⟩ => ⟨O_of_compl! a b⟩

def O_of_Ncompl! [DecidableEq F] (h₁ : 𝓢 ⊢! ∼φ) (h₂ : 𝓢 ⊢! ∼-φ) : 𝓢 ⊢! ⊥ := negMDP (K_right (ENN_of_E compl_equiv!) ⨀ h₂) h₁
@[grind] lemma O_of_Ncompl [DecidableEq F] : 𝓢 ⊢ ∼φ → 𝓢 ⊢ ∼-φ → 𝓢 ⊢ ⊥ := λ ⟨a⟩ ⟨b⟩ => ⟨O_of_Ncompl! a b⟩

instance FiniteContext.ComplEquiv (Γ : FiniteContext F 𝓢) : ComplEquiv Γ := ⟨λ {_} => of compl_equiv!⟩

instance Context.ComplEquiv (Γ : Context F 𝓢) : ComplEquiv Γ := ⟨λ {_} => of compl_equiv!⟩

end

end

end Entailment



namespace CCMF

open LO.Entailment LO.Entailment.Context LO.Modal.Entailment


variable {F} [LogicalConnective F] [DecidableEq F]
         {S} [Entailment S F]
variable {𝓢 : S} {Γ Δ : Finset F} {φ ψ : F}

def Consistent (𝓢 : S) (Γ : Finset F) : Prop := Γ *⊬[𝓢] ⊥

lemma def_consistent [Entailment.Minimal 𝓢] : Consistent 𝓢 Γ ↔ ∀ Δ : Finset F, (Δ ⊆ Γ) → Δ *⊬[𝓢] ⊥ := by
  constructor;
  . intro h Δ hΔ;
    have := Context.provable_iff_finset.not.mp h;
    push_neg at this;
    apply this;
    simpa;
  . intro h;
    apply Context.provable_iff_finset.not.mpr;
    push_neg;
    simpa using h;


def Inconsistent (𝓢 : S) (Γ : Finset F) : Prop := ¬(Consistent 𝓢 Γ)

lemma def_inconsistent [Entailment.Minimal 𝓢] : Inconsistent 𝓢 Γ ↔ ∃ Δ : Finset F, (Δ ⊆ Γ) ∧ (Δ *⊢[𝓢] ⊥) := by
  rw [Inconsistent, def_consistent];
  push_neg;
  simp;


def Maximal (𝓢 : S) (Γ : Finset F) : Prop := ∀ Δ, Γ ⊂ Δ → Inconsistent 𝓢 Δ

def ComplementSubset [Compl F] (Γ Δ : Finset F) : Prop := Γ ⊆ (Δ ∪ Δ.image (-·))

/-- For every `φ` in `Δ`, `φ` or `-φ` is in `Γ` -/
def ComplementMaximal [Compl F] (Γ Δ : Finset F) : Prop := ∀ φ ∈ Δ, φ ∈ Γ ∨ -φ ∈ Γ


section

variable [Entailment.Cl 𝓢]

@[simp]
lemma empty_conisistent [consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ∅ := by
  obtain ⟨φ, hφ⟩ := consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Δ hΔ;
  rw [(show Δ = ∅ by simpa [Set.subset_empty_iff, Finset.coe_eq_empty] using hΔ)];
  contrapose! hφ;
  apply Context.emptyPrf!
  apply of_O!;
  simp_all;

@[grind]
lemma not_mem_falsum (Γ_consis : Consistent 𝓢 Γ) : ⊥ ∉ Γ := by
  contrapose! Γ_consis;
  suffices Γ *⊢[𝓢] ⊥ by simpa [Consistent];
  apply Context.by_axm!;
  simpa;

@[grind]
lemma not_mem_neg_of_mem (Γ_consis : Consistent 𝓢 Γ) (h : φ ∈ Γ) : ∼φ ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . grind;

@[grind]
lemma not_mem_of_mem_neg (Γ_consis : Consistent 𝓢 Γ) (h : ∼φ ∈ Γ) : φ ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . grind;

lemma iff_insert_consistent : Consistent 𝓢 (insert φ Γ) ↔ ∀ Δ ⊆ Γ, Δ *⊬[𝓢] φ ➝ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    have := def_consistent.mp h (insert φ Γ) ?_;
    . contrapose! this;
      simp only [Finset.coe_insert];
      apply Context.deductInv! this;
    . grind;
  . intro h;
    apply def_consistent.mpr;
    intro Γ hΓ;
    have := @h (Γ.erase φ) (by grind);
    contrapose! this;
    simp only [Finset.coe_erase];
    apply Context.deduct!;
    apply Context.weakening! (Γ := Γ);
    . simp;
    . assumption;

lemma iff_insert_inconsistent : Inconsistent 𝓢 (insert φ Γ) ↔ ∃ Δ ⊆ Γ, Δ *⊢[𝓢] φ ➝ ⊥ := by
  unfold Inconsistent;
  apply not_iff_not.mp;
  push_neg;
  exact iff_insert_consistent;

lemma neg_provable_iff_insert_not_consistent : Inconsistent 𝓢 (insert φ Γ) ↔ Γ *⊢[𝓢] ∼φ := by
  apply Iff.trans iff_insert_inconsistent;
  constructor;
  . rintro ⟨Δ, hΓΔ, hΔ⟩;
    apply N!_iff_CO!.mpr;
    apply weakening! hΓΔ hΔ;
  . intro h;
    use Γ;
    constructor;
    . tauto;
    . apply N!_iff_CO!.mp h;

end


section

variable [Compl F] [Entailment.Cl 𝓢] [ComplEquiv 𝓢]

@[grind]
lemma not_mem_compl_of_mem (Γ_consis : Consistent 𝓢 Γ) (h : φ ∈ Γ) : (-φ) ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, -φ} ?_;
  . replace h₁ : {φ, -φ} *⊢[𝓢] φ := by_axm! (by simp);
    replace h₂ : {φ, -φ} *⊢[𝓢] -φ := by_axm! (by simp);
    convert O_of_compl h₁ h₂;
    simp;
  . grind;

@[grind]
lemma not_mem_of_mem_compl (Γ_consis : Consistent 𝓢 Γ) (h : -φ ∈ Γ) : φ ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, -φ} ?_;
  . replace h₁ : {φ, -φ} *⊢[𝓢] φ := by_axm! (by simp);
    replace h₂ : {φ, -φ} *⊢[𝓢] -φ := by_axm! (by simp);
    convert O_of_compl h₁ h₂;
    simp;
  . grind;

end


namespace exists_consistent_complementary_closed

open Classical

variable [Compl F]

variable {Γ : Finset F} {l : List F}

noncomputable def next (𝓢 : S) (φ : F) (Γ : Finset F) : Finset F := if Consistent 𝓢 (insert φ Γ) then insert φ Γ else insert (-φ) Γ

noncomputable def enum (𝓢 : S) (Γ : Finset F) : List F → Finset F
  | [] => Γ
  | ψ :: ψs => next 𝓢 ψ (enum 𝓢 Γ ψs)

local notation:max t"[" l "]" => enum 𝓢 t l


section

@[simp] lemma eq_enum_nil : Γ[[]] = Γ := by simp [enum]

@[simp]
lemma subset_enum_step : Γ[l] ⊆ (Γ[(ψ :: l)]) := by
  simp [enum, next];
  split <;> simp;

@[simp]
lemma subset_enum : Γ ⊆ Γ[l] := by
  induction l with
  | nil => simp;
  | cons ψ ψs ih => exact Set.Subset.trans ih $ by apply subset_enum_step;


lemma of_mem_seed (h : φ ∈ l) : φ ∈ Γ[l] ∨ -φ ∈ Γ[l] := by
  induction l with
  | nil => simp_all;
  | cons ψ ψs ih =>
    simp only [enum, next];
    rcases List.mem_cons.mp h with (rfl | h) <;> grind;

lemma of_mem_enum (h : φ ∈ Γ[l]) : φ ∈ Γ ∨ φ ∈ l ∨ (∃ ψ ∈ l, -ψ = φ)  := by
  induction l generalizing φ with
  | nil => simp_all;
  | cons ψ ψs ih =>
    simp only [enum, next] at h;
    split at h <;> rcases Finset.mem_insert.mp h with (rfl | h) <;> grind;

end


section

variable [ComplEquiv 𝓢] [Entailment.Cl 𝓢]

lemma consistent_next (Γ_consis : Consistent 𝓢 Γ) (φ : F) : Consistent 𝓢 (next 𝓢 φ Γ) := by
  simp only [next];
  split;
  . simpa;
  . rename_i h;
    by_contra hC;
    have h₁ : ↑Γ *⊢[𝓢] ∼φ := neg_provable_iff_insert_not_consistent.mp h;
    have h₂ : ↑Γ *⊢[𝓢] ∼-φ := @neg_provable_iff_insert_not_consistent.mp hC;
    have : ↑Γ *⊢[𝓢] ⊥ := O_of_Ncompl h₁ h₂;
    contradiction;

@[grind]
lemma consistent_enum (Γ_consis : Consistent 𝓢 Γ) : Consistent 𝓢 (Γ[l]) := by
  induction l with
  | nil => exact Γ_consis;
  | cons ψ ψs ih => apply consistent_next; exact ih;

end

end exists_consistent_complementary_closed


open exists_consistent_complementary_closed in
theorem exists_consistent_complement_maximal {Ξ : Finset F} [Compl F] [ComplEquiv 𝓢] [Entailment.Cl 𝓢]
  (Γ_consis : Consistent 𝓢 Γ)
  (subset_ΓΔ : ComplementSubset Γ Ξ)
  : ∃ Γ', (Γ ⊆ Γ') ∧ (Consistent 𝓢 Γ') ∧ (ComplementSubset Γ' Ξ) ∧ (ComplementMaximal Γ' Ξ) := by
  use enum 𝓢 Γ Ξ.toList;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . simp;
  . grind;
  . intro φ hφ;
    simp only [Finset.mem_union, Finset.mem_image];
    rcases of_mem_enum hφ with (hφ | hφ | ⟨ψ, hψ, rfl⟩);
    . dsimp [ComplementSubset] at subset_ΓΔ
      grind;
    . left;
      simpa using hφ;
    . right;
      use ψ;
      constructor;
      . simpa using hψ;
      . rfl
  . intro φ hφ;
    apply of_mem_seed;
    simpa;

section

variable [Compl F] {Φ : Finset F}

abbrev ComplementMaximalConsistentFinset (𝓢 : S) (Φ : Finset F) := { Γ : Finset F // (Consistent 𝓢 Γ) ∧ (ComplementSubset Γ Φ) ∧ (ComplementMaximal Γ Φ) }

variable {Γ Γ₁ Γ₂ Δ : ComplementMaximalConsistentFinset 𝓢 Φ} {φ ψ : F}

namespace ComplementMaximalConsistentFinset

instance : Membership (F) (ComplementMaximalConsistentFinset 𝓢 Φ) := ⟨λ X φ => φ ∈ X.1⟩

@[simp] lemma consistent (Γ : ComplementMaximalConsistentFinset 𝓢 Φ) : Consistent 𝓢 Γ := Γ.2.1
@[simp] lemma unprovable_falsum : Γ.1 *⊬[𝓢] ⊥ := Γ.consistent
@[simp, grind] lemma mem_falsum [Entailment.Cl 𝓢] : ⊥ ∉ Γ := not_mem_falsum (consistent Γ)

@[simp] lemma maximal (Γ : ComplementMaximalConsistentFinset 𝓢 Φ) : ComplementMaximal Γ Φ := Γ.2.2.2

@[grind]
lemma mem_compl_of_not_mem (hs : ψ ∈ Φ) : ψ ∉ Γ → -ψ ∈ Γ := by
  intro h;
  rcases Γ.maximal ψ (by assumption) with (h | h);
  . contradiction;
  . assumption;

@[grind]
lemma mem_of_not_mem_compl (hs : ψ ∈ Φ) : -ψ ∉ Γ → ψ ∈ Γ := by grind;

@[grind]
lemma equality_def : Γ₁ = Γ₂ ↔ Γ₁.1 = Γ₂.1 := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Γ₁; cases Γ₂; simp_all;

variable [Entailment.ComplEquiv 𝓢] [Entailment.Cl 𝓢]

theorem lindenbaum {Γ : Finset F} (Γ_consis : Consistent 𝓢 Γ) (X_sub : ComplementSubset Γ Φ)
  : ∃ Γ' : ComplementMaximalConsistentFinset 𝓢 Φ, Γ ⊆ Γ'.1 := by
  obtain ⟨Y, ⟨_, _, _⟩⟩ := exists_consistent_complement_maximal Γ_consis X_sub;
  use ⟨Y, (by assumption), (by assumption)⟩;

noncomputable instance [Entailment.Consistent 𝓢] : Inhabited (ComplementMaximalConsistentFinset 𝓢 Φ) := ⟨lindenbaum (Γ := ∅) (by simp) (by tauto) |>.choose⟩

@[grind]
lemma membership_iff (hξ : φ ∈ Φ) : (φ ∈ Γ) ↔ (Γ *⊢[𝓢] φ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro h₁;
    suffices -φ ∉ Γ by
      apply or_iff_not_imp_right.mp $ ?_;
      . assumption;
      . apply Γ.maximal;
        simpa;
    by_contra hC;
    have h₂ : Γ *⊢[𝓢] -φ := Context.by_axm! hC;
    simpa using O_of_compl h₁ h₂;

@[grind]
lemma mem_verum (h : ⊤ ∈ Φ) : ⊤ ∈ Γ := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[grind]
lemma iff_not_mem_compl (hξ : φ ∈ Φ) : (φ ∈ Γ) ↔ (-φ ∉ Γ) := by
  apply Iff.trans $ membership_iff hξ;
  constructor;
  . intro h₁ h₂;
    replace h₂ : Γ *⊢[𝓢] -φ := Context.by_axm! h₂;
    simpa using O_of_compl h₁ h₂;
  . intro h;
    apply Context.by_axm!;
    simpa using mem_of_not_mem_compl hξ h;

@[grind]
lemma iff_mem_compl (hξ : φ ∈ Φ) : (φ ∉ Γ) ↔ (-φ ∈ Γ) := by simpa using iff_not_mem_compl hξ |>.not;

@[grind]
lemma iff_mem_imp (hφψΦ : (φ ➝ ψ) ∈ Φ) (hφΦ : φ ∈ Φ) (hψΦ : ψ ∈ Φ) : (φ ➝ ψ ∈ Γ) ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  constructor;
  . intro hφψ hφ;
    replace hφψΦ := membership_iff hφψΦ |>.mp hφψ;
    replace hφΦ := membership_iff hφΦ |>.mp hφ;
    apply membership_iff hψΦ |>.mpr;
    exact hφψΦ ⨀ hφΦ;
  . intro hφψ;
    rcases not_or_of_imp hφψ with (hφ | hψ);
    . apply membership_iff hφψΦ |>.mpr;
      apply C_of_N;
      apply neg_of_compl;
      apply Context.by_axm;
      exact mem_compl_of_not_mem hφΦ hφ;
    . apply membership_iff hφψΦ |>.mpr;
      apply C!_of_conseq!;
      apply membership_iff hψΦ |>.mp;
      assumption;

end ComplementMaximalConsistentFinset

end

end CCMF

end LO






namespace LO.InterpretabilityLogic

variable {α : Type*} [DecidableEq α]
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

open Modal (Kripke.Frame Kripke.Model)

namespace Formula

variable {φ ψ χ : Formula α}

@[grind]
def subformulas : Formula α → Finset (Formula α)
  | atom a => {atom a}
  | ⊥      => {⊥}
  | φ ➝ ψ => {φ ➝ ψ} ∪ subformulas φ ∪ subformulas ψ
  | □φ     => {□φ} ∪ subformulas φ
  | φ ▷ ψ  => {φ ▷ ψ} ∪ subformulas φ ∪ subformulas ψ

namespace subformulas

@[simp, grind]
lemma mem_self : φ ∈ φ.subformulas := by induction φ <;> simp_all [subformulas, Finset.mem_union, Finset.mem_singleton]

@[grind ⇒]
lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
lemma mem_box (h : (□ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | hbox ψ ihψ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒]
lemma mem_rhd (h : (ψ ▷ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp ψ χ ihψ ihχ
  | hrhd ψ χ ihψ ihχ => simp_all [subformulas]; grind;
  | _ => simp_all [subformulas];

@[grind ⇒] lemma mem_neg (h : (∼ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas := (mem_imp h).1
@[grind ⇒] lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∨ χ ∈ φ.subformulas := by
  simp only [LukasiewiczAbbrev.or] at h;
  grind;
@[grind ⇒] lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  simp only [LukasiewiczAbbrev.and] at h;
  grind;

end subformulas


def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
instance : Compl (Formula α) where
  compl := complement

end Formula


namespace FormulaFinset

variable {Φ Φ₁ Φ₂ : FormulaFinset α}

class SubformulaClosed (Φ : FormulaFinset α) where
  subfml_closed : ∀ φ ∈ Φ, φ.subformulas ⊆ Φ

namespace SubformulaClosed

variable [Φ.SubformulaClosed]

@[grind ⇒]
lemma mem_imp (h : φ ➝ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  constructor <;>
  . apply SubformulaClosed.subfml_closed _ h;
    simp [Formula.subformulas];

@[grind ⇒]
lemma mem_neg (h : ∼φ ∈ Φ) : φ ∈ Φ := (mem_imp h).1

@[grind ⇒]
lemma mem_and (h : φ ⋏ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  simp only [LukasiewiczAbbrev.and] at h;
  grind;

@[grind ⇒]
lemma mem_or (h : φ ⋎ ψ ∈ Φ) : φ ∈ Φ ∨ ψ ∈ Φ := by
  simp only [LukasiewiczAbbrev.or] at h;
  grind;

@[grind ⇒]
lemma mem_box (h : □φ ∈ Φ) : φ ∈ Φ := by
  apply SubformulaClosed.subfml_closed _ h;
  simp [Formula.subformulas];

@[grind ⇒]
lemma mem_rhd (h : φ ▷ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := by
  constructor <;>
  . apply SubformulaClosed.subfml_closed _ h;
    simp [Formula.subformulas];

end SubformulaClosed


class Adequate (Φ : FormulaFinset α) extends Φ.SubformulaClosed where
  compl_closed : ∀ φ ∈ Φ, -φ ∈ Φ
  mem_top_rhd_top : ⊤ ▷ ⊤ ∈ Φ
  mem_part₁ : ∀ {φ ψ}, (φ ▷ ψ) ∈ Φ → (□-φ) ∈ Φ ∧ (□-ψ) ∈ Φ
  mem_part₂ : ∀ {φ₁ ψ₁ φ₂ ψ₂},
    (φ₁ ▷ ψ₁) ∈ Φ → (φ₂ ▷ ψ₂) ∈ Φ →
    ∀ ξ₁ ∈ [φ₁, ψ₁, φ₂, ψ₂],
    ∀ ξ₂ ∈ [φ₁, ψ₁, φ₂, ψ₂],
    (ξ₁ ▷ ξ₂) ∈ Φ

attribute [simp] Adequate.mem_top_rhd_top

namespace Adequate

variable [Φ.Adequate]

@[grind ⇒] lemma mem_imp (h : φ ➝ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := SubformulaClosed.mem_imp h
@[grind ⇒] lemma mem_box (h : □φ ∈ Φ) : φ ∈ Φ := SubformulaClosed.mem_box h
@[grind ⇒] lemma mem_rhd (h : φ ▷ ψ ∈ Φ) : φ ∈ Φ ∧ ψ ∈ Φ := SubformulaClosed.mem_rhd h

end Adequate



def Consistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := Φ *⊬[𝓢] ⊥
def Inconsistent (𝓢 : S) (Φ : FormulaFinset α) : Prop := ¬Consistent 𝓢 Φ

def Maximal (𝓢 : S) (Φ : FormulaFinset α) := ∀ Ψ, Φ ⊂ Ψ → Inconsistent 𝓢 Ψ

end FormulaFinset

section

def AdequateSet (α) [DecidableEq α] := { Φ : FormulaFinset α // Φ.Adequate }

namespace AdequateSet

variable {Φ : AdequateSet α}

@[grind ⇒] lemma mem_imp (h : φ ➝ ψ ∈ Φ.1) : φ ∈ Φ.1 ∧ ψ ∈ Φ.1 := Φ.2.mem_imp h
@[grind ⇒] lemma mem_box (h : □φ ∈ Φ.1) : φ ∈ Φ.1 := Φ.2.mem_box h
@[grind ⇒] lemma mem_rhd (h : φ ▷ ψ ∈ Φ.1) : φ ∈ Φ.1 ∧ ψ ∈ Φ.1 := Φ.2.mem_rhd h

end AdequateSet


def MaximalConsistentSet (𝓢 : S) (Φ : AdequateSet α) := { Ψ : FormulaFinset α // Ψ ⊆ Φ.1 ∧ Ψ.Maximal 𝓢 ∧ Ψ.Consistent 𝓢 }

variable {Φ} {Γ Δ Θ : MaximalConsistentSet 𝓢 Φ}

structure ILSuccessor (Γ Δ : MaximalConsistentSet 𝓢 Φ) : Prop where
  prop1 : (∀ φ ∈ Γ.1.prebox, φ ∈ Δ.1 ∧ □φ ∈ Δ.1)
  prop2 : (∃ φ ∈ Δ.1.prebox, □φ ∉ Γ.1)
infix:80 " < " => ILSuccessor

structure ILCriticalSuccessor (χ : { χ : Formula α // χ ∈ Φ.1}) (Γ Δ : MaximalConsistentSet 𝓢 Φ) extends Γ < Δ where
  prop3 : ∀ φ, φ ▷ χ.1 ∈ Γ.1 → -φ ∈ Δ.1 ∧ □-φ ∈ Δ.1
notation Γ:max " <[" χ "] " Δ:max => ILCriticalSuccessor χ Γ Δ

lemma claim1 (hΓΔ : Γ <[χ] Δ) (hΔΘ : Δ < Θ) : Γ <[χ] Θ where
  prop1 := by
    intro φ hφ;
    apply hΔΘ.prop1 φ;
    simpa using hΓΔ.prop1 _ hφ |>.2;
  prop2 := by
    rcases hΔΘ.prop2 with ⟨φ, hφ, h⟩;
    use φ;
    constructor;
    . assumption;
    . contrapose! h;
      apply hΓΔ.prop1 φ ?_ |>.2;
      simpa;
  prop3 := by
    intro φ hφ;
    rcases hΓΔ.prop3 φ hφ with ⟨h₁, h₂⟩;
    apply hΔΘ.prop1;
    simpa;

lemma claim3 (h₁ : ∼(φ ▷ χ.1) ∈ Γ.1) : ∃ Δ : MaximalConsistentSet 𝓢 Φ, (Γ <[χ] Δ) ∧ φ ∈ Δ.1 := by
  have : (φ ▷ χ.1) ∈ Φ.1 := Φ.2.compl_closed (∼(φ ▷ χ.1)) $ Γ.2.1 h₁;
  have : □-φ ∈ Φ.1 := Φ.2.mem_part₁ this |>.1;
  have : □-φ ∉ Γ.1 := by
    by_contra hC;
    sorry;
  let Δ₀ : FormulaFinset _ :=
    {φ, □-φ} ∪
    Γ.1.prebox ∪
    Γ.1.prebox.box ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ.1) (by simp)) |>.image (λ ξ => -ξ)) ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ.1) (by simp)) |>.image (λ ξ => □-ξ))
  have Δ₀_consis : Δ₀.Consistent 𝓢 := by sorry;
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : MaximalConsistentSet 𝓢 Φ, Δ₀ ⊆ Δ.1 := by
    sorry;
  use Δ;
  constructor;
  . exact {
      prop1 := by
        intro ψ hψ;
        simp at hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; left; right;
          simpa;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; right;
          simpa;
      prop2 := by
        use (-φ);
        constructor;
        . suffices □-φ ∈ Δ.1 by simpa;
          apply hΔ;
          simp [Δ₀];
        . assumption;
      prop3 := by
        intro ψ hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
    }
  . apply hΔ;
    simp [Δ₀];

lemma claim4 (h₁ : (φ ▷ ψ) ∈ Γ.1) (h₂ : φ ∈ Δ.1) (h₃ : Γ <[χ] Δ)
  : ∃ Δ' : MaximalConsistentSet 𝓢 Φ, (Γ <[χ] Δ') ∧ ψ ∈ Δ'.1 ∧ □(-ψ) ∈ Δ'.1 := by
  have : □-ψ ∉ Γ.1 := by
    by_contra hC;
    sorry;
  let Δ₀ : FormulaFinset _ :=
    {ψ, □-ψ} ∪
    Γ.1.prebox ∪
    Γ.1.prebox.box ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => -ξ)) ∪
    ((Γ.1.preimage (λ ξ => ξ ▷ χ) (by simp)) |>.image (λ ξ => □-ξ))

  have Δ₀_consis : Δ₀.Consistent 𝓢 := by sorry;
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : MaximalConsistentSet 𝓢 Φ, Δ₀ ⊆ Δ.1 := by
    sorry;
  use Δ;
  refine ⟨?_, ?_, ?_⟩;
  . exact {
      prop1 := by
        intro ψ hψ;
        simp at hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; left; right;
          simpa;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; left; right;
          simpa;
      prop2 := by
        use (-ψ);
        constructor;
        . suffices □-ψ ∈ Δ.1 by simpa;
          apply hΔ;
          simp [Δ₀];
        . assumption;
      prop3 := by
        intro ψ hψ;
        constructor;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          left; right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
        . apply hΔ;
          simp only [Finset.mem_union, Δ₀];
          right;
          suffices ∃ ξ, (ξ ▷ χ.1 ∈ Γ.1) ∧ -ξ = -ψ by simpa;
          use ψ;
    }
  . apply hΔ; simp [Δ₀];
  . apply hΔ; simp [Δ₀];

end

open Veltman

namespace Veltman

variable {α : Type*} [DecidableEq α]
variable [Entailment S (Formula ℕ)]
variable {𝓢 : S} {Γ : MaximalConsistentSet 𝓢 Φ}

protected inductive ILMiniCanonicalModel.IsWorld (Γ : MaximalConsistentSet 𝓢 Φ) : MaximalConsistentSet 𝓢 Φ → List { φ // φ ∈ Φ.1 } → Prop
  | i₁              : ILMiniCanonicalModel.IsWorld Γ Γ []
  | i₂ {Δ Δ'} {τ}   : ILMiniCanonicalModel.IsWorld Γ Δ τ → Δ < Δ' → ILMiniCanonicalModel.IsWorld Γ Δ' τ
  | i₃ {Δ Δ'} {τ χ} : ILMiniCanonicalModel.IsWorld Γ Δ τ → Δ <[χ] Δ' → ILMiniCanonicalModel.IsWorld Γ Δ' (τ ++ [χ])

def ILMiniCanonicalModel (Γ : MaximalConsistentSet 𝓢 Φ) : Veltman.Model where
  toKripkeFrame := {
    World := { P : (MaximalConsistentSet 𝓢 Φ) × (List _) // ILMiniCanonicalModel.IsWorld Γ P.1 P.2 }
    world_nonempty := ⟨⟨(Γ, []), ILMiniCanonicalModel.IsWorld.i₁⟩⟩
    Rel X Y := ∃ χ, X.1.1 <[χ] Y.1.1 ∧ (∃ τ, Y.1.2 = X.1.2 ++ [χ] ++ τ)
  }
  S X U V :=
    X ≺ U.1 ∧
    X ≺ V.1 ∧
    (∃ χ, (∃ τ, U.1.1.2 = X.1.2 ++ [χ] ++ τ) ∧ (∃ τ, V.1.1.2 = X.1.2 ++ [χ] ++ τ))
  Val X p := (.atom p) ∈ X.1.1.1

instance : (ILMiniCanonicalModel Γ).IsFiniteGL where
  world_finite := by sorry
  trans X Y Z := by
    rintro ⟨χ₁, RXY, ⟨τ₁, hτ₁⟩⟩ ⟨χ₂, RYZ, ⟨τ₂, hτ₂⟩⟩;
    use χ₁;
    constructor;
    . exact claim1 RXY RYZ.1;
    . use τ₁ ++ [χ₂] ++ τ₂;
      simp [hτ₂, hτ₁];
  irrefl := by
    rintro _ ⟨_, _, ⟨_, hτ⟩⟩;
    simp at hτ;

instance : (ILMiniCanonicalModel Γ).IsIL where
  S_refl X := by
    constructor;
    rintro ⟨U, RXU⟩;
    refine ⟨RXU, RXU, ?_⟩;
    . rcases RXU with ⟨χ, RχXU, ⟨τ, hτ⟩⟩;
      tauto;
  S_trans X := by
    constructor;
    rintro ⟨U, RXU⟩ ⟨V, RXV⟩ ⟨W, RXW⟩ ⟨_, _, ⟨χ₁, ⟨⟨τ₁₁, hτ₁₁⟩, ⟨τ₁₂, hτ₁₂⟩⟩⟩⟩ ⟨_, _, ⟨χ₂, ⟨τ₂₁, hτ₂₁⟩, ⟨τ₂₂, hτ₂₂⟩⟩⟩;
    refine ⟨RXU, RXW, ?_⟩;
    simp_all;
  S_IL := by
    rintro X ⟨U, RXU⟩ ⟨V, RXV⟩ ⟨_, _, ⟨_, _⟩⟩;
    refine ⟨RXU, RXV, ?_⟩;
    rcases RXU with ⟨ξ, _, ⟨_, _⟩⟩;
    use ξ;
    simp_all;

instance : (ILMiniCanonicalModel Γ).IsFiniteIL where

open Formula.Veltman

lemma ILMiniCanonicalModel.truthlemma {X : ILMiniCanonicalModel Γ} (hφ : φ ∈ Φ.1) : X ⊧ φ ↔ φ ∈ X.1.1.1 := by
  induction φ generalizing X with
  | hfalsum => sorry;
  | hatom a => tauto;
  | himp φ ψ ihφ ihψ =>
    suffices φ ∈ X.1.1.1 → ψ ∈ X.1.1.1 ↔ φ ➝ ψ ∈ X.1.1.1 by simpa [Satisfies, (ihφ (X := X) (by grind)), ihψ (X := X) (by grind)];
    sorry;
  | hbox φ ih =>

    have := ih (X := X) (by grind);
    sorry;
  | hrhd φ ψ ihφ ihψ =>
    let ψ : { χ // χ ∈ Φ.1} := ⟨ψ, by grind⟩;
    suffices (∀ U : {V // X ≺ V}, U.1 ⊧ φ → ∃ V : {V // X ≺ V}, (ILMiniCanonicalModel Γ).S X U V ∧ V.1 ⊧ ψ.1) ↔ φ ▷ ψ ∈ X.1.1.1 by tauto
    constructor;
    . contrapose!;
      intro h;
      replace h : ∼(φ ▷ ψ) ∈ X.1.1.1 := by sorry;
      obtain ⟨Δ, hΔ₁, hΔ₂⟩ := claim3 h;
      use ⟨⟨⟨Δ, X.1.2 ++ [ψ]⟩, IsWorld.i₃ X.2 hΔ₁⟩, ⟨ψ, by simpa⟩⟩;
      constructor;
      . apply ihφ (by grind) |>.mpr;
        simpa;
      . rintro V ⟨_, ⟨χ, hχXV, _⟩, h⟩;
        apply ihψ (by grind) |>.not.mpr;
        have := hχXV.prop3 χ (by sorry) |>.1;
        sorry;
    . rintro h ⟨U, ⟨χ, hχXU, τ, eU₂⟩⟩ hU;
      replace hU := ihφ (by grind) |>.mp hU;
      obtain ⟨Δ, hΔ₁, hΔ₂, hΔ₃⟩ := claim4 h hU hχXU;
      use ⟨⟨⟨Δ, X.1.2 ++ [χ]⟩, IsWorld.i₃ X.2 hΔ₁⟩, ⟨χ, by simpa⟩⟩;
      constructor;
      . refine ⟨?_, ?_, ?_⟩;
        . use χ; tauto;
        . use χ; simpa;
        . use χ;
          constructor;
          . use τ;
          . use []; simp;
      . apply ihψ (by grind) |>.mpr;
        simpa;

end Veltman

open Formula.Veltman in
instance IL.Veltman.finite_complete : Complete InterpretabilityLogic.IL Veltman.FrameClass.FiniteIL := by
  constructor;
  intro φ;
  contrapose!
  intro hφ;
  apply not_validOnFrameClass_of_exists_model_world;
  let Φ : AdequateSet ℕ := ⟨{-φ}, by sorry⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : MaximalConsistentSet (InterpretabilityLogic.IL) Φ, {-φ} ⊆ Γ.1 := by sorry;
  use ILMiniCanonicalModel Γ, ⟨⟨Γ, []⟩, ILMiniCanonicalModel.IsWorld.i₁⟩;
  constructor;
  . apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply ILMiniCanonicalModel.truthlemma (by sorry) |>.not.mpr;
    sorry;

end LO.InterpretabilityLogic
