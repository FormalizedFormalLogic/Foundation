/-
  Complement maximal consistent finset for propositional logic
-/
import Foundation.Logic.HilbertStyle.Supplemental

section

open LO

variable {F} [LogicalConnective F]
         {S} [Entailment S F]
variable {𝓢 : S} {Γ Δ : Finset F} {φ ψ : F} {Φ : Finset F}


namespace LO

class Compl (F : Type*) where
  compl : F → F

prefix:120 "-" => Compl.compl

namespace Entailment

class ComplEquiv [LogicalConnective F] [Compl F] (𝓢 : S) where
  compl_equiv! {φ : F} : 𝓢 ⊢! ∼φ ⭤ -φ
export ComplEquiv (compl_equiv!)

@[simp] lemma compl_equiv {φ : F} [Compl F] [ComplEquiv 𝓢] : 𝓢 ⊢ ∼φ ⭤ -φ := ⟨compl_equiv!⟩

section

variable [Compl F] [Entailment.Minimal 𝓢] [Entailment.ComplEquiv 𝓢]

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

end Entailment

end LO



open LO.Entailment LO.Entailment.Context

namespace Finset.LO

variable [DecidableEq F]

def Consistent (𝓢 : S) (Γ : Finset F) : Prop := Γ *⊬[𝓢] ⊥

def Inconsistent (𝓢 : S) (Γ : Finset F) : Prop := ¬(Consistent 𝓢 Γ)

def ComplementBounded [Compl F] (Γ Φ : Finset F) : Prop := Γ ⊆ (Φ ∪ Φ.image (-·))

/-- For every `φ` in `Δ`, `φ` or `-φ` is in `Γ` -/
def ComplementMaximal [Compl F] (Γ Φ : Finset F) : Prop := ∀ φ ∈ Φ, φ ∈ Γ ∨ -φ ∈ Γ


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

lemma def_inconsistent [Entailment.Minimal 𝓢] : Inconsistent 𝓢 Γ ↔ ∃ Δ : Finset F, (Δ ⊆ Γ) ∧ (Δ *⊢[𝓢] ⊥) := by
  rw [Inconsistent, def_consistent];
  push_neg;
  simp;


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

section

variable [Compl F] [ComplEquiv 𝓢]

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

end


namespace exists_consistent_complement_closed

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

end exists_consistent_complement_closed

open exists_consistent_complement_closed in
theorem exists_consistent_complement_closed [Compl F] [ComplEquiv 𝓢] [Entailment.Cl 𝓢] (Γ_consis : Consistent 𝓢 Γ)
  : ∃ Γ', (Γ ⊆ Γ') ∧ (Consistent 𝓢 Γ') ∧ (ComplementMaximal Γ' Φ) := by
  use enum 𝓢 Γ Φ.toList;
  refine ⟨?_, ?_, ?_⟩;
  . simp;
  . grind;
  . intro φ hφ;
    apply of_mem_seed;
    simpa;

end Finset.LO




namespace LO

open Finset.LO

variable [Compl F] {Φ : Finset F}

abbrev ComplementMaximalConsistentFinset (𝓢 : S) (Φ : Finset F) := { Γ : Finset F // (Consistent 𝓢 Γ) ∧ (ComplementMaximal Γ Φ) }

variable {Γ Γ₁ Γ₂ Δ : ComplementMaximalConsistentFinset 𝓢 Φ} {φ ψ : F}

namespace ComplementMaximalConsistentFinset

instance : Membership (F) (ComplementMaximalConsistentFinset 𝓢 Φ) := ⟨λ X φ => φ ∈ X.1⟩

@[simp] lemma consistent (Γ : ComplementMaximalConsistentFinset 𝓢 Φ) : Consistent 𝓢 Γ := Γ.2.1
@[simp] lemma unprovable_falsum : Γ.1 *⊬[𝓢] ⊥ := Γ.consistent
@[simp, grind] lemma mem_falsum [DecidableEq F] [Entailment.Cl 𝓢] : ⊥ ∉ Γ := not_mem_falsum (consistent Γ)

@[simp] lemma maximal (Γ : ComplementMaximalConsistentFinset 𝓢 Φ) : ComplementMaximal Γ Φ := Γ.2.2

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

theorem lindenbaum [DecidableEq F] {Γ : Finset F} (Γ_consis : Consistent 𝓢 Γ)
  : ∃ Γ' : ComplementMaximalConsistentFinset 𝓢 Φ, Γ ⊆ Γ'.1 := by
  obtain ⟨Γ', ⟨_, _⟩⟩ := exists_consistent_complement_closed Γ_consis;
  use ⟨Γ', ?_⟩;
  assumption;

noncomputable instance [DecidableEq F] [Entailment.Consistent 𝓢] : Inhabited (ComplementMaximalConsistentFinset 𝓢 Φ) := ⟨lindenbaum (Γ := ∅) (by simp) |>.choose⟩

variable [DecidableEq F]

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

end LO

end
