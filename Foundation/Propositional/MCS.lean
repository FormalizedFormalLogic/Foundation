/-
  Maximal consistent set for propositional classical logic
-/
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Meta.ClProver

section

open LO LO.Entailment LO.Entailment.Context

variable {F} [DecidableEq F] [LogicalConnective F]
         {S} [Entailment S F]
variable {𝓢 : S} {Γ Δ : Set F} {φ ψ : F}

namespace Set.LO

def Consistent (𝓢 : S) (Γ : Set F) : Prop := Γ *⊬[𝓢] ⊥

def Inconsistent (𝓢 : S) (Γ : Set F) : Prop := ¬(Consistent 𝓢 Γ)

def Maximal (𝓢 : S) (Γ : Set F) : Prop := ∀ Δ, Γ ⊂ Δ → Inconsistent 𝓢 Δ


lemma def_consistent [Entailment.Minimal 𝓢] : Consistent 𝓢 Γ ↔ ∀ Δ : Finset F, (↑Δ ⊆ Γ) → Δ *⊬[𝓢] ⊥ := by
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

lemma def_inconsistent [Entailment.Minimal 𝓢] : Inconsistent 𝓢 Γ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ (Δ *⊢[𝓢] ⊥) := by
  rw [Inconsistent, def_consistent];
  push_neg;
  simp;

omit [DecidableEq F] in
@[grind]
lemma iff_maximal_no_proper_consistent_superset : Maximal 𝓢 Γ ↔ (∀ Δ, Consistent 𝓢 Δ → Γ ⊆ Δ → Δ = Γ) := by
  dsimp [Maximal, Inconsistent];
  grind;

section

variable [Entailment.Cl 𝓢]

@[simp]
lemma empty_consistent [consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ∅ := by
  obtain ⟨φ, hφ⟩ := consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Δ hΔ;
  rw [(show Δ = ∅ by simpa [Set.subset_empty_iff, Finset.coe_eq_empty] using hΔ)];
  contrapose! hφ;
  apply Context.emptyPrf!
  apply of_O!;
  simp_all;

@[grind]
lemma not_mem_falsum_of_consistent (Γ_consis : Consistent 𝓢 Γ) : ⊥ ∉ Γ := by
  contrapose! Γ_consis;
  suffices Γ *⊢[𝓢] ⊥ by simpa [Consistent];
  apply Context.by_axm!;
  simpa;

@[grind]
lemma not_mem_neg_of_mem_of_consistent (Γ_consis : Consistent 𝓢 Γ) (h : φ ∈ Γ) : ∼φ ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . grind;

@[grind]
lemma not_mem_of_mem_neg_of_consistent (Γ_consis : Consistent 𝓢 Γ) (h : ∼φ ∈ Γ) : φ ∉ Γ := by
  by_contra hC;
  apply def_consistent.mp Γ_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . grind;

lemma iff_insert_consistent : Consistent 𝓢 (insert φ Γ) ↔ ∀ Δ : Finset F, ↑Δ ⊆ Γ → Δ *⊬[𝓢] φ ➝ ⊥ := by
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
    apply Context.deduct!;
    apply Context.weakening! (Γ := Γ);
    . simp;
    . assumption;

lemma iff_inconsistent_insert : Inconsistent 𝓢 (insert φ Γ) ↔ ∃ Δ : Finset F, ↑Δ ⊆ Γ ∧ Δ *⊢[𝓢] φ ➝ ⊥ := by
  rw [Inconsistent, iff_insert_consistent]
  push_neg;
  simp;

lemma iff_inconsistent_insert_provable_neg : Inconsistent 𝓢 (insert φ Γ) ↔ Γ *⊢[𝓢] ∼φ := by
  apply Iff.trans iff_inconsistent_insert;
  constructor;
  . rintro ⟨Δ, hΓΔ, hΔ⟩;
    apply N!_iff_CO!.mpr;
    apply weakening! hΓΔ hΔ;
  . intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff_finset.mp h;
    use Δ;
    constructor;
    . tauto;
    . apply N!_iff_CO!.mp;
      assumption;

lemma iff_inconsistent_insert_neg_provable : Inconsistent 𝓢 (insert (∼φ) Γ) ↔ Γ *⊢[𝓢] φ := by
  apply Iff.trans iff_inconsistent_insert_provable_neg;
  constructor <;> . intro h; cl_prover [h];

lemma iff_consistent_insert_neg_unprovable : Consistent 𝓢 (insert (∼φ) Γ) ↔ Γ *⊬[𝓢] φ := by
  simpa [Inconsistent] using iff_inconsistent_insert_neg_provable.not;

lemma iff_consistent_neg_singleton_unprovable : Consistent 𝓢 ({∼φ}) ↔ 𝓢 ⊬ φ := by
  rw [(show {∼φ} = insert (∼φ) ∅ by simp), iff_consistent_insert_neg_unprovable];
  apply Context.provable_iff_provable.not.symm;


lemma or_consistent_insert_consistent_insert_neg (T_consis : Consistent 𝓢 T) (φ) :
  Consistent 𝓢 (insert φ T) ∨ Consistent 𝓢 (insert (∼φ) T) := by
  by_contra! hC;
  obtain ⟨hC₁, hC₂⟩ := hC;
  obtain ⟨Δ₁, hΔ₁Γ, hΔ₁⟩ := iff_inconsistent_insert.mp $ by simpa using hC₁;
  obtain ⟨Δ₂, hΔ₂Γ, hΔ₂⟩ := iff_inconsistent_insert.mp $ by simpa using hC₂;
  apply def_consistent.mp T_consis (Δ₁ ∪ Δ₂);
  . grind;
  . replace hΔ₁ : ↑(Δ₁ ∪ Δ₂) *⊢[𝓢] φ ➝ ⊥ := Context.weakening! (by simp) hΔ₁;
    replace hΔ₂ : ↑(Δ₁ ∪ Δ₂) *⊢[𝓢] ∼φ ➝ ⊥ := Context.weakening! (by simp) hΔ₂;
    exact of_C!_of_C!_of_A! hΔ₁ hΔ₂ (by simp);

lemma exists_consistent_maximal_of_consistent (Γ_consis : Consistent 𝓢 Γ)
  : ∃ Δ, Γ ⊆ Δ ∧ Consistent 𝓢 Δ ∧ ∀ U, Consistent 𝓢 U → Δ ⊆ U → U = Δ := by
  obtain ⟨Δ, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { Γ | Consistent 𝓢 Γ} (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Set.mem_setOf_eq];
    constructor;
    . apply def_consistent.mpr;
      intro Γ hΓ;
      by_contra hC;
      obtain ⟨U, hUc, hUs⟩ := Set.subset_mem_chain_of_finite c hnc chain (s := ↑Γ.toSet) (by simp) $ by
        intro φ hφ;
        apply hΓ hφ;
      have : Consistent 𝓢 U := hc hUc;
      have : Inconsistent 𝓢 U := by
        apply def_inconsistent.mpr;
        use Γ;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) Γ Γ_consis;
  use Δ;
  refine ⟨?_, ?_, ?_⟩;
  . assumption;
  . assumption;
  . intro U hU hZU;
    apply Set.eq_of_subset_of_subset;
    . exact h₃ hU hZU;
    . assumption;

end

end Set.LO


namespace LO

open Set.LO

abbrev MaximalConsistentSet (𝓢 : S) := { Γ // Consistent 𝓢 Γ ∧ Maximal 𝓢 Γ }

namespace MaximalConsistentSet

variable {Γ Δ Γ₁ Γ₂ : MaximalConsistentSet 𝓢}

instance : Membership F (MaximalConsistentSet 𝓢) := ⟨λ Γ φ => φ ∈ Γ.1⟩

omit [DecidableEq F] in @[simp] lemma consistent (Γ : MaximalConsistentSet 𝓢) : Consistent 𝓢 Γ := Γ.2.1

omit [DecidableEq F] in lemma maximal (Γ : MaximalConsistentSet 𝓢) : Maximal 𝓢 Γ := Γ.2.2

omit [DecidableEq F] in
lemma no_proper_consistent_superset (Γ : MaximalConsistentSet 𝓢) : ∀ Δ, Consistent 𝓢 Δ → Γ.1 ⊆ Δ → Δ = Γ.1 := by
  apply iff_maximal_no_proper_consistent_superset.mp;
  exact Γ.maximal;


variable [Entailment.Cl 𝓢]

lemma exists_of_consistent {Γ : Set F} (Γ_consis : Consistent 𝓢 Γ) : ∃ Δ : MaximalConsistentSet 𝓢, (Γ ⊆ Δ.1) := by
  have ⟨Γ, _⟩ := exists_consistent_maximal_of_consistent Γ_consis;
  use ⟨Γ, ?_⟩ <;> grind;

alias lindenbaum := exists_of_consistent


instance [Entailment.Consistent 𝓢] : Nonempty (MaximalConsistentSet 𝓢) := ⟨lindenbaum empty_consistent |>.choose⟩

@[grind]
lemma or_mem_mem_neg (φ) : φ ∈ Γ ∨ ∼φ ∈ Γ := by
  by_contra! hC;
  rcases or_consistent_insert_consistent_insert_neg Γ.consistent φ with h | h;
  . apply hC.1; simpa using Γ.no_proper_consistent_superset _ h (by simp);
  . apply hC.2; simpa using Γ.no_proper_consistent_superset _ h (by simp);

lemma iff_mem_provable : φ ∈ Γ ↔ Γ.1 *⊢[𝓢] φ := by
  constructor;
  . intro h;
    apply Context.by_axm!;
    simpa;
  . intro hφ;
    suffices ∼φ ∉ Γ.1 by apply or_iff_not_imp_right.mp $ (or_mem_mem_neg φ); assumption;
    by_contra hnφ;
    apply Γ.consistent;
    replace hnφ : Γ.1 *⊢[𝓢] ∼φ := Context.by_axm! hnφ;
    cl_prover [hφ, hnφ];

@[simp, grind] lemma not_mem_falsum : ⊥ ∉ Γ := not_mem_falsum_of_consistent Γ.consistent
@[simp, grind] lemma mem_verum : ⊤ ∈ Γ := by apply iff_mem_provable.mpr; cl_prover;

@[grind]
lemma iff_mem_neg : (∼φ ∈ Γ) ↔ (φ ∉ Γ) := by
  simp only [iff_mem_provable];
  constructor;
  . intro hnφ hφ;
    apply Γ.consistent;
    cl_prover [hφ, hnφ];
  . intro hφ;
    apply Context.by_axm!;
    simpa using Γ.no_proper_consistent_superset _ (iff_consistent_insert_neg_unprovable.mpr hφ) (by tauto);

lemma iff_forall_mem_provable : (∀ Γ : MaximalConsistentSet 𝓢, φ ∈ Γ) ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose!;
    intro h;
    obtain ⟨Γ, hΓ⟩ := lindenbaum $ iff_consistent_neg_singleton_unprovable.mpr h;
    use Γ;
    apply iff_mem_neg.mp;
    simpa using hΓ;
  . intro h Γ;
    apply iff_mem_provable.mpr;
    exact Context.of! h;

@[grind] lemma mem_of_provable (h : 𝓢 ⊢ φ) : φ ∈ Γ := iff_forall_mem_provable.mpr h Γ

@[grind] lemma iff_mem_negneg : (∼∼φ ∈ Γ) ↔ (φ ∈ Γ) := by grind

@[grind ⇒]
lemma iff_mem_imp : ((φ ➝ ψ) ∈ Γ) ↔ ((φ ∈ Γ) → (ψ ∈ Γ)) := by
  constructor;
  . intro hφψ hφ;
    simp_all only [iff_mem_provable]
    cl_prover [hφψ, hφ];
  . intro h;
    rcases imp_iff_not_or.mp h with (h | h);
    . replace h := iff_mem_provable.mp $ iff_mem_neg.mpr h;
      apply iff_mem_provable.mpr;
      cl_prover [h];
    . replace h := iff_mem_provable.mp h;
      apply iff_mem_provable.mpr;
      cl_prover [h];


@[grind]
lemma mdp (hφψ : (φ ➝ ψ) ∈ Γ) (hφ : φ ∈ Γ) : ψ ∈ Γ := iff_mem_imp.mp hφψ hφ

@[grind ⇒]
lemma iff_mem_and : ((φ ⋏ ψ) ∈ Γ) ↔ (φ ∈ Γ) ∧ (ψ ∈ Γ) := by
  constructor;
  . intro hφψ;
    simp_all only [iff_mem_provable];
    constructor <;> cl_prover [hφψ];
  . simp_all only [iff_mem_provable];
    rintro ⟨hφ, hψ⟩;
    cl_prover [hφ, hψ];

@[grind ⇒]
lemma iff_mem_or : ((φ ⋎ ψ) ∈ Γ) ↔ (φ ∈ Γ) ∨ (ψ ∈ Γ) := by
  constructor;
  . intro hφψ;
    replace hφψ := iff_mem_provable.mp hφψ;
    by_contra!;
    rcases this with ⟨hφ, hψ⟩;
    replace hφ := iff_mem_provable.mp $ iff_mem_neg.mpr hφ;
    replace hψ := iff_mem_provable.mp $ iff_mem_neg.mpr hψ;
    apply Γ.consistent;
    cl_prover [hφψ, hφ, hψ];
  . simp_all only [iff_mem_provable];
    rintro (h | h) <;> cl_prover [h];

@[grind]
lemma iff_mem_conj {l : List F} : (⋀l ∈ Γ) ↔ (∀ φ ∈ l, φ ∈ Γ) := by simp [iff_mem_provable, Conj₂!_iff_forall_provable];

lemma imp_of_provable_C (hφψ : Γ *⊢[𝓢] (φ ➝ ψ)) : (φ ∈ Γ) → (ψ ∈ Γ) := by
  apply iff_mem_imp.mp;
  apply iff_mem_provable.mpr;
  assumption;

lemma iff_of_provable_E (h : Γ *⊢[𝓢] (φ ⭤ ψ)) : φ ∈ Γ ↔ ψ ∈ Γ := by
  constructor <;> . apply imp_of_provable_C; cl_prover [h];

@[grind ⇒] lemma neg_monotone (h : φ ∈ Γ → ψ ∈ Γ) : (∼ψ ∈ Γ) → (∼φ ∈ Γ) := by simp only [iff_mem_neg]; grind;

@[grind ⇒] lemma neg_congruence (h : φ ∈ Γ ↔ ψ ∈ Γ) : (∼φ ∈ Γ) ↔ (∼ψ ∈ Γ) := by grind;

end MaximalConsistentSet

end LO

end
