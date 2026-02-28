module

public import Foundation.Modal.Formula.Basic
public import Foundation.Modal.Entailment.K
public import Foundation.Meta.ClProver
public import Foundation.Vorspiel.Set.Basic

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

namespace FormulaSet

variable [DecidableEq α]
variable {T : FormulaSet α}

-- abbrev Consistent (𝓢 : Hilbert α) (T : FormulaSet α) := T *⊬[𝓢] ⊥

abbrev Consistent (𝓢 : S) (T : FormulaSet α) := T *⊬[𝓢] ⊥

abbrev Inconsistent (𝓢 : S) (T : FormulaSet α) := ¬(Consistent 𝓢 T)

lemma def_consistent [Entailment.Minimal 𝓢] : Consistent 𝓢 T ↔ ∀ Γ : FormulaFinset _, (Γ.toSet ⊆ T) → Γ *⊬[𝓢] ⊥ := by
  constructor;
  . intro h Γ hΓ;
    have := Context.provable_iff_finset.not.mp h;
    push_neg at this;
    exact this Γ (by tauto);
  . intro h;
    apply Context.provable_iff_finset.not.mpr;
    push_neg;
    simpa using h;

lemma def_inconsistent [Entailment.Minimal 𝓢] : Inconsistent 𝓢 T ↔ ∃ (Γ : FormulaFinset _), (Γ.toSet ⊆ T) ∧ Γ *⊢[𝓢] ⊥ := by
  unfold Inconsistent;
  apply not_iff_not.mp;
  push_neg;
  exact def_consistent;

lemma union_consistent [Entailment.Minimal 𝓢] : Consistent 𝓢 (T₁ ∪ T₂) → (Consistent 𝓢 T₁) ∧ (Consistent 𝓢 T₂) := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> {
    apply def_consistent.mpr;
    intro Γ hΓ;
    exact h Γ $ by tauto_set;
  }

variable [Entailment.Cl 𝓢]

lemma emptyset_consistent [H_consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ∅ := by
  obtain ⟨f, hf⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ;
  replace hΓ : Γ = ∅ := by simpa [Set.subset_empty_iff, Finset.coe_eq_empty] using hΓ;
  subst hΓ;
  by_contra hC;
  apply hf;
  apply Context.emptyPrf!;
  apply of_O!;
  simpa using hC;

lemma not_mem_of_mem_neg (T_consis : Consistent 𝓢 T) (h : ∼φ ∈ T) : φ ∉ T := by
  by_contra hC;
  apply def_consistent.mp T_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    tauto;

lemma not_mem_neg_of_mem (T_consis : Consistent 𝓢 T) (h : φ ∈ T) : ∼φ ∉ T := by
  by_contra hC;
  apply def_consistent.mp T_consis {φ, ∼φ} ?_;
  . apply Context.bot_of_mem_neg (φ := φ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    tauto;

lemma iff_insert_consistent : Consistent 𝓢 (insert φ T) ↔ ∀ {Γ : FormulaFinset α}, (↑Γ ⊆ T) → Γ *⊬[𝓢] φ ➝ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    have := def_consistent.mp h (insert φ Γ) ?_;
    . revert this;
      contrapose!;
      simp only [Finset.coe_insert];
      intro h;
      exact Context.deductInv! h;
    . simpa using Set.insert_subset_insert hΓ;
  . intro h;
    apply def_consistent.mpr;
    intro Γ hΓ;
    have := @h (Γ.erase φ) ?_;
    . revert this;
      contrapose!;
      simp only [Finset.coe_erase];
      intro h;
      apply Context.deduct!;
      apply Context.weakening! (Γ := Γ) ?_ h;
      simp;
    . simp_all;

lemma iff_insert_inconsistent : Inconsistent 𝓢 (insert φ T) ↔ ∃ Γ : FormulaFinset _, (Γ.toSet ⊆ T) ∧ Γ *⊢[𝓢] φ ➝ ⊥ := by
  unfold Inconsistent;
  apply not_iff_not.mp;
  push_neg;
  exact iff_insert_consistent;

lemma provable_iff_insert_neg_not_consistent : Inconsistent 𝓢 (insert (∼φ) T) ↔ T *⊢[𝓢] φ := by
  constructor;
  . intro h;
    apply Context.provable_iff_finset.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    use Γ;
    constructor;
    . tauto;
    . exact of_NN! $ N!_iff_CO!.mp hΓ₂;
  . intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff_finset.mp h;
    use Γ;
    constructor;
    . tauto;
    . apply N!_iff_CO!.mp;
      apply dni'!;
      assumption;

lemma unprovable_iff_insert_neg_consistent : Consistent 𝓢 (insert (∼φ) T) ↔ T *⊬[𝓢] φ := by
  simpa [not_not] using provable_iff_insert_neg_not_consistent.not;

lemma unprovable_iff_singleton_neg_consistent : Consistent 𝓢 {∼φ} ↔ 𝓢 ⊬ φ:= by
  apply Iff.trans (by simpa using unprovable_iff_insert_neg_consistent (T := ∅))
  apply Context.provable_iff_provable.not.symm;

lemma neg_provable_iff_insert_not_consistent : Inconsistent 𝓢 (insert (φ) T) ↔ T *⊢[𝓢] ∼φ := by
  constructor;
  . intro h;
    apply Context.provable_iff_finset.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    use Γ;
    constructor;
    . assumption;
    . apply N!_iff_CO!.mpr hΓ₂;
  . intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff_finset.mp h;
    use Γ;
    constructor;
    . assumption;
    . apply N!_iff_CO!.mp;
      assumption;

lemma neg_unprovable_iff_insert_consistent : Consistent 𝓢 (insert (φ) T) ↔ T *⊬[𝓢] ∼φ := by
  simpa [not_not] using neg_provable_iff_insert_not_consistent.not;

lemma unprovable_iff_singleton_consistent : Consistent 𝓢 {φ} ↔ 𝓢 ⊬ ∼φ := by
  have e : insert (φ) ∅ = ({φ} : FormulaSet α) := by aesop;
  have h₂ := neg_unprovable_iff_insert_consistent (𝓢 := 𝓢) (T := ∅) (φ := φ);
  rw [e] at h₂;
  suffices 𝓢 ⊬ ∼φ ↔ ∅ *⊬[𝓢] ∼φ by tauto;
  exact Context.provable_iff_provable.not;

/-
omit [DecidableEq α] in
lemma unprovable_falsum (T_consis : T.Consistent 𝓢) : Consistent 𝓢 := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, _⟩ := Context.provable_iff.mp $ hC;
  have : Γ ⊬[𝓢] ⊥ := (def_consistent.mp T_consis) _ hΓ₁;
  contradiction;
-/

lemma unprovable_either (T_consis : Consistent 𝓢 T) : ¬(T *⊢[𝓢] φ ∧ T *⊢[𝓢] ∼φ) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have := neg_mdp hC₂ hC₁;
  contradiction;

lemma not_mem_falsum_of_consistent (T_consis : Consistent 𝓢 T) : ⊥ ∉ T := by
  by_contra hC;
  apply def_consistent.mp T_consis {⊥};
  . simpa using hC;
  . apply Context.by_axm!;
    simp;

lemma not_singleton_consistent [Entailment.Necessitation 𝓢] (T_consis : Consistent 𝓢 T) (h : ∼□φ ∈ T) : Consistent 𝓢 {∼φ} := by
  apply def_consistent.mpr;
  intro Γ hΓ;
  rcases (Set.subset_singleton_iff_eq.mp hΓ) with hΓ | hΓ;
  . by_contra! hC;
    apply T_consis;
    apply Context.weakening! _ hC;
    simp [hΓ];
  . by_contra! hC;
    apply def_consistent.mp T_consis (Γ := {∼(□φ)}) $ by simpa;
    have : 𝓢 ⊢ ∼φ ➝ ⊥ := by
      apply Context.provable_iff_provable.mpr;
      apply Context.deduct!;
      simpa [hΓ] using hC;
    have : 𝓢 ⊢ φ := by cl_prover [this];
    have : 𝓢 ⊢ □φ := nec! this;
    have : 𝓢 ⊢ ∼□φ ➝ ⊥ := by cl_prover [this];
    simpa using Context.deductInv! $ Context.provable_iff_provable.mp this;

lemma either_consistent (T_consis : Consistent 𝓢 T) (φ) : Consistent 𝓢 (insert φ T) ∨ Consistent 𝓢 (insert (∼φ) T) := by
  by_contra! hC;
  obtain ⟨hC₁, hC₂⟩ := hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp $ by simpa using hC₁;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_inconsistent.mp $ by simpa using hC₂;
  apply def_consistent.mp T_consis (Γ := Γ ∪ Δ) ?_;
  . replace hΓ₂ : ↑(Γ ∪ Δ) *⊢[𝓢] φ ➝ ⊥ := Context.weakening! (by simp) hΓ₂;
    replace hΔ₂ : ↑(Γ ∪ Δ) *⊢[𝓢] ∼φ ➝ ⊥ := Context.weakening! (by simp) hΔ₂;
    exact of_C!_of_C!_of_A! hΓ₂ hΔ₂ (by simp);
  . simp_all;

open Classical in
lemma intro_union_consistent(h : ∀ {Γ₁ Γ₂ : FormulaFinset _}, (Γ₁.toSet ⊆ T₁) → (Γ₂.toSet ⊆ T₂) → (Γ₁ ∪ Γ₂) *⊬[𝓢] ⊥)
  : Consistent 𝓢 (T₁ ∪ T₂) := by
  apply def_consistent.mpr;
  intro Δ hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  apply not_imp_not.mpr $ Context.weakening! (𝓢 := 𝓢) (Γ := Δ) (Δ := Δ₁ ∪ Δ₂) (φ := ⊥) ?_;
  . have := @h Δ₁ Δ₂ ?_ ?_;
    . simpa using this;
    . intro φ; simp [Δ₁];
    . intro φ; simp [Δ₂];
  . intro φ hφ;
    have : φ ∈ T₁ ∪ T₂ := hΔ hφ;
    simp_all [Δ₁, Δ₂];
    grind;

lemma exists_consistent_maximal_of_consistent (T_consis : Consistent 𝓢 T)
  : ∃ Z, Consistent 𝓢 Z ∧ T ⊆ Z ∧ ∀ U, U *⊬[𝓢] ⊥ → Z ⊆ U → U = Z := by
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { T : FormulaSet α | Consistent 𝓢 T} (by
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
  ) T T_consis;
  use Z;
  simp_all only [Set.mem_setOf_eq, Set.le_eq_subset, true_and];
  constructor;
  . assumption;
  . intro U hU hZU;
    apply Set.eq_of_subset_of_subset;
    . exact h₃ hU hZU;
    . assumption;

protected alias lindenbaum := exists_consistent_maximal_of_consistent

end FormulaSet

open FormulaSet

abbrev MaximalConsistentSet (𝓢 : S) := { T : FormulaSet α // (Consistent 𝓢 T) ∧ (∀ {U}, T ⊂ U → Inconsistent 𝓢 U)}

namespace MaximalConsistentSet

variable {Ω Ω₁ Ω₂ : MaximalConsistentSet 𝓢}
variable {φ : Formula α}

instance : Membership (Formula α) (MaximalConsistentSet 𝓢) := ⟨λ Ω φ => φ ∈ Ω.1⟩

lemma consistent (Ω : MaximalConsistentSet 𝓢) : Consistent 𝓢 Ω.1 := Ω.2.1

lemma maximal (Ω : MaximalConsistentSet 𝓢) : Ω.1 ⊂ U → Inconsistent 𝓢 U := Ω.2.2

lemma maximal' (Ω : MaximalConsistentSet 𝓢) {φ : Formula α} (hp : φ ∉ Ω) : Inconsistent 𝓢 (insert φ Ω.1) := Ω.maximal (Set.ssubset_insert hp)

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

variable [DecidableEq α] [Entailment.Cl 𝓢]

lemma exists_of_consistent (consisT : Consistent 𝓢 T) : ∃ Ω : MaximalConsistentSet 𝓢, (T ⊆ Ω.1) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := FormulaSet.lindenbaum consisT;
  use ⟨Ω, ?_, ?_⟩;
  . assumption;
  . rintro U ⟨hU₁, _⟩;
    by_contra hC;
    have := hΩ₃ U hC $ hU₁;
    subst this;
    simp_all;

alias lindenbaum := exists_of_consistent

instance [Entailment.Consistent 𝓢] : Nonempty (MaximalConsistentSet 𝓢) := ⟨lindenbaum emptyset_consistent |>.choose⟩

lemma either_mem (Ω : MaximalConsistentSet 𝓢) (φ) : φ ∈ Ω ∨ ∼φ ∈ Ω := by
  by_contra hC;
  push_neg at hC;
  rcases either_consistent (𝓢 := 𝓢) (Ω.consistent) φ;
  . have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  . have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma membership_iff : (φ ∈ Ω) ↔ (Ω.1 *⊢[𝓢] φ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ∼φ ∉ Ω.1 by apply or_iff_not_imp_right.mp $ (either_mem Ω φ); assumption;
    by_contra hC;
    have hnp : Ω.1 *⊢[𝓢] ∼φ := Context.by_axm! hC;
    have : Ω.1 *⊢[𝓢] ⊥ := neg_mdp hnp hp;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω := not_mem_falsum_of_consistent Ω.consistent

@[simp]
lemma mem_verum : ⊤ ∈ Ω := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma iff_mem_neg : (∼φ ∈ Ω) ↔ (φ ∉ Ω) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.1 *⊢[𝓢] ⊥ := neg_mdp hnp hp;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;
  . intro hp;
    have : Consistent 𝓢 (insert (∼φ) Ω.1) := by
      haveI := provable_iff_insert_neg_not_consistent.not.mpr $ membership_iff.not.mp hp;
      unfold FormulaSet.Inconsistent at this;
      push_neg at this;
      exact this;
    have := not_imp_not.mpr (@maximal (Ω := Ω) (U := insert (∼φ) Ω.1)) (by simpa);
    have : insert (∼φ) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    apply this;
    tauto_set;

lemma iff_forall_mem_provable : (∀ Ω : MaximalConsistentSet 𝓢, φ ∈ Ω) ↔ 𝓢 ⊢ φ := by
  constructor;
  . contrapose!;
    intro h;
    obtain ⟨Ω, hΩ⟩ := lindenbaum $ unprovable_iff_singleton_neg_consistent.mpr h;
    use Ω;
    apply iff_mem_neg.mp;
    tauto;
  . intro h Ω;
    apply membership_iff.mpr;
    exact Context.of! h;

@[grind]
lemma mem_of_prove (h : 𝓢 ⊢ φ) : φ ∈ Ω := by apply iff_forall_mem_provable.mpr h;

@[simp]
lemma iff_mem_negneg : (∼∼φ ∈ Ω) ↔ (φ ∈ Ω) := by simp;

@[simp, grind]
lemma iff_mem_imp : ((φ ➝ ψ) ∈ Ω) ↔ (φ ∈ Ω) → (ψ ∈ Ω) := by
  constructor;
  . intro hpq hp;
    replace dpq := membership_iff.mp hpq;
    replace dp  := membership_iff.mp hp;
    apply membership_iff.mpr;
    exact dpq ⨀ dp;
  . intro h;
    replace h : φ ∉ Ω.1 ∨ ψ ∈ Ω := or_iff_not_imp_left.mpr (by simpa using h);
    cases h with
    | inl h =>
      apply membership_iff.mpr;
      exact C_of_N $ membership_iff.mp $ iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact implyK! ⨀ (membership_iff.mp h)

lemma mdp (hφψ : φ ➝ ψ ∈ Ω) (hψ : φ ∈ Ω) : ψ ∈ Ω := iff_mem_imp.mp hφψ hψ

lemma mdp_provable (hφψ : 𝓢 ⊢ φ ➝ ψ) (hψ : φ ∈ Ω) : ψ ∈ Ω := mdp (mem_of_prove hφψ) hψ

@[simp]
lemma iff_mem_and : ((φ ⋏ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∧ (ψ ∈ Ω) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    constructor;
    . apply membership_iff.mpr; exact K!_left hpq;
    . apply membership_iff.mpr; exact K!_right hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact K!_intro (membership_iff.mp hp) (membership_iff.mp hq);

@[simp]
lemma iff_mem_or : ((φ ⋎ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∨ (ψ ∈ Ω) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC;
    push_neg at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp $ iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp $ iff_mem_neg.mpr hq;
    have : Ω.1 *⊢[𝓢] ⊥ := of_C!_of_C!_of_A! (N!_iff_CO!.mp hp) (N!_iff_CO!.mp hq) hpq;
    have : Ω.1 *⊬[𝓢] ⊥ := Ω.consistent;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact A!_intro_left (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact A!_intro_right (membership_iff.mp hq);

lemma iff_congr : (Ω.1 *⊢[𝓢] (φ ⭤ ψ)) → ((φ ∈ Ω) ↔ (ψ ∈ Ω)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ K!_left hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ K!_right hpq) hq;

lemma intro_equality {h : ∀ φ, φ ∈ Ω₁.1 → φ ∈ Ω₂.1} : Ω₁ = Ω₂ := by
  exact equality_def.mpr $ Set.eq_of_subset_of_subset
    (by intro φ hp; exact h φ hp)
    (by
      intro φ;
      contrapose;
      intro hp;
      apply iff_mem_neg.mp;
      apply h;
      apply iff_mem_neg.mpr hp;
    )

lemma neg_imp (h : ψ ∈ Ω₂ → φ ∈ Ω₁) : (∼φ ∈ Ω₁) → (∼ψ ∈ Ω₂) := by
  contrapose;
  intro nhnψ hnφ;
  have : φ ∈ Ω₁ := h $ iff_mem_negneg.mp $ iff_mem_neg.mpr nhnψ;
  have : ⊥ ∈ Ω₁ := mdp hnφ this;
  simpa;

lemma neg_iff (h : φ ∈ Ω₁ ↔ ψ ∈ Ω₂) : (∼φ ∈ Ω₁) ↔ (∼ψ ∈ Ω₂) := ⟨neg_imp $ h.mpr, neg_imp $ h.mp⟩

lemma iff_mem_conj : (⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, φ ∈ Ω) := by simp [membership_iff, Conj₂!_iff_forall_provable];

section

variable [Entailment.K 𝓢]

lemma iff_mem_boxItr : (□^[n]φ ∈ Ω) ↔ (∀ {Ω' : MaximalConsistentSet 𝓢}, ((□⁻¹^[n]'Ω.1) ⊆ Ω'.1) → (φ ∈ Ω')) := by
  constructor;
  . intro hp Ω' hΩ';
    apply hΩ';
    simpa;
  . contrapose!;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓢 := 𝓢) (T := insert (∼φ) ((□⁻¹^[n]'Ω.1))) (by
      apply unprovable_iff_insert_neg_consistent.mpr;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : 𝓢 ⊢ □^[n]⋀Γ ➝ □^[n]φ := imply_boxItr_distribute'! hΓ₂;
      have : 𝓢 ⊬ □^[n]⋀Γ ➝ □^[n]φ := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : 𝓢 ⊬ ⋀((□^[n]'Γ)) ➝ □^[n]φ := FiniteContext.provable_iff.not.mp $ this (□^[n]'Γ) (by
          intro ψ hq;
          obtain ⟨χ, hr₁, rfl⟩ := List.LO.exists_of_mem_boxItr hq;
          simpa using hΓ₁ χ hr₁;
        );
        contrapose! this;
        exact C!_trans collect_boxItr_conj! this;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by tauto_set) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]

lemma iff_mem_box : (□φ ∈ Ω) ↔ (∀ {Ω' : MaximalConsistentSet 𝓢}, ((□⁻¹'Ω.1) ⊆ Ω'.1) → (φ ∈ Ω')) := iff_mem_boxItr (n := 1)

lemma boxItr_dn_iff : (□^[n](∼∼φ) ∈ Ω) ↔ (□^[n]φ ∈ Ω) := by
  simp only [iff_mem_boxItr];
  constructor;
  . intro h Ω hΩ;
    exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ;
    exact iff_mem_negneg.mpr $ h hΩ;

lemma box_dn_iff : (□(∼∼φ) ∈ Ω) ↔ (□φ ∈ Ω) := boxItr_dn_iff (n := 1)

lemma mem_boxItr_dual : □^[n]φ ∈ Ω ↔ ∼(◇^[n](∼φ)) ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_left boxItr_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_right boxItr_duality!);

lemma mem_box_dual : □φ ∈ Ω ↔ (∼(◇(∼φ)) ∈ Ω) := mem_boxItr_dual (n := 1)

lemma mem_diaItr_dual : ◇^[n]φ ∈ Ω ↔ ∼(□^[n](∼φ)) ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_left diaItr_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ C!_trans (FiniteContext.provable_iff.mp hΓ₂) (K!_right diaItr_duality!);
lemma mem_dia_dual : ◇φ ∈ Ω ↔ (∼(□(∼φ)) ∈ Ω) := mem_diaItr_dual (n := 1)

lemma iff_mem_diaItr : (◇^[n]φ ∈ Ω) ↔ (∃ Ω' : MaximalConsistentSet 𝓢, ((□⁻¹^[n]'Ω.1) ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) := by
  constructor;
  . intro h;
    have := mem_diaItr_dual.mp h;
    have := iff_mem_neg.mp this;
    have := iff_mem_boxItr.not.mp this;
    push_neg at this;
    obtain ⟨Ω', h₁, h₂⟩ := this;
    use Ω';
    constructor;
    . exact h₁;
    . exact iff_mem_negneg.mp $ iff_mem_neg.mpr h₂;
  . rintro ⟨Ω', h₁, h₂⟩;
    apply mem_diaItr_dual.mpr;
    apply iff_mem_neg.mpr;
    apply iff_mem_boxItr.not.mpr;
    push_neg;
    use Ω';
    constructor;
    . exact h₁;
    . exact iff_mem_neg.mp $ iff_mem_negneg.mpr h₂;
lemma iff_mem_dia : (◇φ ∈ Ω) ↔ (∃ Ω' : MaximalConsistentSet 𝓢, ((□⁻¹'Ω.1) ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) := iff_mem_diaItr (n := 1)

lemma boxItr_diaItr : (∀ {φ : Formula α}, (□^[n]φ ∈ Ω₁.1 → φ ∈ Ω₂.1)) ↔ (∀ {φ : Formula α}, (φ ∈ Ω₂.1 → ◇^[n]φ ∈ Ω₁.1)) := by
  constructor;
  . intro h φ;
    contrapose;
    intro h₂;
    apply iff_mem_neg.mp;
    apply h;
    apply iff_mem_negneg.mp;
    apply (neg_iff $ mem_diaItr_dual).mp;
    exact iff_mem_neg.mpr h₂;
  . intro h φ;
    contrapose;
    intro h₂;
    apply iff_mem_neg.mp;
    apply (neg_iff $ mem_boxItr_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply h;
    exact iff_mem_neg.mpr h₂;

variable {Γ : List (Formula α)}

lemma iff_mem_boxItr_conj : (□^[n]⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □^[n]φ ∈ Ω) := by
  simp only [iff_mem_boxItr, iff_mem_conj];
  constructor;
  . intro h φ hφ Ω' hΩ';
    exact h hΩ' _ hφ;
  . intro h Ω' hΩ' φ hφ;
    apply h _ hφ;
    tauto;

lemma iff_mem_box_conj : (□⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □φ ∈ Ω) := iff_mem_boxItr_conj (n := 1)

end

-- lemma diaItr_dn_iff : (◇^[n](∼∼φ) ∈ Ω) ↔ (◇^[n]φ ∈ Ω) := by sorry

-- lemma dia_dn_iff : (◇(∼∼φ) ∈ Ω) ↔ (◇φ) ∈ Ω := neg_iff box_dn_iff -- TODO: diaItr_dn_iff (n := 1)

end MaximalConsistentSet

end LO.Modal
end
