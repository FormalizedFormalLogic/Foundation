import Foundation.Modal.Hilbert2.Basic

namespace LO.Modal

variable {α : Type*}
variable {H : Hilbert α}

open System
open Hilbert.Deduction

namespace FormulaSet

variable {T : FormulaSet α} (T_consis : T *⊬[H] ⊥)

lemma def_consistent : T *⊬[H] ⊥ ↔ ∀ (Γ : List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) → Γ ⊬[H] ⊥ := by
  constructor;
  . intro h;
    simpa using Context.provable_iff.not.mp h;
  . intro h;
    apply Context.provable_iff.not.mpr; push_neg;
    assumption;

lemma def_inconsistent : T *⊢[H]! ⊥ ↔ ∃ (Γ : List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Γ ⊢[H]! ⊥ := by
  apply not_iff_not.mp;
  push_neg;
  exact def_consistent;

/-
@[simp]
lemma self_consistent [H_consis : System.Consistent H] : H.axioms.Consistent H := by
  obtain ⟨ψ, hq⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ;
  by_contra hC;
  have : H ⊢! ψ := imp_trans''! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => maxm! $ hΓ _ h);
  contradiction;
-/

lemma union_consistent : (T₁ ∪ T₂) *⊬[H] ⊥ → T₁ *⊬[H] ⊥ ∧ T₂ *⊬[H] ⊥ := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> {
    apply def_consistent.mpr;
    intro Γ hΓ;
    exact h Γ $ by tauto_set;
  }

lemma emptyset_consistent [H_consis : System.Consistent H] : ∅ *⊬[H] ⊥ := by
  obtain ⟨f, hf⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ; by_contra hC;
  replace hΓ := List.eq_nil_iff_forall_not_mem.mpr hΓ; subst hΓ;
  have : H ⊢! f := efq'! $ hC ⨀ verum!;
  contradiction;

variable [DecidableEq α]

lemma iff_insert_consistent : (insert φ T) *⊬[H] ⊥ ↔ ∀ {Γ : List (Formula α)}, (∀ ψ ∈ Γ, ψ ∈ T) → H ⊬ φ ⋏ ⋀Γ ➝ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have : H ⊬ φ ⋏ ⋀Γ ➝ ⊥ := iff_imply_left_cons_conj'!.not.mp $ (def_consistent.mp h) (φ :: Γ) (by
      rintro ψ hq;
      simp at hq;
      cases hq with
      | inl h => subst h; simp;
      | inr h => simp; right; exact hΓ ψ h;
    );
    contradiction;
  . intro h;
    apply def_consistent.mpr;
    intro Γ hΓ;
    have  : H ⊬ φ ⋏ ⋀List.remove φ Γ ➝ ⊥ := @h (Γ.remove φ) (by
      intro ψ hq;
      have := by simpa using hΓ ψ $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have := FiniteContext.provable_iff.mp hC;
    have := imp_trans''! and_comm! $ imply_left_remove_conj! (φ := φ) $ FiniteContext.provable_iff.mp hC;
    contradiction;

lemma iff_insert_inconsistent : (insert φ T) *⊢[H]! ⊥ ↔ ∃ Γ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ H ⊢! φ ⋏ ⋀Γ ➝ ⊥ := by
  apply not_iff_not.mp;
  push_neg;
  exact iff_insert_consistent;

lemma provable_iff_insert_neg_not_consistent : T *⊢[H]! φ ↔ (insert (∼φ) T) *⊢[H]! ⊥ := by
  constructor;
  . intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    use Γ;
    constructor;
    . exact hΓ₁;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact neg_equiv'!.mp $ dni'! hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . have : Γ ⊢[H]! ∼φ ➝ ⊥ := imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;
      exact dne'! $ neg_equiv'!.mpr this;

lemma unprovable_iff_insert_neg_consistent : T *⊬[H] φ ↔ (insert (∼φ) T) *⊬[H] ⊥ := by
  simpa [not_not] using provable_iff_insert_neg_not_consistent.not;

lemma unprovable_iff_singleton_neg_consistent : H ⊬ φ ↔ {∼φ} *⊬[H] ⊥ := by
  have e : insert (∼φ) ∅ = ({∼φ} : FormulaSet α) := by aesop;
  have h₂ := unprovable_iff_insert_neg_consistent (H := H) (T := ∅) (φ := φ);
  rw [e] at h₂;
  exact Iff.trans Context.provable_iff_provable.not h₂;

lemma neg_provable_iff_insert_not_consistent : T *⊢[H]! ∼φ ↔ (insert (φ) T) *⊢[H]! ⊥ := by
  constructor;
  . intro h;
    apply iff_insert_inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . assumption;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact neg_equiv'!.mp hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply neg_equiv'!.mpr;
      exact imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;

lemma neg_unprovable_iff_insert_consistent : T *⊬[H] ∼φ ↔ (insert (φ) T) *⊬[H] ⊥ := by
  simpa [not_not] using neg_provable_iff_insert_not_consistent.not;

lemma unprovable_iff_singleton_consistent : H ⊬ ∼φ ↔ {φ} *⊬[H] ⊥ := by
  have e : insert (φ) ∅ = ({φ} : FormulaSet α) := by aesop;
  have h₂ := neg_unprovable_iff_insert_consistent (H := H) (T := ∅) (φ := φ);
  rw [e] at h₂;
  exact Iff.trans Context.provable_iff_provable.not h₂;

/-
omit [DecidableEq α] in
lemma unprovable_falsum (T_consis : T.Consistent H) : T *⊬[H] ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, _⟩ := Context.provable_iff.mp $ hC;
  have : Γ ⊬[H] ⊥ := (def_consistent.mp T_consis) _ hΓ₁;
  contradiction;
-/

lemma unprovable_either (T_consis : T *⊬[H] ⊥) : ¬(T *⊢[H]! φ ∧ T *⊢[H]! ∼φ) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[H]! ⊥ := neg_mdp! hC₂ hC₁;
  contradiction;

lemma not_mem_falsum_of_consistent (T_consis : T *⊬[H] ⊥) : ⊥ ∉ T := by
  by_contra hC;
  have : H ⊬ ⊥ ➝ ⊥ := (def_consistent.mp T_consis) [⊥] (by simpa);
  have : H ⊢! ⊥ ➝ ⊥ := efq!;
  contradiction;

lemma not_singleton_consistent (T_consis : T *⊬[H] ⊥) (h : ∼□φ ∈ T) : {∼φ} *⊬[H] ⊥ := by
  apply def_consistent.mpr;
  intro Γ hΓ;
  simp only [Set.mem_singleton_iff] at hΓ;
  by_contra hC;
  have : H ⊢! ∼(□φ) ➝ ⊥ := neg_equiv'!.mp $ dni'! $ nec! $ dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj! hΓ hC;
  have : H ⊬ ∼(□φ) ➝ ⊥ := def_consistent.mp T_consis (Γ := [∼(□φ)]) (by aesop)
  contradiction;

lemma either_consistent (T_consis : T *⊬[H] ⊥) (φ) : (insert φ T) *⊬[H] ⊥ ∨ (insert (∼φ) T) *⊬[H] ⊥ := by
  by_contra hC;
  push_neg at hC;
  obtain ⟨hC₁, hC₂⟩ := hC
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp $ by simpa using hC₁;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_inconsistent.mp $ by simpa using hC₂;
  replace hΓ₂ := neg_equiv'!.mpr hΓ₂;
  replace hΔ₂ := neg_equiv'!.mpr hΔ₂;
  have : H ⊢! ⋀Γ ⋏ ⋀Δ ➝ ⊥ := neg_equiv'!.mp $ demorgan₁'! $ or₃'''! (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΔ₂) or₂!) lem!
  have : H ⊬ ⋀Γ ⋏ ⋀Δ ➝ ⊥ := unprovable_imp_trans''! imply_left_concat_conj! $ def_consistent.mp T_consis (Γ ++ Δ) $ by
    simp only [List.mem_append];
    rintro ψ (hqΓ | hqΔ);
    . exact hΓ₁ ψ hqΓ;
    . exact hΔ₁ ψ hqΔ;
  contradiction;

lemma exists_consistent_maximal_of_consistent (T_consis : T *⊬[H] ⊥)
  : ∃ Z, Z *⊬[H] ⊥ ∧ T ⊆ Z ∧ ∀ U, U *⊬[H] ⊥ → Z ⊆ U → U = Z := by
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { T : FormulaSet α | T *⊬[H] ⊥ } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . apply def_consistent.mpr;
      intro Γ hΓ; by_contra hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro φ hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : U *⊬[H] ⊥ := hc hUc;
      have : U *⊢[H]! ⊥ := by
        apply def_inconsistent.mpr;
        use Γ;
        constructor;
        . intro φ hp; exact hUs hp;
        . assumption;
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

omit [DecidableEq α] in
open Classical in
lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) → H ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ➝ ⊥) : (T₁ ∪ T₂) *⊬[H] ⊥ := by
  apply def_consistent.mpr;
  intro Δ hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : H ⊬ ⋀Δ₁ ⋏ ⋀Δ₂ ➝ ⊥ := @h Δ₁ Δ₂ ⟨(by intro _ h; simpa using List.of_mem_filter h), (by intro _ h; simpa using List.of_mem_filter h)⟩;
  exact unprovable_imp_trans''! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro ψ hq;
    cases (hΔ ψ hq);
    . exact iff_provable_list_conj.mp (and₁'! FiniteContext.id!) ψ $ List.mem_filter_of_mem hq (by simpa);
    . exact iff_provable_list_conj.mp (and₂'! FiniteContext.id!) ψ $ List.mem_filter_of_mem hq (by simpa);
  ) this;

open Classical in
lemma intro_triunion_consistent
  (h : ∀ {Γ₁ Γ₂ Γ₃ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) ∧ (∀ φ ∈ Γ₃, φ ∈ T₃) → H ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃ ➝ ⊥)
  : (T₁ ∪ T₂ ∪ T₃) *⊬[H] ⊥ := by
  apply intro_union_consistent;
  rintro Γ₁₂ Γ₃ ⟨h₁₂, h₃⟩;
  simp at h₁₂;
  let Γ₁ := (Γ₁₂.filter (· ∈ T₁));
  let Γ₂ := (Γ₁₂.filter (· ∈ T₂));
  apply unprovable_imp_trans''! (φ := ⋀Γ₁ ⋏ ⋀Γ₂ ⋏ ⋀Γ₃);
  . exact imp_trans''! (and₂'! $ and_assoc!) $ by
      apply and_replace_left!;
      apply imply_left_conj_concat!.mp;
      apply conjconj_subset!;
      intro φ hp;
      simp [Γ₁, Γ₂];
      rcases h₁₂ φ hp with (h₁ | h₂);
      . left; exact ⟨hp, h₁⟩;
      . right; exact ⟨hp, h₂⟩;
  . apply h;
    refine ⟨?_, ?_, h₃⟩;
    . intro φ hp;
      rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      . assumption;
      . simpa using List.of_mem_filter hp;
    . intro φ hp;
      rcases h₁₂ φ (List.mem_of_mem_filter hp) with (_ | _)
      . have := List.of_mem_filter hp; simp at this;
        simpa using List.of_mem_filter hp;
      . assumption;

lemma not_mem_of_mem_neg (T_consis : T *⊬[H] ⊥) (h : ∼φ ∈ T) : φ ∉ T := by
  by_contra hC;
  have : [φ, ∼φ] ⊬[H] ⊥ := (FormulaSet.def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[H]! ⊥ := System.bot_of_mem_either! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;

lemma not_mem_neg_of_mem (T_consis : T *⊬[H] ⊥) (h : φ ∈ T) : ∼φ ∉ T := by
  by_contra hC;
  have : [φ, ∼φ] ⊬[H] ⊥ := (FormulaSet.def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[H]! ⊥ := System.bot_of_mem_either! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;
end FormulaSet

abbrev MaximalConsistentSet (H : Hilbert α) := { T : FormulaSet α // (T *⊬[H] ⊥) ∧ (∀ {U}, T ⊂ U → U *⊢[H]! ⊥)}

alias MCS := MaximalConsistentSet

namespace MaximalConsistentSet

open FormulaSet

lemma consistent {Ω : MCS H} : Ω.1 *⊬[H] ⊥ := Ω.2.1

lemma maximal {Ω : MCS H} : Ω.1 ⊂ U → U *⊢[H]! ⊥ := Ω.2.2

variable [DecidableEq α]
variable {H : Hilbert α}
variable {Ω Ω₁ Ω₂ : MCS H}
variable {φ : Formula α}

instance : Membership (Formula α) (MCS H) := ⟨λ Ω φ => φ ∈ Ω.1⟩

lemma exists_of_consistent {T : FormulaSet α} (consisT : T *⊬[H] ⊥) : ∃ Ω : MCS H, (T ⊆ Ω.1) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := FormulaSet.lindenbaum consisT;
  use ⟨Ω, ?_, ?_⟩;
  . assumption;
  . rintro U ⟨hU₁, _⟩;
    by_contra hC;
    have := hΩ₃ U hC $ hU₁;
    subst this;
    simp_all;

alias lindenbaum := exists_of_consistent

instance [System.Consistent H] : Nonempty (MCS H) := ⟨lindenbaum emptyset_consistent |>.choose⟩

lemma either_mem (Ω : MCS H) (φ) : φ ∈ Ω ∨ ∼φ ∈ Ω := by
  by_contra hC; push_neg at hC;
  cases either_consistent consistent φ with
  | inl h => have := maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := maximal (Set.ssubset_insert hC.2); contradiction;

omit [DecidableEq α] in
lemma maximal' {φ : Formula α} (hp : φ ∉ Ω) : (insert φ Ω.1) *⊢[H]! ⊥ := maximal (Set.ssubset_insert hp)

lemma membership_iff : (φ ∈ Ω) ↔ (Ω.1 *⊢[H]! φ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ∼φ ∉ Ω.1 by apply or_iff_not_imp_right.mp $ (either_mem Ω φ); assumption;
    by_contra hC;
    have hnp : Ω.1 *⊢[H]! ∼φ := Context.by_axm! hC;
    have : Ω.1 *⊢[H]! ⊥ := neg_mdp! hnp hp;
    have : Ω.1 *⊬[H] ⊥ := consistent;
    contradiction;

lemma subset_axiomset : H.axioms ⊆ Ω.1 := by
  intro φ hp;
  apply membership_iff.mpr;
  apply Context.of!;
  exact maxm! (by aesop);

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω.1 := not_mem_falsum_of_consistent consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma iff_mem_neg : (∼φ ∈ Ω) ↔ (φ ∉ Ω.1) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.1 *⊢[H]! ⊥ := neg_mdp! hnp hp;
    have : Ω.1 *⊬[H] ⊥ := consistent;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_consistent.not.mp $ membership_iff.not.mp hp;
    have := not_imp_not.mpr (@maximal (Ω := Ω) (U := insert (∼φ) Ω.1)) this;
    have : insert (∼φ) Ω.1 ⊆ Ω.1 := by simpa [Set.ssubset_def] using this;
    apply this;
    tauto_set;

lemma iff_mem_negneg : (∼∼φ ∈ Ω) ↔ (φ ∈ Ω) := by
  simp only [membership_iff];
  constructor;
  . apply dne'!;
  . apply dni'!;

@[simp]
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
      exact efq_of_neg! $ membership_iff.mp $ iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact imply₁! ⨀ (membership_iff.mp h)

@[simp]
lemma iff_mem_and : ((φ ⋏ ψ) ∈ Ω) ↔ (φ ∈ Ω) ∧ (ψ ∈ Ω) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    constructor;
    . apply membership_iff.mpr; exact and₁'! hpq;
    . apply membership_iff.mpr; exact and₂'! hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact and₃'! (membership_iff.mp hp) (membership_iff.mp hq);

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
    have : Ω.1 *⊢[H]! ⊥ := or₃'''! (neg_equiv'!.mp hp) (neg_equiv'!.mp hq) hpq;
    have : Ω.1 *⊬[H] ⊥ := consistent;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

lemma iff_congr : (Ω.1 *⊢[H]! (φ ⭤ ψ)) → ((φ ∈ Ω) ↔ (ψ ∈ Ω)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ and₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ and₂'! hpq) hq;

lemma mem_dn_iff : (φ ∈ Ω) ↔ (∼∼φ ∈ Ω) := iff_congr $ dn!

omit [DecidableEq α] in
lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

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

lemma neg_imp (h : ψ ∈ Ω₂.1 → φ ∈ Ω₁.1) : (∼φ ∈ Ω₁.1) → (∼ψ ∈ Ω₂.1) := by
  contrapose;
  intro hq;
  apply iff_mem_neg.mp;
  apply mem_dn_iff.mp;
  apply h;
  exact mem_dn_iff.mpr $ iff_mem_neg.mpr hq;

lemma neg_iff (h : φ ∈ Ω₁.1 ↔ ψ ∈ Ω₂.1) : (∼φ ∈ Ω₁.1) ↔ (∼ψ ∈ Ω₂.1) := ⟨neg_imp $ h.mpr, neg_imp $ h.mp⟩

lemma iff_mem_conj : (⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, φ ∈ Ω) := by simp [membership_iff, iff_provable_list_conj];

-- These lemmata require H normality
section Normal

variable [System.K H]

lemma iff_mem_multibox : (□^[n]φ ∈ Ω) ↔ (∀ {Ω' : MCS H}, (□''⁻¹^[n]Ω.1 ⊆ Ω'.1) → (φ ∈ Ω')) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (H := H) (T := insert (∼φ) (□''⁻¹^[n]Ω.1)) (by
      apply unprovable_iff_insert_neg_consistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : H ⊢! □^[n]⋀Γ ➝ □^[n]φ := imply_multibox_distribute'! hΓ₂;
      have : H ⊬ □^[n]⋀Γ ➝ □^[n]φ := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : H ⊬ ⋀□'^[n]Γ ➝ □^[n]φ := FiniteContext.provable_iff.not.mp $ this (□'^[n]Γ) (by
          intro ψ hq;
          obtain ⟨χ, hr₁, rfl⟩ := by simpa using hq;
          simpa using hΓ₁ χ hr₁;
        );
        revert this;
        contrapose;
        simp only [not_not];
        exact imp_trans''! collect_multibox_conj!;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by tauto_set) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□φ ∈ Ω) ↔ (∀ {Ω' : MCS H}, (□''⁻¹Ω.1 ⊆ Ω'.1) → (φ ∈ Ω'.1)) := iff_mem_multibox (n := 1)

lemma multibox_dn_iff : (□^[n](∼∼φ) ∈ Ω) ↔ (□^[n]φ ∈ Ω) := by
  simp only [iff_mem_multibox];
  constructor;
  . intro h Ω hΩ; exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ; exact iff_mem_negneg.mpr $ h hΩ;
lemma box_dn_iff : (□(∼∼φ) ∈ Ω) ↔ (□φ ∈ Ω) := multibox_dn_iff (n := 1)

lemma mem_multibox_dual : □^[n]φ ∈ Ω ↔ ∼(◇^[n](∼φ)) ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multibox_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    use Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multibox_duality!);
lemma mem_box_dual : □φ ∈ Ω ↔ (∼(◇(∼φ)) ∈ Ω) := mem_multibox_dual (n := 1)

-- lemma multidia_dn_iff : (◇^[n](∼∼φ) ∈ Ω) ↔ (◇^[n]φ ∈ Ω) := by sorry

-- lemma dia_dn_iff : (◇(∼∼φ) ∈ Ω) ↔ (◇φ) ∈ Ω := neg_iff box_dn_iff -- TODO: multidia_dn_iff (n := 1)

lemma mem_multidia_dual : ◇^[n]φ ∈ Ω ↔ ∼(□^[n](∼φ)) ∈ Ω := by
  simp only [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multidia_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multidia_duality!);
lemma mem_dia_dual : ◇φ ∈ Ω ↔ (∼(□(∼φ)) ∈ Ω) := mem_multidia_dual (n := 1)

lemma iff_mem_multidia : (◇^[n]φ ∈ Ω) ↔ (∃ Ω' : MCS H, (□''⁻¹^[n]Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) := by
  constructor;
  . intro h;
    have := mem_multidia_dual.mp h;
    have := iff_mem_neg.mp this;
    have := iff_mem_multibox.not.mp this;
    push_neg at this;
    obtain ⟨Ω', h₁, h₂⟩ := this;
    use Ω';
    constructor;
    . exact h₁;
    . exact mem_dn_iff.mpr $ iff_mem_neg.mpr h₂;
  . rintro ⟨Ω', h₁, h₂⟩;
    apply mem_multidia_dual.mpr;
    apply iff_mem_neg.mpr;
    apply iff_mem_multibox.not.mpr;
    push_neg;
    use Ω';
    constructor;
    . exact h₁;
    . exact iff_mem_neg.mp $ mem_dn_iff.mp h₂;
lemma iff_mem_dia : (◇φ ∈ Ω) ↔ (∃ Ω' : MCS H, (□''⁻¹Ω.1 ⊆ Ω'.1) ∧ (φ ∈ Ω'.1)) := iff_mem_multidia (n := 1)

lemma multibox_multidia : (∀ {φ : Formula α}, (□^[n]φ ∈ Ω₁.1 → φ ∈ Ω₂.1)) ↔ (∀ {φ : Formula α}, (φ ∈ Ω₂.1 → ◇^[n]φ ∈ Ω₁.1)) := by
  constructor;
  . intro H φ;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply H;
    apply mem_dn_iff.mpr;
    apply (neg_iff $ mem_multidia_dual).mp;
    exact iff_mem_neg.mpr h;
  . intro H φ;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply (neg_iff $ mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply H;
    exact iff_mem_neg.mpr h;

variable {Γ : List (Formula α)}

lemma iff_mem_multibox_conj : (□^[n]⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □^[n]φ ∈ Ω) := by
  simp only [iff_mem_multibox, iff_mem_conj];
  constructor;
  . intro h φ hφ Ω' hΩ';
    exact h hΩ' _ hφ;
  . intro h Ω' hΩ' φ hφ;
    apply h _ hφ;
    tauto;

lemma iff_mem_box_conj : (□⋀Γ ∈ Ω) ↔ (∀ φ ∈ Γ, □φ ∈ Ω) := iff_mem_multibox_conj (n := 1)

end Normal

end MaximalConsistentSet

end LO.Modal
