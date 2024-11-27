import Foundation.Modal.Hilbert.Basic

namespace LO.Modal

variable {α : Type*}
variable {H : Hilbert α}

open System
open Hilbert.Deduction

abbrev Theory.Consistent (H : Hilbert α) (T : Theory α) := T *⊬[H] ⊥

abbrev Theory.Inconsistent (H : Hilbert α) (T : Theory α) := ¬(T.Consistent H)

namespace Theory

variable {T : Theory α} (T_consis : T.Consistent H)

lemma def_consistent : T.Consistent H ↔ ∀ (Γ : List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) → Γ ⊬[H] ⊥ := by
  constructor;
  . intro h;
    simpa using Context.provable_iff.not.mp h;
  . intro h;
    apply Context.provable_iff.not.mpr; push_neg;
    assumption;

lemma def_inconsistent : ¬T.Consistent H ↔ ∃ (Γ : List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Γ ⊢[H]! ⊥ := by
  simp only [def_consistent]; push_neg; tauto;

@[simp]
lemma self_consistent [H_consis : System.Consistent H] : H.axioms.Consistent H := by
  obtain ⟨ψ, hq⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ;
  by_contra hC;
  have : H ⊢! ψ := imp_trans''! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => maxm! $ hΓ _ h);
  contradiction;

lemma union_consistent : Theory.Consistent H (T₁ ∪ T₂) → T₁.Consistent H ∧ T₂.Consistent H := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> { apply def_consistent.mpr; intro Γ hΓ; exact h Γ (by simp_all); }

lemma union_not_consistent : ¬T₁.Consistent H ∨ ¬T₂.Consistent H → ¬(Theory.Consistent H (T₁ ∪ T₂)) := by
  contrapose; push_neg;
  exact union_consistent;

lemma emptyset_consistent [H_consis : System.Consistent H] : Theory.Consistent H ∅ := by
  obtain ⟨f, hf⟩ := H_consis.exists_unprovable;
  apply def_consistent.mpr;
  intro Γ hΓ; by_contra hC;
  replace hΓ := List.nil_iff.mpr hΓ; subst hΓ;
  have : H ⊢! f := efq'! $ hC ⨀ verum!;
  contradiction;

variable [DecidableEq α]

lemma iff_insert_consistent : Theory.Consistent H (insert φ T) ↔ ∀ {Γ : List (Formula α)}, (∀ ψ ∈ Γ, ψ ∈ T) → H ⊬ φ ⋏ ⋀Γ ➝ ⊥ := by
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

lemma iff_insert_inconsistent : ¬(insert φ T).Consistent H ↔ ∃ Γ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ H ⊢! φ ⋏ ⋀Γ ➝ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_consistent.mpr;
  . contrapose; push_neg; apply iff_insert_consistent.mp;

lemma provable_iff_insert_neg_not_consistent : T *⊢[H]! φ ↔ ¬Theory.Consistent H (insert (∼φ) T) := by
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

lemma unprovable_iff_insert_neg_consistent : T *⊬[H] φ ↔ Theory.Consistent H (insert (∼φ) T) := by
  simpa [not_not] using provable_iff_insert_neg_not_consistent.not;

lemma unprovable_iff_singleton_neg_consistent : H ⊬ φ ↔ Theory.Consistent H {∼φ} := by
  have e : insert (∼φ) ∅ = ({∼φ} : Theory α) := by aesop;
  have H := unprovable_iff_insert_neg_consistent (H := H) (T := ∅) (φ := φ);
  rw [e] at H;
  exact Iff.trans Context.provable_iff_provable.not H;

lemma neg_provable_iff_insert_not_consistent : T *⊢[H]! ∼φ ↔ ¬Theory.Consistent H (insert (φ) T) := by
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

lemma neg_unprovable_iff_insert_consistent : T *⊬[H] ∼φ ↔ Theory.Consistent H (insert (φ) T) := by
  simpa [not_not] using neg_provable_iff_insert_not_consistent.not;

lemma unprovable_iff_singleton_consistent : H ⊬ ∼φ ↔ Theory.Consistent H {φ} := by
  have e : insert (φ) ∅ = ({φ} : Theory α) := by aesop;
  have H := neg_unprovable_iff_insert_consistent (H := H) (T := ∅) (φ := φ);
  rw [e] at H;
  exact Iff.trans Context.provable_iff_provable.not H;

omit [DecidableEq α] in
lemma unprovable_falsum (T_consis : T.Consistent H) : T *⊬[H] ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, _⟩ := Context.provable_iff.mp $ hC;
  have : Γ ⊬[H] ⊥ := (def_consistent.mp T_consis) _ hΓ₁;
  contradiction;

lemma unprovable_either (T_consis : T.Consistent H) : ¬(T *⊢[H]! φ ∧ T *⊢[H]! ∼φ) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[H]! ⊥ := neg_mdp! hC₂ hC₁;
  have : T *⊬[H] ⊥ := unprovable_falsum T_consis;
  contradiction;

lemma not_mem_falsum_of_consistent (T_consis : T.Consistent H) : ⊥ ∉ T := by
  by_contra hC;
  have : H ⊬ ⊥ ➝ ⊥ := (def_consistent.mp T_consis) [⊥] (by simpa);
  have : H ⊢! ⊥ ➝ ⊥ := efq!;
  contradiction;

lemma not_singleton_consistent [H.HasNecessitation] (T_consis : T.Consistent H) (h : ∼□φ ∈ T) : Theory.Consistent H {∼φ} := by
  apply def_consistent.mpr;
  intro Γ hΓ;
  simp only [Set.mem_singleton_iff] at hΓ;
  by_contra hC;
  have : H ⊢! ∼(□φ) ➝ ⊥ := neg_equiv'!.mp $ dni'! $ nec! $ dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj! hΓ hC;
  have : H ⊬ ∼(□φ) ➝ ⊥ := def_consistent.mp T_consis (Γ := [∼(□φ)]) (by aesop)
  contradiction;

lemma either_consistent (T_consis : T.Consistent H) (φ) : Theory.Consistent H (insert φ T) ∨ Theory.Consistent H (insert (∼φ) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_inconsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_inconsistent.mp hC.2;

  replace hΓ₂ := neg_equiv'!.mpr hΓ₂;
  replace hΔ₂ := neg_equiv'!.mpr hΔ₂;
  have : H ⊢! ⋀Γ ⋏ ⋀Δ ➝ ⊥ := neg_equiv'!.mp $ demorgan₁'! $ or₃'''! (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΔ₂) or₂!) lem!
  have : H ⊬ ⋀Γ ⋏ ⋀Δ ➝ ⊥ := unprovable_imp_trans''! imply_left_concat_conj! $ def_consistent.mp T_consis (Γ ++ Δ) $ by
    simp;
    rintro ψ (hqΓ | hqΔ);
    . exact hΓ₁ ψ hqΓ;
    . exact hΔ₁ ψ hqΔ;
  contradiction;

lemma exists_maximal_consistent_theory
  (T_consis : T.Consistent H)
  : ∃ Z, Theory.Consistent H Z ∧ T ⊆ Z ∧ ∀ U, Theory.Consistent H U → Z ⊆ U → U = Z := by
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { T : Theory α | T.Consistent H } (by
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
      have : Theory.Consistent H U := hc hUc;
      have : ¬Theory.Consistent H U := by
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
protected alias lindenbaum := exists_maximal_consistent_theory

omit [DecidableEq α] in
open Classical in
lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ φ ∈ Γ₁, φ ∈ T₁) ∧ (∀ φ ∈ Γ₂, φ ∈ T₂) → H ⊬ ⋀Γ₁ ⋏ ⋀Γ₂ ➝ ⊥) : Theory.Consistent H (T₁ ∪ T₂) := by
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
  : Theory.Consistent H (T₁ ∪ T₂ ∪ T₃) := by
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
      intro φ hp; simp [Γ₁, Γ₂];
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

lemma not_mem_of_mem_neg (T_consis : T.Consistent H) (h : ∼φ ∈ T) : φ ∉ T := by
  by_contra hC;
  have : [φ, ∼φ] ⊬[H] ⊥ := (Theory.def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[H]! ⊥ := System.bot_of_mem_either! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;

lemma not_mem_neg_of_mem (T_consis : T.Consistent H) (h : φ ∈ T) : ∼φ ∉ T := by
  by_contra hC;
  have : [φ, ∼φ] ⊬[H] ⊥ := (Theory.def_consistent.mp T_consis) [φ, ∼φ] (by simp_all);
  have : [φ, ∼φ] ⊢[H]! ⊥ := System.bot_of_mem_either! (φ := φ) (Γ := [φ, ∼φ]) (by simp) (by simp);
  contradiction;
end Theory

structure MaximalConsistentTheory (H : Hilbert α) where
  theory : Theory α
  consistent : theory.Consistent H
  maximal : ∀ {U}, theory ⊂ U → ¬Theory.Consistent H U
alias MCT := MaximalConsistentTheory

namespace MaximalConsistentTheory

open Theory

variable [DecidableEq α]
variable {H : Hilbert α}
variable {Ω Ω₁ Ω₂ : MCT H}
variable {φ : Formula α}

lemma exists_maximal_Lconsistented_theory (consisT : T.Consistent H) : ∃ Ω : MCT H, (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := Theory.lindenbaum consisT;
  use {
    theory := Ω,
    consistent := hΩ₁,
    maximal := by
      rintro U ⟨hU₁, hU₂⟩;
      by_contra hC;
      have : U = Ω := hΩ₃ U hC hU₁;
      subst_vars;
      simp at hU₂,
  }

alias lindenbaum := exists_maximal_Lconsistented_theory

instance [System.Consistent H] : Nonempty (MCT H) := ⟨lindenbaum emptyset_consistent |>.choose⟩

lemma either_mem (Ω : MCT H) (φ) : φ ∈ Ω.theory ∨ ∼φ ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent φ with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

omit [DecidableEq α] in
lemma maximal' {φ : Formula α} (hp : φ ∉ Ω.theory) : ¬Theory.Consistent H (insert φ Ω.theory) := Ω.maximal (Set.ssubset_insert hp)

lemma membership_iff : (φ ∈ Ω.theory) ↔ (Ω.theory *⊢[H]! φ) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ∼φ ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω φ); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[H]! ∼φ := Context.by_axm! hC;
    have := neg_mdp! hnp hp;
    have := Ω.consistent;
    contradiction;

lemma subset_axiomset : H.axioms ⊆ Ω.theory := by
  intro φ hp;
  apply membership_iff.mpr;
  apply Context.of!;
  exact maxm! (by aesop);

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω.theory := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[H] ⊥ := by apply membership_iff.not.mp; simp

@[simp]
lemma iff_mem_neg : (∼φ ∈ Ω.theory) ↔ (φ ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.theory *⊢[H]! ⊥ := neg_mdp! hnp hp;
    have : Ω.theory *⊬[H] ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_consistent.not.mp $ membership_iff.not.mp hp;
    have := (not_imp_not.mpr $ Ω.maximal (U := insert (∼φ) Ω.theory)) this;
    simp [Set.ssubset_def] at this;
    apply this;
    simp;

lemma iff_mem_negneg : (∼∼φ ∈ Ω.theory) ↔ (φ ∈ Ω.theory) := by
  simp only [membership_iff];
  constructor;
  . exact dne'!;
  . exact dni'!;

@[simp]
lemma iff_mem_imp : ((φ ➝ ψ) ∈ Ω.theory) ↔ (φ ∈ Ω.theory) → (ψ ∈ Ω.theory) := by
  constructor;
  . intro hpq hp;
    replace dpq := membership_iff.mp hpq;
    replace dp  := membership_iff.mp hp;
    apply membership_iff.mpr;
    exact dpq ⨀ dp;
  . intro h;
    replace h : φ ∉ Ω.theory ∨ ψ ∈ Ω.theory := or_iff_not_imp_left.mpr (by simpa using h);
    cases h with
    | inl h =>
      apply membership_iff.mpr;
      exact efq_of_neg! $ membership_iff.mp $ iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact imply₁! ⨀ (membership_iff.mp h)

@[simp]
lemma iff_mem_and : ((φ ⋏ ψ) ∈ Ω.theory) ↔ (φ ∈ Ω.theory) ∧ (ψ ∈ Ω.theory) := by
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
lemma iff_mem_or : ((φ ⋎ ψ) ∈ Ω.theory) ↔ (φ ∈ Ω.theory) ∨ (ψ ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC; simp [not_or] at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp $ iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp $ iff_mem_neg.mpr hq;
    have : Ω.theory *⊢[H]! ⊥ := or₃'''! (neg_equiv'!.mp hp) (neg_equiv'!.mp hq) hpq;
    have : Ω.theory *⊬[H] ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

lemma iff_congr : (Ω.theory *⊢[H]! (φ ⭤ ψ)) → ((φ ∈ Ω.theory) ↔ (ψ ∈ Ω.theory)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ and₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ and₂'! hpq) hq;

lemma mem_dn_iff : (φ ∈ Ω.theory) ↔ (∼∼φ ∈ Ω.theory) := iff_congr $ dn!

omit [DecidableEq α] in
lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.theory = Ω₂.theory := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

lemma intro_equality {h : ∀ φ, φ ∈ Ω₁.theory → φ ∈ Ω₂.theory} : Ω₁ = Ω₂ := by
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

lemma neg_imp (h : ψ ∈ Ω₂.theory → φ ∈ Ω₁.theory) : (∼φ ∈ Ω₁.theory) → (∼ψ ∈ Ω₂.theory) := by
  contrapose;
  intro hq;
  apply iff_mem_neg.mp;
  apply mem_dn_iff.mp;
  apply h;
  exact mem_dn_iff.mpr $ iff_mem_neg.mpr hq;

lemma neg_iff (h : φ ∈ Ω₁.theory ↔ ψ ∈ Ω₂.theory) : (∼φ ∈ Ω₁.theory) ↔ (∼ψ ∈ Ω₂.theory) := ⟨neg_imp $ h.mpr, neg_imp $ h.mp⟩

-- These lemmata require H normality
section Normal

variable [H.IsNormal]

lemma iff_mem_multibox : (□^[n]φ ∈ Ω.theory) ↔ (∀ {Ω' : MCT H}, (□''⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (φ ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (H := H) (T := insert (∼φ) (□''⁻¹^[n]Ω.theory)) (by
      apply unprovable_iff_insert_neg_consistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : H ⊢! □^[n]⋀Γ ➝ □^[n]φ := imply_multibox_distribute'! hΓ₂;
      have : H ⊬ □^[n]⋀Γ ➝ □^[n]φ := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : H ⊬ ⋀□'^[n]Γ ➝ □^[n]φ := FiniteContext.provable_iff.not.mp $ this (□'^[n]Γ) (by
          intro ψ hq;
          obtain ⟨χ, hr₁, hr₂⟩ := by simpa using hq;
          subst hr₂;
          simpa using hΓ₁ χ hr₁;
        );
        revert this;
        contrapose;
        simp [neg_neg];
        exact imp_trans''! collect_multibox_conj!;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□φ ∈ Ω.theory) ↔ (∀ {Ω' : MCT H}, (□''⁻¹Ω.theory ⊆ Ω'.theory) → (φ ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

lemma multibox_dn_iff : (□^[n](∼∼φ) ∈ Ω.theory) ↔ (□^[n]φ ∈ Ω.theory) := by
  simp only [iff_mem_multibox];
  constructor;
  . intro h Ω hΩ; exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ; exact iff_mem_negneg.mpr $ h hΩ;
lemma box_dn_iff : (□(∼∼φ) ∈ Ω.theory) ↔ (□φ ∈ Ω.theory) := multibox_dn_iff (n := 1)

lemma mem_multibox_dual : □^[n]φ ∈ Ω.theory ↔ ∼(◇^[n](∼φ)) ∈ Ω.theory := by
  simp [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₁'! multibox_duality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans''! (FiniteContext.provable_iff.mp hΓ₂) (and₂'! multibox_duality!);
lemma mem_box_dual : □φ ∈ Ω.theory ↔ (∼(◇(∼φ)) ∈ Ω.theory) := mem_multibox_dual (n := 1)

-- lemma multidia_dn_iff : (◇^[n](∼∼φ) ∈ Ω.theory) ↔ (◇^[n]φ ∈ Ω.theory) := by sorry

-- lemma dia_dn_iff : (◇(∼∼φ) ∈ Ω.theory) ↔ (◇φ) ∈ Ω.theory := neg_iff box_dn_iff -- TODO: multidia_dn_iff (n := 1)

lemma mem_multidia_dual : ◇^[n]φ ∈ Ω.theory ↔ ∼(□^[n](∼φ)) ∈ Ω.theory := by
  simp [membership_iff];
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
lemma mem_dia_dual : ◇φ ∈ Ω.theory ↔ (∼(□(∼φ)) ∈ Ω.theory) := mem_multidia_dual (n := 1)

lemma iff_mem_multidia : (◇^[n]φ ∈ Ω.theory) ↔ (∃ Ω' : MCT H, (□''⁻¹^[n]Ω.theory ⊆ Ω'.theory) ∧ (φ ∈ Ω'.theory)) := by
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
lemma iff_mem_dia : (◇φ ∈ Ω.theory) ↔ (∃ Ω' : MCT H, (□''⁻¹Ω.theory ⊆ Ω'.theory) ∧ (φ ∈ Ω'.theory)) := iff_mem_multidia (n := 1)

lemma multibox_multidia : (∀ {φ : Formula α}, (□^[n]φ ∈ Ω₁.theory → φ ∈ Ω₂.theory)) ↔ (∀ {φ : Formula α}, (φ ∈ Ω₂.theory → ◇^[n]φ ∈ Ω₁.theory)) := by
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

omit [H.IsNormal] in
lemma iff_mem_conj : (⋀Γ ∈ Ω.theory) ↔ (∀ φ ∈ Γ, φ ∈ Ω.theory) := by simp [membership_iff, iff_provable_list_conj];

lemma iff_mem_multibox_conj : (□^[n]⋀Γ ∈ Ω.theory) ↔ (∀ φ ∈ Γ, □^[n]φ ∈ Ω.theory) := by
  simp only [iff_mem_multibox, iff_mem_conj];
  constructor;
  . intro h φ hp Ω' hΩ';
    exact (h hΩ') φ hp;
  . intro h Ω' hΩ' φ hp;
    exact @h φ hp Ω' hΩ';

lemma iff_mem_box_conj : (□⋀Γ ∈ Ω.theory) ↔ (∀ φ ∈ Γ, □φ ∈ Ω.theory) := iff_mem_multibox_conj (n := 1)

end Normal

end MaximalConsistentTheory

end LO.Modal
