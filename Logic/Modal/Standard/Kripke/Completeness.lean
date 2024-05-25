import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Kripke.Completeness

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {𝓢 : S} {p q r : F} {Γ Δ : List F} {T : Set F}
variable [Minimal 𝓢] [NegDefinition F]

open FiniteContext

lemma efq_of_neg! [HasEFQ 𝓢] (h : 𝓢 ⊢! ~p) : 𝓢 ⊢! p ⟶ q := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [p] ⊢[𝓢]! p ⟶ ⊥ := by simpa [NegDefinition.neg] using of'! h;
  have dp : [p] ⊢[𝓢]! p := by_axm! (by simp);
  exact efq'! (dnp ⨀ dp);

lemma id_conj'! (he : ∀ g ∈ Γ, g = p) : 𝓢 ⊢! p ⟶ Γ.conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp_all only [List.conj'_nil, IsEmpty.forall_iff, forall_const]; exact dhyp! $ verum!;
  | hsingle => simp_all only [List.mem_singleton, forall_eq, List.conj'_singleton, imp_id!];
  | hcons r Γ h ih =>
    simp [List.conj'_cons_nonempty h];
    simp at he;
    have ⟨he₁, he₂⟩ := he;
    subst he₁;
    exact implyRightAnd! imp_id! (ih he₂);

lemma replace_imply_left_conj'! (he : ∀ g ∈ Γ, g = p) (hd : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! p ⟶ q := imp_trans! (id_conj'! he) hd


end LO.System


namespace LO.Modal.Standard

variable [DecidableEq α]

def Theory.ΛConsistent (Λ : AxiomSet α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → Λ ⊬! Γ.conj' ⟶ ⊥
notation:max "(" Λ ")-Consistent " T:90 => Theory.ΛConsistent Λ T

variable {Λ : AxiomSet α}

open System
open Theory

namespace Theory

variable {T : Theory α}

lemma def_not_ΛConsistent : ¬(Λ)-Consistent T ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ Λ ⊢! Γ.conj' ⟶ ⊥ := by simp [ΛConsistent];

lemma union_ΛConsistent : (Λ)-Consistent (T₁ ∪ T₂) → (Λ)-Consistent T₁ ∧ (Λ)-Consistent T₂ := by
  simp only [ΛConsistent];
  intro h;
  constructor;
  . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
  . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);

/-
lemma union_ΛConsistent' : (Λ)-Consistent (T₁ ∪ T₂) ↔ (Λ)-Consistent T₁ ∧ (Λ)-Consistent T₂ := by
  constructor;
  . simp only [ΛConsistent];
    intro h;
    constructor;
    . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
    . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);
  . rintro ⟨h₁, h₂⟩;
    intro Γ hΓ;
    induction Γ using List.induction_with_singleton with
    | hnil => exact h₁ (Γ := []) (by simp);
    | hsingle p =>
      simp at hΓ;
      cases hΓ with
      | inl h => exact h₁ (Γ := [p]) (by simp; exact h);
      | inr h => exact h₂ (Γ := [p]) (by simp; exact h);
    | hcons p Γ h ih =>
      by_contra hC;
      simp [List.conj'_cons_nonempty h, ←NegDefinition.neg] at hC;
      have : Λ ⊬! List.conj' Γ ⟶ ⊥ := ih (by intro q hq; exact hΓ q (by right; assumption));
      have : Λ ⊢! List.conj' Γ ⟶ ⊥ := disj₃'! (by
        apply contra₀'!;
        apply generalConj'!;
        have := hΓ p (by simp);
        sorry;
      ) imp_id! $ demorgan₄'! hC;
      contradiction;
-/

lemma union_not_Λconsistent : ¬(Λ)-Consistent T₁ ∨ ¬(Λ)-Consistent T₂ → ¬(Λ)-Consistent (T₁ ∪ T₂) := by
  contrapose;
  push_neg;
  exact union_ΛConsistent;

/-
lemma _root_.List.mem_insert {a : α} {l : List α} : a ∈ insert b l ↔ a = b ∨ a ∈ l := by
  induction l with
  | nil => simp;
  | cons c l ih =>
    simp_all [List.insert];
-/

lemma implyLeft_cons_conj' {Γ : List (Formula α)} : Λ ⊢! (p :: Γ).conj' ⟶ q ↔ Λ ⊢! p ⋏ Γ.conj' ⟶ q := by
  induction Γ with
  | nil =>
    simp [andImplyIffImplyImply'!];
    constructor;
    . intro h; apply imp_swap'!; exact dhyp! h;
    . intro h; exact imp_swap'! h ⨀ verum!;
  | cons q ih => simp;

lemma iff_insert_ΛConsistent : (Λ)-Consistent (insert p T) ↔ ∀ {Γ : List (Formula α)}, (∀ q ∈ Γ, q ∈ T) → Λ ⊬! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have := implyLeft_cons_conj'.not.mp $ @h (p :: Γ) (by
      rintro q hq;
      simp at hq;
      cases hq with
      | inl h => subst h; simp;
      | inr h => simp; right; exact hΓ q h;
    );
    contradiction;
  . intro h Γ hΓ;
    sorry
    -- by_contra hC;

lemma iff_insert_notΛConsistent : ¬(Λ)-Consistent (insert p T) ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ Λ ⊢! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_ΛConsistent.mpr;
  . contrapose; push_neg; apply iff_insert_ΛConsistent.mp;

lemma provable_iff_insert_neg_not_Λconsistent : T *⊢[Λ]! p ↔ ¬(Λ)-Consistent (insert (~p) T) := by
  constructor;
  . intro h;
    apply iff_insert_notΛConsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply andImplyIffImplyImply'!.mpr;
      apply imp_swap'!;
      exact imp_trans! (FiniteContext.toDef'! hΓ₂) dni!;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notΛConsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact FiniteContext.ofDef'! $ imp_trans! (imp_swap'! $ andImplyIffImplyImply'!.mp hΓ₂) dne!;

lemma unprovable_iff_insert_neg_ΛConsistent : T *⊬[Λ]! p ↔ (Λ)-Consistent (insert (~p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Λconsistent.mpr;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Λconsistent.mp;

lemma neg_provable_iff_insert_not_Λconsistent : T *⊢[Λ]! ~p ↔ ¬(Λ)-Consistent (insert (p) T) := by
  constructor;
  . intro h;
    apply iff_insert_notΛConsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . assumption;
    . apply andImplyIffImplyImply'!.mpr;
      apply imp_swap'!;
      exact FiniteContext.toDef'! hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notΛConsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact FiniteContext.ofDef'! $ imp_swap'! $ andImplyIffImplyImply'!.mp hΓ₂;

lemma neg_unprovable_iff_insert_ΛConsistent : T *⊬[Λ]! ~p ↔ (Λ)-Consistent (insert (p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Λconsistent.mpr;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Λconsistent.mp;

variable (consisT : (Λ)-Consistent T)

lemma unprovable_either : ¬(T *⊢[Λ]! p ∧ T *⊢[Λ]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[Λ]! ⊥ := hC₂ ⨀ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : Λ ⊬! List.conj' Γ ⟶ ⊥ := consisT hΓ₁;
  have : Λ ⊢! List.conj' Γ ⟶ ⊥ := implyLeft_conj_eq_conj'!.mp $ FiniteContext.toₛ! hΓ₂;
  contradiction;

lemma not_provable_falsum : T *⊬[Λ]! ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp $ hC;
  have : Λ ⊬! List.conj' Γ ⟶ ⊥ := consisT hΓ₁;
  have : Λ ⊢! List.conj' Γ ⟶ ⊥ := implyLeft_conj_eq_conj'!.mp hΓ₂;
  contradiction;

lemma not_mem_falsum_of_Λconsistent : ⊥ ∉ T := by
  by_contra hC;
  have : Λ ⊬! ⊥ ⟶ ⊥ := consisT (Γ := [⊥]) (by simpa);
  have : Λ ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

@[simp]
lemma append_singleton_eq {Γ : List (Formula α)} {p} (hΓ : Γ ≠ []) : (Γ ++ [p]).conj' = Γ.conj' ⋏ p := by
  induction Γ using List.induction_with_singleton with
  | hnil => contradiction;
  | hsingle q => simp;
  | hcons q Γ hΓ ih => simp; sorry;

lemma andAssoc! {p q r} : Λ ⊢! (p ⋏ q) ⋏ r ⟷ p ⋏ (q ⋏ r) := by
  apply iff_intro!;
  . apply FiniteContext.deduct'!;
    have hpqr : [(p ⋏ q) ⋏ r] ⊢[Λ]! (p ⋏ q) ⋏ r := FiniteContext.by_axm! (by simp);
    have hp : [(p ⋏ q) ⋏ r] ⊢[Λ]! p := conj₁'! $ conj₁'! hpqr;
    have hq : [(p ⋏ q) ⋏ r] ⊢[Λ]! q := conj₂'! $ conj₁'! hpqr;
    have hr : [(p ⋏ q) ⋏ r] ⊢[Λ]! r := conj₂'! hpqr;
    exact conj₃'! hp (conj₃'! hq hr);
  . apply FiniteContext.deduct'!;
    have hpqr : [p ⋏ (q ⋏ r)] ⊢[Λ]! p ⋏ q ⋏ r := FiniteContext.by_axm! (by simp);
    have hp : [p ⋏ (q ⋏ r)] ⊢[Λ]! p := conj₁'! hpqr;
    have hq : [p ⋏ (q ⋏ r)] ⊢[Λ]! q := conj₁'! $ conj₂'! hpqr;
    have hr : [p ⋏ (q ⋏ r)] ⊢[Λ]! r := conj₂'! $ conj₂'! hpqr;
    apply conj₃'!;
    . exact conj₃'! hp hq;
    . exact hr;

lemma conj'pl {Γ Δ : List (Formula α)} : Λ ⊢! (Γ ++ Δ).conj' ⟶ Γ.conj' ⋏ Δ.conj' := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil => simp only [List.append_nil, List.conj'_nil, imp_id!, implyRightAnd!];
  case hsingle.hsingle p q => simp only [List.singleton_append, ne_eq, not_false_eq_true, List.conj'_cons_nonempty, List.conj'_singleton, imp_id!];

  case hnil.hsingle q => simp only [List.nil_append, List.conj'_singleton, List.conj'_nil]; exact implyRightAnd! (dhyp! verum!) imp_id!;
  case hsingle.hnil p => simp only [List.nil_append, List.conj'_singleton, List.conj'_nil]; exact implyRightAnd! imp_id! (dhyp! verum!);

  case hcons.hnil p Γ hΓ ihΓ => simp only [(List.conj'_cons_nonempty hΓ), List.append_nil, List.conj'_nil]; exact implyRightAnd! imp_id! (dhyp! verum!);
  case hnil.hcons p Δ hΔ ihΔ => simp only [(List.conj'_cons_nonempty hΔ), List.nil_append, List.conj'_nil]; exact implyRightAnd! (dhyp! verum!) imp_id!;

  case hsingle.hcons p q Δ hΔ ihΔ => simp [(List.conj'_cons_nonempty hΔ)];
  case hcons.hsingle p Γ hΓ ihΓ q =>
    simp only [(List.conj'_cons_nonempty hΓ), List.cons_append, ne_eq, List.append_eq_nil, and_false, not_false_eq_true, List.conj'_cons_nonempty, List.conj'_singleton];
    exact imp_trans! (andReplaceRight! $ @ihΓ [q]) (conj₂'! andAssoc!);

    /-
    simp only [List.conj'_singleton] at ihΓ;
    exact imp_trans! (andReplaceRight! ihΓ) (conj₂'! andAssoc!);
    -/

  case hcons.hcons p Γ hΓ ihΓ q Δ hΔ ihΔ =>
    simp [(List.conj'_cons_nonempty hΓ)] at ihΔ;
    -- simp_all [(List.conj'_cons_nonempty hΓ), (List.conj'_cons_nonempty hΔ)];
    -- simp_all [(List.conj'_cons_nonempty hΓ), (List.conj'_cons_nonempty hΔ)];
    sorry;


lemma unprovable_imp_trans! (hpq : Λ ⊢! p ⟶ q) : Λ ⊬! p ⟶ r → Λ ⊬! q ⟶ r := by
  contrapose; simp [neg_neg];
  exact imp_trans! hpq;

lemma either_consistent (p) : (Λ)-Consistent (insert p T) ∨ (Λ)-Consistent (insert (~p) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notΛConsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_notΛConsistent.mp hC.2;

  rw [←NegDefinition.neg] at hΓ₂ hΔ₂;
  have : Λ ⊢! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := demorgan₁'! $ disj₃'! (imp_trans! (implyOfNotOr'! $ demorgan₄'! hΓ₂) disj₁!) (imp_trans! (implyOfNotOr'! $ demorgan₄'! hΔ₂) disj₂!) lem!;
  have := @consisT (Γ ++ Δ) (by
    intro q hq;
    simp at hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  );
  have : Λ ⊬! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := unprovable_imp_trans! conj'pl (consisT (by
    simp;
    intro q hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  ));
  contradiction;

lemma exists_maximal_Λconsistent_theory
  : ∃ Z, (Λ)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (Λ)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (Λ)-Consistent T } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [ΛConsistent, Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . intro Γ;
      by_contra hC;
      obtain ⟨hΓs, hΓd⟩ := by simpa using hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : (Λ)-Consistent U := hc hUc;
      have : ¬(Λ)-Consistent U := by
        simp only [ΛConsistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . intro p hp; exact hUs hp;
        . assumption;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T consisT

lemma intro_union_ΛConsistent (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ T₁) → (∀ p ∈ Γ₂, p ∈ T₂) → Λ ⊬! Γ₁.conj' ⋏ Γ₂.conj' ⟶ ⊥) : (Λ)-Consistent (T₁ ∪ T₂) := by
  intro Δ hΔ;
  let Δ₁ := Δ
  have := @h Δ Δ;
  sorry;


end Theory

structure MaximalΛConsistentTheory (Λ : AxiomSet α) where
  theory : Theory α
  consistent : (Λ)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(Λ)-Consistent U

alias MCT := MaximalΛConsistentTheory

namespace MaximalΛConsistentTheory

variable [HasAxiomK Λ]
variable {Ω Ω₁ Ω₂ : MCT Λ}
variable {p : Formula α}

lemma exists_maximal_Λconsistented_theory (consisT : (Λ)-Consistent T) : ∃ (Ω : MCT Λ), (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := exists_maximal_Λconsistent_theory consisT;
  existsi ⟨
    Ω,
    hΩ₁,
    by
      rintro U ⟨hU₁, hU₂⟩;
      by_contra hC;
      have : U = Ω := hΩ₃ U hC hU₁;
      subst_vars;
      simp at hU₂,
  ⟩;
  exact hΩ₂;

alias lindenbaum := exists_maximal_Λconsistented_theory

lemma either_mem (Ω : MCT Λ) (p) : p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent p with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(Λ)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)


lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω p); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[Λ]! ~p := Context.by_axm! hC;
    have := hnp ⨀ hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_Λconsistent Ω.consistent

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[Λ]! ⊥ := by apply membership_iff.not.mp; simp

lemma iff_mem_neg : (~p ∈ Ω.theory) ↔ (p ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.theory *⊢[Λ]! ⊥ := hnp ⨀ hp;
    have : Ω.theory *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_Λconsistent.not.mp $ membership_iff.not.mp hp;
    have := (not_imp_not.mpr $ Ω.maximal (U := insert (~p) Ω.theory)) this;
    simp [Set.ssubset_def] at this;
    apply this;
    simp;

lemma iff_mem_negneg : (~~p ∈ Ω.theory) ↔ (p ∈ Ω.theory) := by
  simp [membership_iff];
  constructor;
  . intro h; exact dne'! h;
  . intro h; exact dni'! h;

#print axioms iff_mem_negneg

@[simp]
lemma iff_mem_imp : ((p ⟶ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) → (q ∈ Ω.theory) := by
  constructor;
  . intro hpq hp;
    replace dpq := membership_iff.mp hpq;
    replace dp  := membership_iff.mp hp;
    apply membership_iff.mpr;
    exact dpq ⨀ dp;
  . intro h;
    replace h : p ∉ Ω.theory ∨ q ∈ Ω.theory := or_iff_not_imp_left.mpr (by simpa using h);
    cases h with
    | inl h =>
      apply membership_iff.mpr;
      exact efq_of_neg! $ membership_iff.mp $ iff_mem_neg.mpr h;
    | inr h =>
      apply membership_iff.mpr;
      exact imply₁! ⨀ (membership_iff.mp h)

@[simp]
lemma iff_mem_and : ((p ⋏ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) ∧ (q ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    constructor;
    . apply membership_iff.mpr; exact conj₁'! hpq;
    . apply membership_iff.mpr; exact conj₂'! hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact conj₃'! (membership_iff.mp hp) (membership_iff.mp hq);

@[simp]
lemma iff_mem_or : ((p ⋎ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) ∨ (q ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC; simp [not_or] at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp $ iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp $ iff_mem_neg.mpr hq;
    have : Ω.theory *⊢[Λ]! ⊥ := disj₃'! hp hq hpq;
    have : Ω.theory *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact disj₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact disj₂'! (membership_iff.mp hq);

lemma iff_mem_multibox : (□^[n]p ∈ Ω.theory) ↔ (∀ {Ω' : MCT Λ}, (□⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (Λ := Λ) (T := insert (~p) (□⁻¹^[n]Ω.theory)) (by
      apply unprovable_iff_insert_neg_ΛConsistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : Λ ⊢! □^[n]Γ.conj' ⟶ □^[n]p := imply_multibox_distribute'! $ implyLeft_conj_eq_conj'!.mp hΓ₂;
      have : Λ ⊬! □^[n]Γ.conj' ⟶ □^[n]p := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : Λ ⊬! (□^[n]Γ).conj' ⟶ □^[n]p := implyLeft_conj_eq_conj'!.not.mp $ FiniteContext.provable_iff.not.mp $ this (□^[n]Γ) (by
          intro q hq;
          obtain ⟨r, hr₁, hr₂⟩ := by simpa using hq;
          subst hr₂;
          simpa using hΓ₁ r hr₁;
        );
        revert this;
        contrapose;
        simp [neg_neg];
        exact imp_trans! imply_multiboxconj'_conj'multibox!
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : MCT Λ}, (□⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

lemma iff_congr : (Ω.theory *⊢[Λ]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ conj₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ conj₂'! hpq) hq;

lemma mem_dn_iff : (p ∈ Ω.theory) ↔ (~~p ∈ Ω.theory) := iff_congr $ (by simp)

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.theory = Ω₂.theory := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

lemma intro_equality {h : ∀ p, p ∈ Ω₁.theory → p ∈ Ω₂.theory} : Ω₁ = Ω₂ := by
  exact equality_def.mpr $ Set.eq_of_subset_of_subset
    (by intro p hp; exact h p hp)
    (by
      intro p;
      contrapose;
      intro hp;
      apply iff_mem_neg.mp;
      apply h;
      apply iff_mem_neg.mpr hp;
    )

lemma neg_imp (h : q ∈ Ω₂.theory → p ∈ Ω₁.theory) : (~p ∈ Ω₁.theory) → (~q ∈ Ω₂.theory) := by
  contrapose;
  intro hq;
  apply iff_mem_neg.mp;
  apply mem_dn_iff.mp;
  apply h;
  exact mem_dn_iff.mpr $ iff_mem_neg.mpr hq;

lemma neg_iff (h : p ∈ Ω₁.theory ↔ q ∈ Ω₂.theory) : (~p ∈ Ω₁.theory) ↔ (~q ∈ Ω₂.theory) := ⟨neg_imp $ h.mpr, neg_imp $ h.mp⟩

lemma box_dn_iff : (□~~p ∈ Ω.theory) ↔ (□p ∈ Ω.theory) := by
  simp only [iff_mem_box];
  constructor;
  . intro h Ω hΩ; exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ; exact iff_mem_negneg.mpr $ h hΩ;

lemma dia_dn_iff : (◇~~p ∈ Ω.theory) ↔ (◇p) ∈ Ω.theory := neg_iff box_dn_iff

lemma mem_multibox_dual : □^[n]p ∈ Ω.theory ↔ ~(◇^[n](~p)) ∈ Ω.theory := by
  simp [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₁'! multiboxDuality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₂'! multiboxDuality!);
lemma mem_box_dual : □p ∈ Ω.theory ↔ (~(◇(~p)) ∈ Ω.theory) := mem_multibox_dual (n := 1)

lemma mem_multidia_dual : ◇^[n]p ∈ Ω.theory ↔ ~(□^[n](~p)) ∈ Ω.theory := by
  simp [membership_iff];
  constructor;
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₁'! multidiaDuality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₂'! multidiaDuality!);
lemma mem_dia_dual : ◇p ∈ Ω.theory ↔ (~(□(~p)) ∈ Ω.theory) := mem_multidia_dual (n := 1)

lemma multibox_multidia : (∀ {p : Formula α}, (□^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory)) ↔ (∀ {p : Formula α}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory)) := by
  constructor;
  . intro H p;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply H;
    apply mem_dn_iff.mpr;
    apply (neg_iff $ mem_multidia_dual).mp;
    exact iff_mem_neg.mpr h;
  . intro H p;
    contrapose;
    intro h;
    apply iff_mem_neg.mp;
    apply (neg_iff $ mem_multibox_dual).mpr;
    apply iff_mem_negneg.mpr;
    apply H;
    exact iff_mem_neg.mpr h;

variable {Γ : List (Formula α)}

lemma iff_mem_conj' : (Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, p ∈ Ω.theory) := by simp [membership_iff, iff_provable_list_conj];

lemma iff_mem_multibox_conj' : (□^[n]Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, □^[n]p ∈ Ω.theory) := by
  simp only [iff_mem_multibox, iff_mem_conj'];
  constructor;
  . intro h p hp Ω' hΩ';
    exact (h hΩ') p hp;
  . intro h Ω' hΩ' p hp;
    exact @h p hp Ω' hΩ';

lemma iff_mem_box_conj' : (□Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, □p ∈ Ω.theory) := iff_mem_multibox_conj' (n := 1)

lemma iff_mem_multibox_conj'₂ : (□^[n]Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ.multibox n, p ∈ Ω.theory) := by simp [iff_mem_multibox_conj']

lemma iff_mem_box_conj'₂ : (□Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ.box, p ∈ Ω.theory) := iff_mem_multibox_conj'₂ (n := 1)

lemma iff_mem_multidia_conj' : (◇^[n]Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, ◇^[n]p ∈ Ω.theory) := by sorry
  /-
  simp [iff_mem_multibox, iff_mem_neg, mem_multidia_dual]
  constructor;
  . rintro ⟨Ω', hΩ'₁, hΩ'₂⟩ p hp;
    existsi Ω';
    constructor;
    . exact hΩ'₁;
    . simp_all;
  -/
lemma iff_mem_dia_conj' : (◇Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, ◇p ∈ Ω.theory) := iff_mem_multidia_conj' (n := 1)

end MaximalΛConsistentTheory


variable [HasAxiomK Λ]

open Formula
open MaximalΛConsistentTheory

namespace Kripke

def CanonicalModel (Λ : AxiomSet α) : Model (MCT Λ) α where
  frame (Ω₁ Ω₂) := □⁻¹Ω₁.theory ⊆ Ω₂.theory
  valuation Ω a := (atom a) ∈ Ω.theory

abbrev CanonicalFrame (Λ : AxiomSet α) : Frame (MCT Λ) α := CanonicalModel Λ |>.frame

namespace CanonicalModel

@[simp]
lemma frame_def_box: (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (∀ {p : Formula α}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory) := by rfl

lemma multiframe_def_multibox : (CanonicalModel Λ).frame^[n] Ω₁ Ω₂ ↔ ∀ {p : Formula α}, □^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory := by
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    simp_all;
    constructor;
    . intro h; subst h; tauto;
    . intro h; apply intro_equality; simpa;
  | succ n ih =>
    constructor;
    . simp;
      intro Ω₃ h₁₃ h₃₂ p h;
      exact ih.mp h₃₂ $ h₁₃ h;
    . intro h;
      obtain ⟨Ω, hΩ⟩ := lindenbaum (Λ := Λ) (T := (□⁻¹Ω₁.theory ∪ ◇^[n]Ω₂.theory)) (by
        intro Γ hΓ hC;
        sorry;

        /-

        have h₁ : □(Γ₁.conj') ∈ Ω₁.theory := iff_mem_box_conj'.mpr hΓ₁;
        have h₂ : (◇⁻¹^[n]Γ₂).conj' ∈ Ω₂.theory := by sorry;

        by_contra hC;
        have d₁ := imply_box_distribute'! $ andImplyIffImplyImply'!.mp hC;
        have d₂ : Ω₁.theory *⊢[Λ]! □(Γ₁.conj') := membership_iff.mp h₁;
        have : □~(Γ₂.conj') ∈ Ω₁.theory := membership_iff.mpr $ (Context.of! (Γ := Ω₁.theory) d₁) ⨀ d₂;

        -- have e : Γ₂.conj' = ◇^[n](◇⁻¹^[n]Γ₂).conj' := by sorry;
        -- rw [e];




        /-
        have d₁ : Ω₁.theory *⊢[Λ]! □(Γ₁.conj') ⟶ ~(◇Γ₂.conj') := Context.of! $ imp_trans! (imply_box_distribute'! $ andImplyIffImplyImply'!.mp hC) (contra₁'! $ conj₁'! $ diaDuality!);
        have d₂ : Ω₁.theory *⊢[Λ]! □(Γ₁.conj') := membership_iff.mp h₁;
        have d₃ : Ω₁.theory *⊢[Λ]! ~(◇Γ₂.conj') := d₁ ⨀ d₂;
        -/

        have d₁ : Λ ⊢! □Γ₁.conj' ⟶ □(~(◇^[n](◇⁻¹^[n]Γ₂).conj')) := imply_box_distribute'! $ andImplyIffImplyImply'!.mp hC;
        have d₂ : Ω₁.theory *⊢[Λ]! □(Γ₁.conj') := membership_iff.mp h₁;

        have := membership_iff.mpr $ (Context.of! (Γ := Ω₁.theory) d₁) ⨀ d₂;

        -- have := ih.mp (by sorry) this;

        -- have : Ω₁.theory *⊢[Λ]! ◇(Γ₂.conj') ⟷ ~(□~(Γ₂.conj')) := diaDuality

        sorry;
        /-
        have : (◇⁻¹^[n]Γ₂).conj' ∉ Ω₂.theory := by
          apply iff_mem_neg.mp;
        -/
        contradiction;
        -/
      )
      existsi Ω;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro p hp;
        apply hΩ;
        simp_all;

lemma multiframe_def_multidia : (CanonicalModel Λ).frame^[n] Ω₁ Ω₂ ↔ ∀ {p : Formula α}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory) := Iff.trans multiframe_def_multibox multibox_multidia

@[simp]
lemma val_def {a : α} : (CanonicalModel Λ).valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel

lemma truthlemma {p : Formula α} : ∀ {Ω : MCT Λ}, (CanonicalModel Λ, Ω) ⊧ p ↔ (p ∈ Ω.theory) := by
  induction p using Formula.rec' with
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply iff_mem_box.mpr;
      intro Ω' hΩ';
      apply ih.mp;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      exact CanonicalModel.frame_def_box.mp hΩ' h;
  | _ => simp_all

lemma deducible_of_validOnCanonicelModel : (CanonicalModel Λ) ⊧ p → (Λ ⊢! p) := by
  contrapose;
  intro h;
  have : (Λ)-Consistent ({~p}) := by
    simp [ΛConsistent];
    intro Γ hΓ;
    by_contra hC;
    have : Λ ⊢! p := dne'! $ replace_imply_left_conj'! hΓ hC;
    contradiction;
  obtain ⟨Ω, hΩ⟩ := lindenbaum this;
  simp [Kripke.ValidOnModel];
  existsi Ω;
  exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);

/-
class Canonical (Λ : AxiomSet α) where
  property : Frame (MCT Λ) α → Prop
  definability : AxiomSetDefinability (MCT Λ) Λ property
  satisfy : property (CanonicalFrame Λ)

lemma complete!_of_canonically [c : Canonical Λ] : 𝔽((Λ : AxiomSet α), MCT (Λ : AxiomSet α)) ⊧ p → (Λ ⊢! p) := by
  contrapose;
  intro h₁ h₂;
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame] at h₂;
  have : Λ ⊢! p := deducible_of_validOnCanonicelModel $ h₂ (CanonicalModel Λ).frame
    (by apply iff_definability_memAxiomSetFrameClass c.definability |>.mp; exact c.satisfy)
    (CanonicalModel Λ).valuation;
  contradiction;
-/

class Canonical (Λ : AxiomSet α) where
  valid : (CanonicalFrame Λ) ⊧* Λ

lemma complete!_of_canonical [canonical : Canonical Λ] : 𝔽((Λ : AxiomSet α), MCT (Λ : AxiomSet α)) ⊧ p → (Λ ⊢! p) := by
  contrapose;
  intro h₁ h₂;
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame] at h₂;
  have : Λ ⊢! p := deducible_of_validOnCanonicelModel $ h₂ (CanonicalModel Λ).frame canonical.valid (CanonicalModel Λ).valuation;
  contradiction;

instance [Canonical Λ]: Complete Λ 𝔽(Λ, MCT Λ) := ⟨complete!_of_canonical⟩

instance AxiomSet.K.Canonical : Canonical (𝐊 : AxiomSet α) where
  valid := by apply AxiomSet.K.definability.defines _ |>.mp; trivial;

instance : Complete (𝐊 : AxiomSet α) 𝔽((𝐊 : AxiomSet α), MCT (𝐊 : AxiomSet α)) := inferInstance

end Kripke

end LO.Modal.Standard
