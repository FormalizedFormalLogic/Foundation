import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α] [Inhabited α]

open System

def Theory.Consistent (𝓓 : DeductionParameter α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → 𝓓 ⊬! Γ.conj' ⟶ ⊥
notation:max "(" 𝓓 ")-Consistent " T:90 => Theory.Consistent 𝓓 T

namespace Theory

variable {𝓓 : DeductionParameter α} {T : Theory α}

lemma self_Consistent [h : System.Consistent 𝓓] : (𝓓)-Consistent Ax(𝓓) := by
  intro Γ hΓ;
  obtain ⟨q, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : 𝓓 ⊢! q := imp_trans''! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => Deduction.maxm! $ hΓ _ h);
  contradiction;

lemma def_not_Consistent : ¬(𝓓)-Consistent T ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ 𝓓 ⊢! Γ.conj' ⟶ ⊥ := by simp [Consistent];

lemma union_Consistent : (𝓓)-Consistent (T₁ ∪ T₂) → (𝓓)-Consistent T₁ ∧ (𝓓)-Consistent T₂ := by
  simp only [Consistent];
  intro h;
  constructor;
  . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
  . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);

lemma union_not_Consistent : ¬(𝓓)-Consistent T₁ ∨ ¬(𝓓)-Consistent T₂ → ¬(𝓓)-Consistent (T₁ ∪ T₂) := by
  contrapose;
  push_neg;
  exact union_Consistent;

lemma iff_insert_Consistent : (𝓓)-Consistent (insert p T) ↔ ∀ {Γ : List (Formula α)}, (∀ q ∈ Γ, q ∈ T) → 𝓓 ⊬! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have : 𝓓 ⊬! p ⋏ List.conj' Γ ⟶ ⊥ := implyLeft_cons_conj'!.not.mp $ @h (p :: Γ) (by
      rintro q hq;
      simp at hq;
      cases hq with
      | inl h => subst h; simp;
      | inr h => simp; right; exact hΓ q h;
    );
    contradiction;
  . intro h Γ hΓ;
    have := @h (Γ.remove p) (by
      intro q hq;
      have := by simpa using hΓ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have := imp_trans''! and_comm! $ imply_left_remove_conj'! (p := p) hC;
    contradiction;

lemma iff_insert_Inconsistent : ¬(𝓓)-Consistent (insert p T) ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ 𝓓 ⊢! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_Consistent.mpr;
  . contrapose; push_neg; apply iff_insert_Consistent.mp;

lemma provable_iff_insert_neg_not_Consistent : T *⊢[𝓓]! p ↔ ¬(𝓓)-Consistent (insert (~p) T) := by
  constructor;
  . intro h;
    apply iff_insert_Inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact neg_equiv'!.mp $ dni'! hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . have : Γ ⊢[𝓓]! ~p ⟶ ⊥ := imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;
      exact dne'! $ neg_equiv'!.mpr this;

lemma unprovable_iff_insert_neg_Consistent : T *⊬[𝓓]! p ↔ (𝓓)-Consistent (insert (~p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Consistent.mpr;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Consistent.mp;

lemma unprovable_iff_singleton_neg_Consistent : 𝓓 ⊬! p ↔ (𝓓)-Consistent {~p} := by
  have e : insert (~p) ∅ = ({~p} : Theory α) := by aesop;
  have H := unprovable_iff_insert_neg_Consistent (𝓓 := 𝓓) (T := ∅) (p := p);
  rw [e] at H;
  exact Iff.trans Context.emptyPrf!.symm.not H;

lemma neg_provable_iff_insert_not_Consistent : T *⊢[𝓓]! ~p ↔ ¬(𝓓)-Consistent (insert (p) T) := by
  constructor;
  . intro h;
    apply iff_insert_Inconsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . assumption;
    . apply and_imply_iff_imply_imply'!.mpr;
      apply imp_swap'!;
      exact neg_equiv'!.mp hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply neg_equiv'!.mpr;
      exact imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;

lemma neg_unprovable_iff_insert_Consistent : T *⊬[𝓓]! ~p ↔ (𝓓)-Consistent (insert (p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Consistent.mpr;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Consistent.mp;

variable (hConsis : (𝓓)-Consistent T)

lemma unprovable_either : ¬(T *⊢[𝓓]! p ∧ T *⊢[𝓓]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[𝓓]! ⊥ := neg_mdp! hC₂ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : 𝓓 ⊬! List.conj' Γ ⟶ ⊥ := hConsis hΓ₁;
  have : 𝓓 ⊢! List.conj' Γ ⟶ ⊥ := FiniteContext.toₛ! hΓ₂;
  contradiction;

lemma not_provable_falsum : T *⊬[𝓓]! ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp $ hC;
  have : 𝓓 ⊬! List.conj' Γ ⟶ ⊥ := hConsis hΓ₁;
  have : 𝓓 ⊢! List.conj' Γ ⟶ ⊥ := hΓ₂;
  contradiction;

lemma not_mem_falsum_of_Consistent : ⊥ ∉ T := by
  by_contra hC;
  have : 𝓓 ⊬! ⊥ ⟶ ⊥ := hConsis (Γ := [⊥]) (by simpa);
  have : 𝓓 ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

lemma either_consistent (p) : (𝓓)-Consistent (insert p T) ∨ (𝓓)-Consistent (insert (~p) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_Inconsistent.mp hC.2;

  replace hΓ₂ := neg_equiv'!.mpr hΓ₂;
  replace hΔ₂ := neg_equiv'!.mpr hΔ₂;
  have : 𝓓 ⊢! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := neg_equiv'!.mp $ demorgan₁'! $ or₃'''! (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΔ₂) or₂!) lem!
  have : 𝓓 ⊬! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := unprovable_imp_trans''! imply_left_concat_conj'! (hConsis (by
    simp;
    intro q hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  ));
  contradiction;

lemma exists_maximal_Consistent_theory
  : ∃ Z, (𝓓)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (𝓓)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (𝓓)-Consistent T } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Consistent, Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . intro Γ;
      by_contra hC;
      obtain ⟨hΓs, hΓd⟩ := by simpa using hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : (𝓓)-Consistent U := hc hUc;
      have : ¬(𝓓)-Consistent U := by
        simp only [Consistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . intro p hp; exact hUs hp;
        . assumption;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T hConsis
protected alias lindenbaum := exists_maximal_Consistent_theory

open Classical in
lemma intro_union_Consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ T₁) → (∀ p ∈ Γ₂, p ∈ T₂) → 𝓓 ⊬! Γ₁.conj' ⋏ Γ₂.conj' ⟶ ⊥) : (𝓓)-Consistent (T₁ ∪ T₂) := by
  intro Δ hΔ;
  simp at hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : 𝓓 ⊬! Δ₁.conj' ⋏ Δ₂.conj' ⟶ ⊥ := @h Δ₁ Δ₂ (by intro _ h; simpa using List.of_mem_filter h) (by intro _ h; simpa using List.of_mem_filter h);
  exact unprovable_imp_trans''! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro q hq;
    cases (hΔ q hq);
    . exact iff_provable_list_conj.mp (and₁'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
    . exact iff_provable_list_conj.mp (and₂'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
  ) this;

lemma not_singleton_consistent [𝓓.HasNecessitation] (h : ~(□p) ∈ T) : (𝓓)-Consistent {~p} := by
  intro Γ hΓ;
  simp only [Set.mem_singleton_iff] at hΓ;
  by_contra hC;
  have : 𝓓 ⊢! ~(□p) ⟶ ⊥ := neg_equiv'!.mp $ dni'! $ nec! $ dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj'! hΓ hC;
  have : 𝓓 ⊬! ~(□p) ⟶ ⊥ := by simpa using hConsis (Γ := [~(□p)]) (by aesop)
  contradiction;

end Theory

structure MaximalConsistentTheory (𝓓 : DeductionParameter α) where
  theory : Theory α
  consistent : (𝓓)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(𝓓)-Consistent U

notation "(" 𝓓 ")-MCT" => MaximalConsistentTheory 𝓓

namespace MaximalConsistentTheory

open Theory

variable {𝓓 : DeductionParameter α}
variable {Ω Ω₁ Ω₂ : (𝓓)-MCT}
variable {p : Formula α}

lemma exists_maximal_Lconsistented_theory (consisT : (𝓓)-Consistent T) : ∃ Ω : (𝓓)-MCT, (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := Theory.lindenbaum consisT;
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

alias lindenbaum := exists_maximal_Lconsistented_theory

noncomputable instance [System.Consistent 𝓓] : Inhabited (𝓓)-MCT := ⟨lindenbaum self_Consistent |>.choose⟩

lemma either_mem (Ω : (𝓓)-MCT) (p) : p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent p with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(𝓓)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)

lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[𝓓]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω p); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[𝓓]! ~p := Context.by_axm! hC;
    have := neg_mdp! hnp hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

lemma subset_axiomset : Ax(𝓓) ⊆ Ω.theory := by
  intro p hp;
  apply membership_iff.mpr;
  apply Context.of!;
  exact Deduction.maxm! (by aesop);

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_Consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω.theory := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[𝓓]! ⊥ := by apply membership_iff.not.mp; simp

@[simp]
lemma iff_mem_neg : (~p ∈ Ω.theory) ↔ (p ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.theory *⊢[𝓓]! ⊥ := neg_mdp! hnp hp;
    have : Ω.theory *⊬[𝓓]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_Consistent.not.mp $ membership_iff.not.mp hp;
    have := (not_imp_not.mpr $ Ω.maximal (U := insert (~p) Ω.theory)) this;
    simp [Set.ssubset_def] at this;
    apply this;
    simp;

lemma iff_mem_negneg : (~~p ∈ Ω.theory) ↔ (p ∈ Ω.theory) := by
  simp [membership_iff];
  constructor;
  . intro h; exact dne'! h;
  . intro h; exact dni'! h;

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
    . apply membership_iff.mpr; exact and₁'! hpq;
    . apply membership_iff.mpr; exact and₂'! hpq;
  . rintro ⟨hp, hq⟩;
    apply membership_iff.mpr;
    exact and₃'! (membership_iff.mp hp) (membership_iff.mp hq);

@[simp]
lemma iff_mem_or : ((p ⋎ q) ∈ Ω.theory) ↔ (p ∈ Ω.theory) ∨ (q ∈ Ω.theory) := by
  constructor;
  . intro hpq;
    replace hpq := membership_iff.mp hpq;
    by_contra hC; simp [not_or] at hC;
    have ⟨hp, hq⟩ := hC;
    replace hp := membership_iff.mp $ iff_mem_neg.mpr hp;
    replace hq := membership_iff.mp $ iff_mem_neg.mpr hq;
    have : Ω.theory *⊢[𝓓]! ⊥ := or₃'''! (neg_equiv'!.mp hp) (neg_equiv'!.mp hq) hpq;
    have : Ω.theory *⊬[𝓓]! ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

lemma iff_congr : (Ω.theory *⊢[𝓓]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ and₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ and₂'! hpq) hq;

lemma mem_dn_iff : (p ∈ Ω.theory) ↔ (~~p ∈ Ω.theory) := iff_congr $ dn!

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

-- These lemmata require 𝓓 normality
section Normal

variable [𝓓.IsNormal]

lemma iff_mem_multibox : (□^[n]p ∈ Ω.theory) ↔ (∀ {Ω' : (𝓓)-MCT}, (□''⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (𝓓 := 𝓓) (T := insert (~p) (□''⁻¹^[n]Ω.theory)) (by
      apply unprovable_iff_insert_neg_Consistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : 𝓓 ⊢! □^[n]Γ.conj' ⟶ □^[n]p := imply_multibox_distribute'! hΓ₂;
      have : 𝓓 ⊬! □^[n]Γ.conj' ⟶ □^[n]p := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : 𝓓 ⊬! (□'^[n]Γ : List (Formula α)).conj' ⟶ □^[n]p := FiniteContext.provable_iff.not.mp $ this (□'^[n]Γ) (by
          intro q hq;
          obtain ⟨r, hr₁, hr₂⟩ := by simpa using hq;
          subst hr₂;
          simpa using hΓ₁ r hr₁;
        );
        revert this;
        contrapose;
        simp [neg_neg];
        exact imp_trans''! collect_multibox_conj'!;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : (𝓓)-MCT}, (□''⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

lemma multibox_dn_iff : (□^[n](~~p) ∈ Ω.theory) ↔ (□^[n]p ∈ Ω.theory) := by
  simp only [iff_mem_multibox];
  constructor;
  . intro h Ω hΩ; exact iff_mem_negneg.mp $ h hΩ;
  . intro h Ω hΩ; exact iff_mem_negneg.mpr $ h hΩ;

lemma box_dn_iff : (□~~p ∈ Ω.theory) ↔ (□p ∈ Ω.theory) := multibox_dn_iff (n := 1)

lemma mem_multibox_dual : □^[n]p ∈ Ω.theory ↔ ~(◇^[n](~p)) ∈ Ω.theory := by
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
lemma mem_box_dual : □p ∈ Ω.theory ↔ (~(◇(~p)) ∈ Ω.theory) := mem_multibox_dual (n := 1)

-- lemma multidia_dn_iff : (◇^[n](~~p) ∈ Ω.theory) ↔ (◇^[n]p ∈ Ω.theory) := by sorry

lemma dia_dn_iff : (◇~~p ∈ Ω.theory) ↔ (◇p) ∈ Ω.theory := neg_iff box_dn_iff -- TODO: multidia_dn_iff (n := 1)

lemma mem_multidia_dual : ◇^[n]p ∈ Ω.theory ↔ ~(□^[n](~p)) ∈ Ω.theory := by
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

end Normal

end MaximalConsistentTheory

end LO.Modal.Standard
