import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α] [Inhabited α]

open System

def Theory.Consistent (Λ : DeductionParameter α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → Λ ⊬! ⋀Γ ⟶ ⊥
notation:max "(" Λ ")-Consistent " T:90 => Theory.Consistent Λ T

namespace Theory

variable {Λ : DeductionParameter α} [Λ_consis : System.Consistent Λ]
         {T : Theory α}

@[simp]
lemma self_consistent : (Λ)-Consistent Ax(Λ) := by
  obtain ⟨q, hq⟩ := Λ_consis.exists_unprovable;
  intro Γ hΓ;
  by_contra hC;
  have : Λ ⊢! q := imp_trans''! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => Deduction.maxm! $ hΓ _ h);
  contradiction;

@[simp]
lemma emptyset_consistent : (Λ)-Consistent ∅ := by
  obtain ⟨f, hf⟩ := Λ_consis.exists_unprovable;
  intro Γ hΓ; by_contra hC;
  replace hΓ := List.nil_iff.mpr hΓ; subst hΓ;
  have : Λ ⊢! f := efq'! $ hC ⨀ verum!;
  contradiction;

lemma def_not_consistent : ¬(Λ)-Consistent T ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ Λ ⊢! ⋀Γ ⟶ ⊥ := by simp [Consistent];

lemma union_consistent : (Λ)-Consistent (T₁ ∪ T₂) → (Λ)-Consistent T₁ ∧ (Λ)-Consistent T₂ := by
  simp only [Consistent];
  intro h;
  constructor;
  . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
  . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);

lemma union_not_consistent : ¬(Λ)-Consistent T₁ ∨ ¬(Λ)-Consistent T₂ → ¬(Λ)-Consistent (T₁ ∪ T₂) := by
  contrapose;
  push_neg;
  exact union_consistent;

lemma iff_insert_consistent : (Λ)-Consistent (insert p T) ↔ ∀ {Γ : List (Formula α)}, (∀ q ∈ Γ, q ∈ T) → Λ ⊬! p ⋏ ⋀Γ ⟶ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have : Λ ⊬! p ⋏ ⋀Γ ⟶ ⊥ := implyLeft_cons_conj'!.not.mp $ @h (p :: Γ) (by
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

lemma iff_insert_Inconsistent : ¬(Λ)-Consistent (insert p T) ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ Λ ⊢! p ⋏ ⋀Γ ⟶ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_consistent.mpr;
  . contrapose; push_neg; apply iff_insert_consistent.mp;

lemma provable_iff_insert_neg_not_consistent : T *⊢[Λ]! p ↔ ¬(Λ)-Consistent (insert (~p) T) := by
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
    . have : Γ ⊢[Λ]! ~p ⟶ ⊥ := imp_swap'! $ and_imply_iff_imply_imply'!.mp hΓ₂;
      exact dne'! $ neg_equiv'!.mpr this;

lemma unprovable_iff_insert_neg_consistent : T *⊬[Λ]! p ↔ (Λ)-Consistent (insert (~p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_consistent.mpr;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_consistent.mp;

lemma unprovable_iff_singleton_neg_consistent : Λ ⊬! p ↔ (Λ)-Consistent {~p} := by
  have e : insert (~p) ∅ = ({~p} : Theory α) := by aesop;
  have H := unprovable_iff_insert_neg_consistent (Λ := Λ) (T := ∅) (p := p);
  rw [e] at H;
  exact Iff.trans Context.emptyPrf!.symm.not H;

lemma neg_provable_iff_insert_not_consistent : T *⊢[Λ]! ~p ↔ ¬(Λ)-Consistent (insert (p) T) := by
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

lemma neg_unprovable_iff_insert_consistent : T *⊬[Λ]! ~p ↔ (Λ)-Consistent (insert (p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_consistent.mpr;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_consistent.mp;

variable (hConsis : (Λ)-Consistent T)

lemma unprovable_either : ¬(T *⊢[Λ]! p ∧ T *⊢[Λ]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[Λ]! ⊥ := neg_mdp! hC₂ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : Λ ⊬! ⋀Γ ⟶ ⊥ := hConsis hΓ₁;
  have : Λ ⊢! ⋀Γ ⟶ ⊥ := FiniteContext.toₛ! hΓ₂;
  contradiction;

lemma not_provable_falsum : T *⊬[Λ]! ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp $ hC;
  have : Λ ⊬! ⋀Γ ⟶ ⊥ := hConsis hΓ₁;
  have : Λ ⊢! ⋀Γ ⟶ ⊥ := hΓ₂;
  contradiction;

lemma not_mem_falsum_of_consistent : ⊥ ∉ T := by
  by_contra hC;
  have : Λ ⊬! ⊥ ⟶ ⊥ := hConsis (Γ := [⊥]) (by simpa);
  have : Λ ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

lemma either_consistent (p) : (Λ)-Consistent (insert p T) ∨ (Λ)-Consistent (insert (~p) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_Inconsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_Inconsistent.mp hC.2;

  replace hΓ₂ := neg_equiv'!.mpr hΓ₂;
  replace hΔ₂ := neg_equiv'!.mpr hΔ₂;
  have : Λ ⊢! ⋀Γ ⋏ ⋀Δ ⟶ ⊥ := neg_equiv'!.mp $ demorgan₁'! $ or₃'''! (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΓ₂) or₁!) (imp_trans''! (imply_of_not_or'! $ demorgan₄'! hΔ₂) or₂!) lem!
  have : Λ ⊬! ⋀Γ ⋏ ⋀Δ ⟶ ⊥ := unprovable_imp_trans''! imply_left_concat_conj'! (hConsis (by
    simp;
    intro q hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  ));
  contradiction;

lemma exists_maximal_consistent_theory
  : ∃ Z, (Λ)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (Λ)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (Λ)-Consistent T } (by
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
      have : (Λ)-Consistent U := hc hUc;
      have : ¬(Λ)-Consistent U := by
        simp only [Consistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . intro p hp; exact hUs hp;
        . assumption;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T hConsis
protected alias lindenbaum := exists_maximal_consistent_theory

open Classical in
lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ T₁) → (∀ p ∈ Γ₂, p ∈ T₂) → Λ ⊬! ⋀Γ₁ ⋏ ⋀Γ₂ ⟶ ⊥) : (Λ)-Consistent (T₁ ∪ T₂) := by
  intro Δ hΔ;
  simp at hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have : Λ ⊬! ⋀Δ₁ ⋏ ⋀Δ₂ ⟶ ⊥ := @h Δ₁ Δ₂ (by intro _ h; simpa using List.of_mem_filter h) (by intro _ h; simpa using List.of_mem_filter h);
  exact unprovable_imp_trans''! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro q hq;
    cases (hΔ q hq);
    . exact iff_provable_list_conj.mp (and₁'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
    . exact iff_provable_list_conj.mp (and₂'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
  ) this;

lemma not_singleton_consistent [Λ.HasNecessitation] (h : ~(□p) ∈ T) : (Λ)-Consistent {~p} := by
  intro Γ hΓ;
  simp only [Set.mem_singleton_iff] at hΓ;
  by_contra hC;
  have : Λ ⊢! ~(□p) ⟶ ⊥ := neg_equiv'!.mp $ dni'! $ nec! $ dne'! $ neg_equiv'!.mpr $ replace_imply_left_conj'! hΓ hC;
  have : Λ ⊬! ~(□p) ⟶ ⊥ := by simpa using hConsis (Γ := [~(□p)]) (by aesop)
  contradiction;

end Theory

structure MaximalConsistentTheory (Λ : DeductionParameter α) where
  theory : Theory α
  consistent : (Λ)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(Λ)-Consistent U

instance : CoeSort (@MaximalConsistentTheory α Λ) (Theory α) := ⟨MaximalConsistentTheory.theory⟩

notation "(" Λ ")-MCT" => MaximalConsistentTheory Λ

namespace MaximalConsistentTheory

open Theory

variable {Λ : DeductionParameter α}
variable {Ω Ω₁ Ω₂ : (Λ)-MCT}
variable {p : Formula α}

lemma exists_maximal_Lconsistented_theory (consisT : (Λ)-Consistent T) : ∃ Ω : (Λ)-MCT, T ⊆ Ω := by
  have ⟨Ω, Ω_consis, Ω_subset, Ω_maximal⟩ := Theory.lindenbaum consisT;
  use {
    theory := Ω,
    consistent := Ω_consis,
    maximal := by
      rintro U ⟨hU₁, hU₂⟩;
      by_contra hC;
      have : U = Ω := Ω_maximal U hC hU₁;
      subst_vars;
      simp at hU₂,
  };

alias lindenbaum := exists_maximal_Lconsistented_theory

noncomputable instance [System.Consistent Λ] : Inhabited (Λ)-MCT := ⟨lindenbaum emptyset_consistent |>.choose⟩

lemma either_mem (Ω : (Λ)-MCT) (p) : p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent p with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(Λ)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)

lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω *⊢[Λ]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω p); assumption;
    by_contra hC;
    have hnp : Ω *⊢[Λ]! ~p := Context.by_axm! hC;
    have := neg_mdp! hnp hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

lemma subset_axiomset : Ax(Λ) ⊆ Ω := by
  intro p hp;
  apply membership_iff.mpr;
  apply Context.of!;
  exact Deduction.maxm! (by aesop);

@[simp] lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_consistent Ω.consistent

@[simp] lemma mem_verum : ⊤ ∈ Ω.theory := by apply membership_iff.mpr; apply verum!;

@[simp]
lemma unprovable_falsum : Ω *⊬[Λ]! ⊥ := by apply membership_iff.not.mp; simp

@[simp]
lemma iff_mem_neg : (~p ∈ Ω.theory) ↔ (p ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω *⊢[Λ]! ⊥ := neg_mdp! hnp hp;
    have : Ω *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_consistent.not.mp $ membership_iff.not.mp hp;
    have := (not_imp_not.mpr $ Ω.maximal (U := insert (~p) Ω)) this;
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
    have : Ω *⊢[Λ]! ⊥ := or₃'''! (neg_equiv'!.mp hp) (neg_equiv'!.mp hq) hpq;
    have : Ω *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact or₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact or₂'! (membership_iff.mp hq);

lemma iff_congr : (Ω *⊢[Λ]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
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

-- These lemmata require Λ normality
section Normal

variable [Λ.IsNormal]

lemma iff_mem_multibox : (□^[n]p ∈ Ω.theory) ↔ (∀ {Ω' : (Λ)-MCT}, (□''⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (Λ := Λ) (T := insert (~p) (□''⁻¹^[n]Ω)) (by
      apply unprovable_iff_insert_neg_consistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : Λ ⊢! □^[n]⋀Γ ⟶ □^[n]p := imply_multibox_distribute'! hΓ₂;
      have : Λ ⊬! □^[n]⋀Γ ⟶ □^[n]p := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : Λ ⊬! ⋀□'^[n]Γ ⟶ □^[n]p := FiniteContext.provable_iff.not.mp $ this (□'^[n]Γ) (by
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

lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : (Λ)-MCT}, (□''⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

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

lemma iff_mem_conj' : (⋀Γ ∈ Ω.theory) ↔ (∀ p ∈ Γ, p ∈ Ω.theory) := by simp [membership_iff, iff_provable_list_conj];

lemma iff_mem_multibox_conj' : (□^[n]⋀Γ ∈ Ω.theory) ↔ (∀ p ∈ Γ, □^[n]p ∈ Ω.theory) := by
  simp only [iff_mem_multibox, iff_mem_conj'];
  constructor;
  . intro h p hp Ω' hΩ';
    exact (h hΩ') p hp;
  . intro h Ω' hΩ' p hp;
    exact @h p hp Ω' hΩ';

lemma iff_mem_box_conj' : (□⋀Γ ∈ Ω.theory) ↔ (∀ p ∈ Γ, □p ∈ Ω.theory) := iff_mem_multibox_conj' (n := 1)

end Normal

end MaximalConsistentTheory

end LO.Modal.Standard
