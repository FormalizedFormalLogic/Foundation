import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.HilbertStyle
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

variable {α : Type u} [DecidableEq α] [Inhabited α]

def Theory.ParametricConsistent (L : DeductionParameter α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → L ⊬! Γ.conj' ⟶ ⊥
notation:max "(" L ")-Consistent " T:90 => Theory.ParametricConsistent L T

variable {L : DeductionParameter α} [L.Normal]

open System
open Theory

namespace Theory

lemma self_ParametricConsistent [h : System.Consistent L] : (L)-Consistent Ax(L) := by
  intro Γ hΓ;
  obtain ⟨q, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : L ⊢! q := imp_trans! hC efq! ⨀ (iff_provable_list_conj.mpr $ λ _ h => ⟨Deduction.maxm $ hΓ _ h⟩);
  contradiction;

variable {T : Theory α}

lemma def_not_ParametricConsistent : ¬(L)-Consistent T ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ L ⊢! Γ.conj' ⟶ ⊥ := by simp [ParametricConsistent];

lemma union_ParametricConsistent : (L)-Consistent (T₁ ∪ T₂) → (L)-Consistent T₁ ∧ (L)-Consistent T₂ := by
  simp only [ParametricConsistent];
  intro h;
  constructor;
  . intro Γ hΓ; exact h (by intro p hp; simp; left; exact hΓ p hp);
  . intro Γ hΓ; exact h (by intro p hp; simp; right; exact hΓ p hp);

lemma union_not_Lconsistent : ¬(L)-Consistent T₁ ∨ ¬(L)-Consistent T₂ → ¬(L)-Consistent (T₁ ∪ T₂) := by
  contrapose;
  push_neg;
  exact union_ParametricConsistent;

lemma iff_insert_ParametricConsistent : (L)-Consistent (insert p T) ↔ ∀ {Γ : List (Formula α)}, (∀ q ∈ Γ, q ∈ T) → L ⊬! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . intro h Γ hΓ;
    by_contra hC;
    have : L ⊬! p ⋏ List.conj' Γ ⟶ ⊥ := implyLeft_cons_conj'!.not.mp $ @h (p :: Γ) (by
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
    have := imp_trans! andComm! $ implyLeftRemoveConj' (p := p) hC;
    contradiction;

lemma iff_insert_notParametricConsistent : ¬(L)-Consistent (insert p T) ↔ ∃ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ L ⊢! p ⋏ Γ.conj' ⟶ ⊥ := by
  constructor;
  . contrapose; push_neg; apply iff_insert_ParametricConsistent.mpr;
  . contrapose; push_neg; apply iff_insert_ParametricConsistent.mp;

lemma provable_iff_insert_neg_not_Lconsistent : T *⊢[L]! p ↔ ¬(L)-Consistent (insert (~p) T) := by
  constructor;
  . intro h;
    apply iff_insert_notParametricConsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . apply andImplyIffImplyImply'!.mpr;
      apply imp_swap'!;
      exact imp_trans! (FiniteContext.toDef'! hΓ₂) dni!;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notParametricConsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact FiniteContext.ofDef'! $ imp_trans! (imp_swap'! $ andImplyIffImplyImply'!.mp hΓ₂) dne!;

lemma unprovable_iff_insert_neg_ParametricConsistent : T *⊬[L]! p ↔ (L)-Consistent (insert (~p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Lconsistent.mpr;
  . contrapose; simp [not_not]; apply provable_iff_insert_neg_not_Lconsistent.mp;

lemma neg_provable_iff_insert_not_Lconsistent : T *⊢[L]! ~p ↔ ¬(L)-Consistent (insert (p) T) := by
  constructor;
  . intro h;
    apply iff_insert_notParametricConsistent.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    existsi Γ;
    constructor;
    . assumption;
    . apply andImplyIffImplyImply'!.mpr;
      apply imp_swap'!;
      exact FiniteContext.toDef'! hΓ₂;
  . intro h;
    apply Context.provable_iff.mpr;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notParametricConsistent.mp h;
    existsi Γ;
    constructor;
    . exact hΓ₁;
    . exact FiniteContext.ofDef'! $ imp_swap'! $ andImplyIffImplyImply'!.mp hΓ₂;

lemma neg_unprovable_iff_insert_ParametricConsistent : T *⊬[L]! ~p ↔ (L)-Consistent (insert (p) T) := by
  constructor;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Lconsistent.mpr;
  . contrapose; simp [not_not]; apply neg_provable_iff_insert_not_Lconsistent.mp;

variable (consisT : (L)-Consistent T)

lemma unprovable_either : ¬(T *⊢[L]! p ∧ T *⊢[L]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[L]! ⊥ := hC₂ ⨀ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : L ⊬! List.conj' Γ ⟶ ⊥ := consisT hΓ₁;
  have : L ⊢! List.conj' Γ ⟶ ⊥ := implyLeft_conj_eq_conj'!.mp $ FiniteContext.toₛ! hΓ₂;
  contradiction;

lemma not_provable_falsum : T *⊬[L]! ⊥ := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp $ hC;
  have : L ⊬! List.conj' Γ ⟶ ⊥ := consisT hΓ₁;
  have : L ⊢! List.conj' Γ ⟶ ⊥ := implyLeft_conj_eq_conj'!.mp hΓ₂;
  contradiction;

lemma not_mem_falsum_of_Lconsistent : ⊥ ∉ T := by
  by_contra hC;
  have : L ⊬! ⊥ ⟶ ⊥ := consisT (Γ := [⊥]) (by simpa);
  have : L ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

-- TODO: move
lemma unprovable_imp_trans! (hpq : L ⊢! p ⟶ q) : L ⊬! p ⟶ r → L ⊬! q ⟶ r := by
  contrapose; simp [neg_neg];
  exact imp_trans! hpq;

lemma either_consistent (p) : (L)-Consistent (insert p T) ∨ (L)-Consistent (insert (~p) T) := by
  by_contra hC; push_neg at hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := iff_insert_notParametricConsistent.mp hC.1;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := iff_insert_notParametricConsistent.mp hC.2;

  rw [←NegDefinition.neg] at hΓ₂ hΔ₂;
  have : L ⊢! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := demorgan₁'! $ disj₃'! (imp_trans! (implyOfNotOr'! $ demorgan₄'! hΓ₂) disj₁!) (imp_trans! (implyOfNotOr'! $ demorgan₄'! hΔ₂) disj₂!) lem!;
  have := @consisT (Γ ++ Δ) (by
    intro q hq;
    simp at hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  );
  have : L ⊬! Γ.conj' ⋏ Δ.conj' ⟶ ⊥ := unprovable_imp_trans! imply_left_concat_conj'! (consisT (by
    simp;
    intro q hq;
    rcases hq with hΓ | hΔ
    . exact hΓ₁ _ hΓ;
    . exact hΔ₁ _ hΔ;
  ));
  contradiction;

lemma exists_maximal_Lconsistent_theory
  : ∃ Z, (L)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (L)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (L)-Consistent T } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [ParametricConsistent, Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . intro Γ;
      by_contra hC;
      obtain ⟨hΓs, hΓd⟩ := by simpa using hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro p hp; simp_all);
      simp [List.coe_toFinset] at hUs;
      have : (L)-Consistent U := hc hUc;
      have : ¬(L)-Consistent U := by
        simp only [ParametricConsistent, not_forall, not_not, exists_prop];
        existsi Γ;
        constructor;
        . intro p hp; exact hUs hp;
        . assumption;
      contradiction;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T consisT


lemma intro_union_ParametricConsistent (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ T₁) → (∀ p ∈ Γ₂, p ∈ T₂) → L ⊬! Γ₁.conj' ⋏ Γ₂.conj' ⟶ ⊥) : (L)-Consistent (T₁ ∪ T₂) := by
  classical!;
  intro Δ hΔ;
  simp at hΔ;
  let Δ₁ := (Δ.filter (· ∈ T₁));
  let Δ₂ := (Δ.filter (· ∈ T₂));
  have := @h Δ₁ Δ₂ (by intro _ h; simpa using List.of_mem_filter h;) (by intro _ h; simpa using List.of_mem_filter h;)
  exact unprovable_imp_trans! (by
    apply FiniteContext.deduct'!;
    apply iff_provable_list_conj.mpr;
    intro q hq;
    cases (hΔ q hq);
    . exact iff_provable_list_conj.mp (conj₁'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
    . exact iff_provable_list_conj.mp (conj₂'! FiniteContext.id!) q $ List.mem_filter_of_mem hq (by simpa);
  ) this;


end Theory

structure MaximalParametricConsistentTheory (L : DeductionParameter α) where
  theory : Theory α
  consistent : (L)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(L)-Consistent U

alias MCT := MaximalParametricConsistentTheory

namespace MaximalParametricConsistentTheory

variable {Ω Ω₁ Ω₂ : MCT L}
variable {p : Formula α}

lemma exists_maximal_Lconsistented_theory (consisT : (L)-Consistent T) : ∃ (Ω : MCT L), (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := exists_maximal_Lconsistent_theory consisT;
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

noncomputable instance [System.Consistent L] : Inhabited (MCT L) := ⟨lindenbaum self_ParametricConsistent |>.choose⟩

lemma either_mem (Ω : MCT L) (p) : p ∈ Ω.theory ∨ ~p ∈ Ω.theory := by
  by_contra hC; push_neg at hC;
  cases either_consistent Ω.consistent p with
  | inl h => have := Ω.maximal (Set.ssubset_insert hC.1); contradiction;
  | inr h => have := Ω.maximal (Set.ssubset_insert hC.2); contradiction;

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(L)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)


lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[L]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by apply or_iff_not_imp_right.mp $ (either_mem Ω p); assumption;
    by_contra hC;
    have hnp : Ω.theory *⊢[L]! ~p := Context.by_axm! hC;
    have := hnp ⨀ hp;
    have := not_provable_falsum Ω.consistent;
    contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ Ω.theory := not_mem_falsum_of_Lconsistent Ω.consistent

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[L]! ⊥ := by apply membership_iff.not.mp; simp

lemma iff_mem_neg : (~p ∈ Ω.theory) ↔ (p ∉ Ω.theory) := by
  constructor;
  . intro hnp;
    by_contra hp;
    replace hp := membership_iff.mp hp;
    replace hnp := membership_iff.mp hnp;
    have : Ω.theory *⊢[L]! ⊥ := hnp ⨀ hp;
    have : Ω.theory *⊬[L]! ⊥ := unprovable_falsum;
    contradiction;
  . intro hp;
    have := provable_iff_insert_neg_not_Lconsistent.not.mp $ membership_iff.not.mp hp;
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
    have : Ω.theory *⊢[L]! ⊥ := disj₃'! hp hq hpq;
    have : Ω.theory *⊬[L]! ⊥ := unprovable_falsum;
    contradiction;
  . rintro (hp | hq);
    . apply membership_iff.mpr;
      exact disj₁'! (membership_iff.mp hp);
    . apply membership_iff.mpr;
      exact disj₂'! (membership_iff.mp hq);

lemma iff_mem_multibox : (□^[n]p ∈ Ω.theory) ↔ (∀ {Ω' : MCT L}, (□⁻¹^[n]Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'; apply hΩ'; simpa;
  . contrapose;
    push_neg;
    intro hp;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum (L := L) (T := insert (~p) (□⁻¹^[n]Ω.theory)) (by
      apply unprovable_iff_insert_neg_ParametricConsistent.mp;
      by_contra hC;
      obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
      have : L ⊢! □^[n]Γ.conj' ⟶ □^[n]p := imply_multibox_distribute'! $ implyLeft_conj_eq_conj'!.mp hΓ₂;
      have : L ⊬! □^[n]Γ.conj' ⟶ □^[n]p := by
        have := Context.provable_iff.not.mp $ membership_iff.not.mp hp;
        push_neg at this;
        have : L ⊬! (□^[n]Γ).conj' ⟶ □^[n]p := implyLeft_conj_eq_conj'!.not.mp $ FiniteContext.provable_iff.not.mp $ this (□^[n]Γ) (by
          intro q hq;
          obtain ⟨r, hr₁, hr₂⟩ := by simpa using hq;
          subst hr₂;
          simpa using hΓ₁ r hr₁;
        );
        revert this;
        contrapose;
        simp [neg_neg];
        exact imp_trans! collect_multibox_conj'!;
      contradiction;
    );
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]
lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : MCT L}, (□⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := iff_mem_multibox (n := 1)

lemma iff_congr : (Ω.theory *⊢[L]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
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
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₁'! multiboxDuality!);
  . intro h;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply Context.provable_iff.mpr;
    existsi Γ;
    constructor;
    . assumption;
    . exact FiniteContext.provable_iff.mpr $ imp_trans! (FiniteContext.provable_iff.mp hΓ₂) (conj₂'! multiboxDuality!);
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

-- lemma iff_mem_multidia_conj' : (◇^[n]Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, ◇^[n]p ∈ Ω.theory) := by sorry

-- lemma iff_mem_dia_conj' : (◇Γ.conj' ∈ Ω.theory) ↔ (∀ p ∈ Γ, ◇p ∈ Ω.theory) := iff_mem_multidia_conj' (n := 1)

end MaximalParametricConsistentTheory



open Formula
open MaximalParametricConsistentTheory

namespace Kripke

abbrev CanonicalFrame (L : DeductionParameter α) [Inhabited (MCT L)] : Frame (MCT L) α := λ Ω₁ Ω₂ => □⁻¹Ω₁.theory ⊆ Ω₂.theory

namespace CanonicalFrame

variable [Minimal L] [Inhabited (MCT L)]

@[simp]
lemma frame_def_box: (CanonicalFrame L) Ω₁ Ω₂ ↔ (∀ {p : Formula α}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory) := by rfl

lemma multiframe_def_multibox : ((CanonicalFrame L)^[n] Ω₁ Ω₂) ↔ ∀ {p : Formula α}, □^[n]p ∈ Ω₁.theory → p ∈ Ω₂.theory := by
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
      obtain ⟨Ω, hΩ⟩ := lindenbaum (L := L) (T := (□⁻¹Ω₁.theory ∪ ◇^[n]Ω₂.theory)) $ by
        apply intro_union_ParametricConsistent;
        intro Γ Δ hΓ hΔ hC;

        replace hΓ : ∀ p ∈ Γ, □p ∈ Ω₁.theory := by simpa using hΓ;
        have dΓconj : Ω₁.theory *⊢[L]! □Γ.conj' := membership_iff.mp $ iff_mem_box_conj'.mpr hΓ;

        have hΔ₂ : ∀ p ∈ ◇⁻¹^[n]Δ, p ∈ Ω₂.theory := by
          intro p hp;
          simpa using hΔ (◇^[n]p) (by simp_all);

        have hΔconj : (◇⁻¹^[n]Δ).conj' ∈ Ω₂.theory := iff_mem_conj'.mpr hΔ₂;

        have : L ⊢! Γ.conj' ⟶ □^[n](~(◇⁻¹^[n]Δ).conj') := imp_trans! (andImplyIffImplyImply'!.mp hC)
          $ contra₂'! $ imp_trans! (conj₂'! multidiaDuality!)
          $ imp_trans! iff_conj'multidia_multidiaconj'! $ by
            apply conj'conj'_subset;
            intro q hq;
            obtain ⟨r, _, _⟩ := by simpa using hΔ q hq;
            subst_vars;
            simpa;
        have : L ⊢! □Γ.conj' ⟶ □^[(n + 1)](~(◇⁻¹^[n]Δ).conj') := by simpa only [UnaryModalOperator.multimop_succ] using imply_box_distribute'! this;
        have : (◇⁻¹^[n]Δ).conj' ∉ Ω₂.theory := iff_mem_neg.mp $ h $ membership_iff.mpr $ (Context.of! this) ⨀ dΓconj;

        contradiction;
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

lemma multiframe_def_multibox' : ((CanonicalFrame L)^[n] Ω₁ Ω₂) ↔ ∀ {p : Formula α}, p ∈ (□⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multibox'' : ((CanonicalFrame L)^[n] Ω₁ Ω₂) ↔ ∀ {p : Formula α}, p ∈ (□⁻¹^[n]Ω₁.theory) → p ∈ Ω₂.theory := by
  constructor;
  . intro h p hp; exact multiframe_def_multibox.mp h hp;
  . intro h; apply multiframe_def_multibox.mpr; assumption;

lemma multiframe_def_multidia : (CanonicalFrame L)^[n] Ω₁ Ω₂ ↔ ∀ {p : Formula α}, (p ∈ Ω₂.theory → ◇^[n]p ∈ Ω₁.theory) := Iff.trans multiframe_def_multibox multibox_multidia

end CanonicalFrame


abbrev CanonicalModel (L : DeductionParameter α) [Inhabited (MCT L)] : Model (MCT L) α where
  frame := CanonicalFrame L
  valuation Ω a := (atom a) ∈ Ω.theory

namespace CanonicalModel

@[simp]
lemma val_def [Inhabited (MCT L)] : (CanonicalModel L).valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel

section

variable [Inhabited (MCT L)]

lemma truthlemma : ∀ {Ω : MCT L}, (CanonicalModel L, Ω) ⊧ p ↔ (p ∈ Ω.theory) := by
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
      exact CanonicalFrame.frame_def_box.mp hΩ' h;
  | _ => simp_all

lemma iff_valid_on_canonicalModel_deducible : (CanonicalModel L) ⊧ p ↔ (L ⊢! p) := by
  constructor;
  . contrapose;
    intro h;
    have : (L)-Consistent ({~p}) := by
      simp [ParametricConsistent];
      intro Γ hΓ;
      by_contra hC;
      have : L ⊢! p := dne'! $ replace_imply_left_conj'! hΓ hC;
      contradiction;
    obtain ⟨Ω, hΩ⟩ := lindenbaum this;
    simp [Kripke.ValidOnModel];
    existsi Ω;
    exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);
  . intro h Ω;
    suffices p ∈ Ω.theory by exact truthlemma.mpr this;
    by_contra hC;
    have := MaximalParametricConsistentTheory.maximal' hC;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Theory.iff_insert_notParametricConsistent.mp this;
    exact Ω.consistent hΓ₁ $ andImplyIffImplyImply'!.mp hΓ₂ ⨀ h;

lemma realize_axiomset_of_self_canonicalModel : CanonicalModel L ⊧* Ax(L) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  exact ⟨Deduction.maxm hp⟩;

@[simp]
lemma realize_theory_of_self_canonicalModel : CanonicalModel L ⊧* (System.theory L) := by
  apply Semantics.realizeSet_iff.mpr;
  intro p hp;
  apply iff_valid_on_canonicalModel_deducible.mpr;
  simpa [System.theory] using hp;

end

lemma validOnCanonicalModel_of_subset
  {L₁ L₂ : DeductionParameter α} [L₁.Normal] [L₂.Normal] [Inhabited (MCT L₁)] [Inhabited (MCT L₂)]
  (hRed : L₁ ≤ₛ L₂ := by simp) (h : CanonicalModel L₁ ⊧ p) : CanonicalModel L₂ ⊧ p :=
  iff_valid_on_canonicalModel_deducible.mpr $ hRed $ iff_valid_on_canonicalModel_deducible.mp h

class Canonical (L : DeductionParameter α) [Inhabited (MCT L)] where
  realize : (CanonicalFrame L) ⊧* Ax(L)

lemma complete!_on_frameclass_of_canonical [System.Consistent L] [Canonical L] : 𝔽(Ax(L)) ⊧ p → L ⊢! p := by
  simp [Kripke.ValidOnFrameClass, Kripke.ValidOnFrame];
  contrapose;
  push_neg;
  intro h;
  existsi MCT L, _, CanonicalFrame L;
  constructor;
  . apply Canonical.realize;
  . existsi (CanonicalModel L).valuation;
    exact iff_valid_on_canonicalModel_deducible.not.mpr h;

instance instComplete [System.Consistent L] [Canonical L] : Complete L 𝔽(Ax(L)) := ⟨complete!_on_frameclass_of_canonical⟩

def canonical_of_definability [Inhabited (MCT L)] (definability : Definability Ax(L) P) (h : P (CanonicalFrame L)) : Canonical L where
  realize := definability.defines _ _ |>.mpr h;

instance : Canonical (𝐊 : DeductionParameter α) := canonical_of_definability AxiomSet.K.definability trivial

-- TODO: inferInstanceで行けてほしいのだがなぜか通らないので明示的に指定している
instance : Complete (𝐊 : DeductionParameter α) 𝔽(Ax(𝐊)) := instComplete


end Kripke

end LO.Modal.Standard
