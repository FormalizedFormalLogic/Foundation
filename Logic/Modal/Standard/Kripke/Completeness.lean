import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Kripke.Completeness

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {𝓢 : S} {p q r : F} {Γ Δ : List F} {T : Set F}
variable [Minimal 𝓢] [NegDefinition F]

open FiniteContext

lemma FiniteContext.of'! (h : 𝓢 ⊢! p) : Γ ⊢[𝓢]! p := weakening! (by simp) $ provable_iff_provable.mp h
lemma FiniteContext.toₛ! (b : Γ ⊢[𝓢]! p) : 𝓢 ⊢! Γ.conj ⟶ p := b

lemma implyLeft_conj_eq_conj' : 𝓢 ⊢! Γ.conj ⟶ p ↔ 𝓢 ⊢! Γ.conj' ⟶ p := implyLeftReplaceIff'! (by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q =>
    simp;
    apply iff_intro! (by simp) (by
      apply provable_iff_provable.mpr;
      apply deduct_iff.mpr;
      exact conj₃'! (by_axm! (by simp)) (by simp)
    );
  | hcons q Γ hΓ ih =>
    simp [(List.conj'_cons_nonempty (a := q) hΓ)];
    apply iff_intro!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have d : [q ⋏ List.conj Γ] ⊢[𝓢]! q ⋏ List.conj Γ := by_axm! (by simp);
        exact conj₃'! (conj₁'! d) ((of'! $ conj₁'! ih) ⨀ (conj₂'! d))
      )
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have d : [q ⋏ List.conj' Γ] ⊢[𝓢]! q ⋏ List.conj' Γ := by_axm! (by simp);
        exact conj₃'! (conj₁'! d) ((of'! $ conj₂'! ih) ⨀ (conj₂'! d))
      )
  )

@[simp]
lemma dn_iff! [NegDefinition F] [HasDNE 𝓢] : 𝓢 ⊢! p ⟷ ~~p := iff_intro! (by simp) (by simp)

lemma supplemental1 [NegDefinition F] [HasEFQ 𝓢] (h : 𝓢 ⊢! ~p) : 𝓢 ⊢! p ⟶ q := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [p] ⊢[𝓢]! p ⟶ ⊥ := by simpa [NegDefinition.neg] using of'! h;
  have dp : [p] ⊢[𝓢]! p := by_axm! (by simp);
  exact efq'! (dnp ⨀ dp);

namespace Context

lemma by_axm! {p} (h : p ∈ T) : T *⊢[𝓢]! p := by
  apply provable_iff.mpr;
  existsi {p};
  constructor;
  . intro q hq; have := Finset.mem_singleton.mp hq; subst_vars; simpa;
  . exact FiniteContext.by_axm! (by tauto)

end Context

end LO.System


namespace LO.Modal.Standard

variable [DecidableEq α]

@[simp]
def Theory.ΛConsistent (Λ : AxiomSet α) (T : Theory α) := ∀ {Γ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → Λ ⊬! Γ.conj' ⟶ ⊥
notation:max "(" Λ ")-Consistent " T:90 => Theory.ΛConsistent Λ T

variable {Λ : AxiomSet α}

open System
open Theory

namespace Theory

variable {T : Theory α} (consisT : (Λ)-Consistent T)

lemma unprovable_either : ¬(T *⊢[Λ]! p ∧ T *⊢[Λ]! ~p) := by
  by_contra hC;
  have ⟨hC₁, hC₂⟩ := hC;
  have : T *⊢[Λ]! ⊥ := hC₂ ⨀ hC₁;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp this;
  have : Λ ⊬! List.conj' Γ ⟶ ⊥ := consisT hΓ₁;
  have : Λ ⊢! List.conj' Γ ⟶ ⊥ := implyLeft_conj_eq_conj'.mp $ FiniteContext.toₛ! hΓ₂;
  contradiction;


lemma provable_iff_insert_neg_not_Λconsistent : T *⊢[Λ]! p ↔ ¬(Λ)-Consistent (insert (~p) T) := by sorry;

lemma neg_provable_iff_insert_not_Λconsistent : T *⊢[Λ]! ~p ↔ ¬(Λ)-Consistent (insert (p) T) := by sorry;


lemma not_provable_falsum : Λ ⊬! ⊥ := by
  by_contra hC;
  have : Λ ⊢! ⊤ ⟶ ⊥ := dhyp! hC;
  have : Λ ⊬! ⊤ ⟶ ⊥ := by simpa [Finset.conj] using consisT (Γ := []) (by simp);
  contradiction;

lemma not_mem_falsum_of_Λconsistent : ⊥ ∉ T := by
  by_contra hC;
  have : Λ ⊬! ⊥ ⟶ ⊥ := consisT (Γ := [⊥]) (by simpa);
  have : Λ ⊢! ⊥ ⟶ ⊥ := efq!;
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

end Theory

structure MaximalConsistentByTheory (Λ : AxiomSet α) where
  theory : Theory α
  consistent : (Λ)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(Λ)-Consistent U

alias MCT := MaximalConsistentByTheory

namespace MaximalConsistentByTheory

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
      simp at hU₂;
  ⟩;
  simp_all only [ΛConsistent];

alias lindenbaum := exists_maximal_Λconsistented_theory

lemma maximal' {p : Formula α} (hp : p ∉ Ω.theory) : ¬(Λ)-Consistent (insert p Ω.theory) := Ω.maximal (Set.ssubset_insert hp)


lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! p) := by
  constructor;
  . intro h;
    exact Context.by_axm! h;
  . intro hp;
    by_contra hC;

    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := hp;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := neg_provable_iff_insert_not_Λconsistent.mpr $ Ω.maximal (Set.ssubset_insert hC);

    replace hΓ₂ : (Γ ++ Δ) ⊢[Λ]! p := FiniteContext.weakening! (by simp) ⟨hΓ₂⟩
    replace hΔ₂ : (Γ ++ Δ) ⊢[Λ]! ~p := FiniteContext.weakening! (by simp) ⟨hΔ₂⟩

    have : Λ ⊢! List.conj' (Γ ++ Δ) ⟶ ⊥ := implyLeft_conj_eq_conj'.mp $ FiniteContext.provable_iff.mp (hΔ₂ ⨀ hΓ₂);
    have : Λ ⊬! List.conj' (Γ ++ Δ) ⟶ ⊥ := Ω.consistent (by simp; rintro q (hq₁ | hq₂); exact hΓ₁ _ hq₁; exact hΔ₁ _ hq₂);
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
      exact supplemental1 $ membership_iff.mp $ iff_mem_neg.mpr h;
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

lemma iff_mem_box : (□p ∈ Ω.theory) ↔ (∀ {Ω' : MCT Λ}, (□⁻¹Ω.theory ⊆ Ω'.theory) → (p ∈ Ω'.theory)) := by
  constructor;
  . intro hp Ω' hΩ'
    apply hΩ';
    simpa;
  . contrapose;
    intro hp;
    have : (Λ)-Consistent (insert (~p) (□⁻¹Ω.theory)) := by sorry;
    obtain ⟨Ω', hΩ'⟩ := lindenbaum this;
    push_neg;
    existsi Ω';
    constructor;
    . exact Set.Subset.trans (by simp_all) hΩ';
    . apply iff_mem_neg.mp;
      apply hΩ';
      simp only [Set.mem_insert_iff, true_or]

lemma iff_congr : (Ω.theory *⊢[Λ]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
  intro hpq;
  constructor;
  . intro hp; exact iff_mem_imp.mp (membership_iff.mpr $ conj₁'! hpq) hp;
  . intro hq; exact iff_mem_imp.mp (membership_iff.mpr $ conj₂'! hpq) hq;

lemma mem_dn_iff : (p ∈ Ω.theory) ↔ (~~p ∈ Ω.theory) := iff_congr $ (by simp)

end MaximalConsistentByTheory


open Formula
open MaximalConsistentByTheory

namespace Kripke

def CanonicalModel (Λ : AxiomSet α) : Model (MCT Λ) α where
  frame (Ω₁ Ω₂) := □⁻¹Ω₁.theory ⊆ Ω₂.theory
  valuation Ω a := (atom a) ∈ Ω.theory

abbrev CanonicalFrame (Λ : AxiomSet α) : Frame (MCT Λ) α := CanonicalModel Λ |>.frame

namespace CanonicalModel

@[simp]
lemma frame_def: (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (∀ {p : Formula α}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory) := by rfl

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
      simp [Set.subset_def, CanonicalModel.frame_def] at hΩ';
      exact hΩ' h;
  | _ => simp_all

lemma deducible_of_validOnCanonicelModel : (CanonicalModel Λ) ⊧ p → (Λ ⊢! p) := by
  contrapose;
  intro h;
  have : (Λ)-Consistent ({~p}) := by sorry;
  obtain ⟨Ω, hΩ⟩ := lindenbaum this;
  simp [Kripke.ValidOnModel];
  existsi Ω;
  exact truthlemma.not.mpr $ iff_mem_neg.mp (show ~p ∈ Ω.theory by simp_all);

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

instance [Canonical Λ] : Complete (Λ : AxiomSet α) 𝔽(Λ, MCT Λ) := ⟨complete!_of_canonically⟩

instance : Canonical (𝐊 : AxiomSet α) where
  definability := AxiomSet.K.definability
  satisfy := by simp;

instance : Complete (𝐊 : AxiomSet α) 𝔽((𝐊 : AxiomSet α), MCT (𝐊 : AxiomSet α)) := inferInstance

end Kripke

end LO.Modal.Standard
