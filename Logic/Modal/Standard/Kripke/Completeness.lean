import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Kripke.Completeness

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {𝓢 : S}
variable [Minimal 𝓢]

lemma dhyp! (q : F) (b : 𝓢 ⊢! p) : 𝓢 ⊢! q ⟶ p := ⟨dhyp q b.some⟩

namespace Context

lemma by_axm! {p} (h : p ∈ Γ) : Γ *⊢[𝓢]! p := by
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
def Theory.ΛConsistent (Λ : AxiomSet α) (T : Theory α) := ∀ Γ : List (Formula α), (∀ p ∈ Γ, p ∈ T) → Λ ⊬! Γ.conj ⟶ ⊥
notation:max "(" Λ ")-Consistent " T:90 => Theory.ΛConsistent Λ T

variable {Λ : AxiomSet α}
variable {T : Theory α} (consisT : (Λ)-Consistent T)

open System
open Theory

namespace Theory

variable (consisT : (Λ)-Consistent T)

lemma not_provable_falsum : Λ ⊬! ⊥ := by
  by_contra hC;
  have : Λ ⊢! ⊤ ⟶ ⊥ := dhyp! ⊤ hC;
  have : Λ ⊬! ⊤ ⟶ ⊥ := by simpa [Finset.conj] using consisT ∅ (by simp);
  contradiction;

lemma not_mem_falsum_of_Λconsistent : ⊥ ∉ T := by
  by_contra hC;
  have : Λ ⊬! ⊥ ⟶ ⊥ := implyLeftConjSingleton!.not.mp $ consisT _ (by simpa);
  have : Λ ⊢! ⊥ ⟶ ⊥ := efq!;
  contradiction;

end Theory

lemma exists_maximal_consistent_theory :
  ∃ Z, (Λ)-Consistent Z ∧ T ⊆ Z ∧ ∀ U, (Λ)-Consistent U → Z ⊆ U → U = Z
  := zorn_subset_nonempty { T : Theory α | (Λ)-Consistent T } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [ΛConsistent, Set.mem_setOf_eq, Set.mem_sUnion];
    constructor;
    . by_contra hC;
      obtain ⟨Γ, hΓs, hΓd⟩ := by simpa using hC;
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

structure MaximalConsistentByTheory (Λ : AxiomSet α) where
  theory : Theory α
  consistent : (Λ)-Consistent theory
  maximal : ∀ {U}, theory ⊂ U → ¬(Λ)-Consistent U

alias MCT := MaximalConsistentByTheory

namespace MaximalConsistentByTheory

variable {Ω Ω₁ Ω₂ : MCT Λ}
variable {p : Formula α}

@[simp]
lemma unprovable_falsum : Ω.theory *⊬[Λ]! ⊥ := by
  have := Theory.not_provable_falsum Ω.consistent;
  by_contra hC;
  have := Context.provable_iff.mp hC;
  sorry;

lemma membership_iff : (p ∈ Ω.theory) ↔ (Ω.theory *⊢[Λ]! p) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices ~p ∉ Ω.theory by sorry;
    by_contra hC;
    have hnp : Ω.theory *⊢[Λ]! ~p := Context.by_axm! hC;
    have : Ω.theory *⊢[Λ]! ⊥ := hnp ⨀ hp;
    have : Ω.theory *⊬[Λ]! ⊥ := unprovable_falsum;
    contradiction;

lemma iff_congr : (Ω.theory *⊢[Λ]! (p ⟷ q)) → ((p ∈ Ω.theory) ↔ (q ∈ Ω.theory)) := by
  simp only [LogicalConnective.iff];
  intro hpq;
  constructor;
  . intro hp;
    exact membership_iff.mpr $ (conj₁'! hpq) ⨀ (membership_iff.mp hp)
  . intro hq;
    exact membership_iff.mpr $ (conj₂'! hpq) ⨀ (membership_iff.mp hq)

lemma mem_dn_iff : (p ∈ Ω.theory) ↔ (~~p ∈ Ω.theory) := iff_congr $ (by sorry)

end MaximalConsistentByTheory

lemma exists_maximal_consistented_theory : ∃ (Ω : MCT Λ), (T ⊆ Ω.theory) := by
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := exists_maximal_consistent_theory consisT;
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

alias lindenbaum := exists_maximal_consistented_theory

open Formula

namespace Kripke

def CanonicalModel (Λ : AxiomSet α) : Model (MCT Λ) α where
  frame (Ω₁ Ω₂) := □⁻¹Ω₁.theory ⊆ Ω₂.theory
  valuation Ω a := (atom a) ∈ Ω.theory

namespace CanonicalModel

lemma frame_def: (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (∀ {p : Formula α}, □p ∈ Ω₁.theory → p ∈ Ω₂.theory) := by rfl

@[simp]
lemma val_def {a : α} : (CanonicalModel Λ).valuation Ω a ↔ (atom a) ∈ Ω.theory := by rfl

end CanonicalModel

lemma truthlemma {p : Formula α} : ∀ {Ω : MCT Λ}, ((CanonicalModel Λ, Ω) ⊧ p) ↔ (p ∈ Ω.theory) := by
  sorry;
  /-
  induction p using Formula.rec' with
  | hatom => simp;
  | hfalsum => simp;
  | himp => simp_all [imp_membership_iff'];
  | hor => simp_all [or_membership_iff];
  | hand => simp_all [and_membership_iff];
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply (mct_mem_box_iff hK).mpr;
      intro Ω' hΩ';
      apply ih.mp;
      simp [Satisfies.box_def] at h;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      simp [Set.subset_def, CanonicalModel.frame_def] at hΩ';
      exact hΩ' h;
  -/

end Kripke

end LO.Modal.Standard
