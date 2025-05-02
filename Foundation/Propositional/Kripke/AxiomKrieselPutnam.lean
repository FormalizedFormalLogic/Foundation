import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Entailment.Cl

section

variable {α : Sort*} (R : α → α → Prop)

def KrieselPutnamCondition :=
  ∀ x y z,
  (R x y ∧ R x z ∧ ¬R y z ∧ ¬R z y) →
  (∃ u, R x u ∧ R u y ∧ R u z ∧ (∀ v, R u v → ∃ w, R v w ∧ (R y w ∨ R z w)))

class SufficesKriselPutnamCondition (α) (R : α → α → Prop) : Prop where
  kpCondition : KrieselPutnamCondition R

end


namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

open Formula (atom)

lemma validate_KrieselPutnam_of_KrieselPutnamCondition : KrieselPutnamCondition F → F ⊧ (Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)) := by
  intro hKP V x y Rxy h₁;
  by_contra hC;
  replace hC := Satisfies.or_def.not.mp hC;
  push_neg at hC;
  obtain ⟨h₂, h₃⟩ := hC;

  replace h₂ := Satisfies.imp_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z₁, Ryz₁, ⟨hz₁₁, hz₁₂⟩⟩ := h₂;

  replace h₃ := Satisfies.imp_def.not.mp h₃;
  push_neg at h₃;
  obtain ⟨z₂, Ryz₂, ⟨hz₂₁, hz₂₂⟩⟩ := h₃;

  obtain ⟨u, Ryu, ⟨Ruz₁, Ruz₂, h⟩⟩ := hKP y z₁ z₂ ⟨
    Ryz₁, Ryz₂,
    by
      rcases Satisfies.or_def.mp $ h₁ Ryz₁ hz₁₁ with (h | h);
      . exfalso; exact hz₁₂ h;
      . by_contra hC; exact hz₂₂ $ Satisfies.formula_hereditary hC h;
    ,
    by
      rcases Satisfies.or_def.mp $ h₁ Ryz₂ hz₂₁ with (h | h);
      . by_contra hC; exact hz₁₂ $ Satisfies.formula_hereditary hC h;
      . exfalso; exact hz₂₂ h;
  ⟩;

  have : ¬Satisfies ⟨F, V⟩ u (∼(.atom 0)) := by
    by_contra hC;
    rcases Satisfies.or_def.mp $ h₁ Ryu hC with (h | h);
    . apply hz₁₂; exact Satisfies.formula_hereditary Ruz₁ h;
    . apply hz₂₂; exact Satisfies.formula_hereditary Ruz₂ h;
  replace this := Satisfies.neg_def.not.mp this;
  push_neg at this;
  obtain ⟨v, Ruv, hv⟩ := this;

  obtain ⟨w, Rvw, (Rz₁w | Rz₂w)⟩ := h v Ruv;
  . exact Satisfies.not_of_neg (Satisfies.formula_hereditary (φ := (∼(.atom 0))) Rz₁w hz₁₁) $ Satisfies.formula_hereditary Rvw hv;
  . exact Satisfies.not_of_neg (Satisfies.formula_hereditary (φ := (∼(.atom 0))) Rz₂w hz₂₁) $ Satisfies.formula_hereditary Rvw hv;

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

namespace Canonical

instance [Entailment.HasAxiomKrieselPutnam 𝓢] : SufficesKriselPutnamCondition _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz, nRyz, nRzy⟩;
  obtain ⟨u, hu₁, hu₂⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨x.1.1 ∪ ({ φ | ∼φ ∈ (y.1.1 ∩ z.1.1)}.image (∼·)), y.1.2 ∪ z.1.2⟩) $ by
    sorry;
  replace hu₂ := Set.union_subset_iff.mp hu₂;
  use u;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . exact Set.union_subset_iff.mp hu₁ |>.1;
  . apply Kripke.canonicalFrame.rel₂.mpr; exact hu₂ |>.1;
  . apply Kripke.canonicalFrame.rel₂.mpr; exact hu₂ |>.2;
  . intro v Ruv;
    by_contra hC;
    push_neg at hC;
    obtain ⟨γ₁, hγ₁₁, hγ₁₂⟩ : ∃ γ₁ ∈ v.1.1, ∼γ₁ ∈ y.1.1 := by
      have : Tableau.Inconsistent 𝓢 ⟨y.1.1 ∪ v.1.1, ∅⟩ := by
        by_contra hconsis;
        obtain ⟨t, ht⟩ := lindenbaum hconsis;
        apply hC t ?_ |>.1;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.1;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.2;
      dsimp [Tableau.Inconsistent, Tableau.Consistent] at this;
      push_neg at this;
      obtain ⟨Γ, Δ, h₁, h₂, h₃⟩ := this;
      use ⋀(Γ.filter (· ∈ v.1.1));
      constructor;
      . apply iff_mem₁_conj.mpr; simp;
      . apply iff_provable_include₁ (T := {x ∈ Γ | x ∈ y.1.1}) |>.mp ?_ y ?_;
        . have : Δ = [] := by sorry;
          subst this;

          simp at h₃;
          replace h₃ := Context.of! (Γ := insert (⋀(Γ.filter (· ∈ v.1.1))) {x | x ∈ Γ ∧ x ∈ y.1.1}) h₃;
          apply Context.deduct!;
          exact h₃ ⨀ by
            apply Conj₂!_iff_forall_provable.mpr;
            intro φ hφ;
            rcases h₁ φ hφ with (h | h);
            . apply Context.by_axm!;
              tauto;
            . sorry;
        . intro φ hφ;
          simp only [List.toFinset_filter, decide_eq_true_eq, Finset.coe_filter, List.mem_toFinset, Set.mem_setOf_eq] at hφ;
          exact hφ.2;
    obtain ⟨γ₂, hγ₂₁, hγ₂₂⟩ : ∃ γ₂ ∈ v.1.1, ∼γ₂ ∈ z.1.1 := by sorry;
    simp only [Set.mem_inter_iff, Set.union_subset_iff, Set.image_subset_iff] at hu₁;
    have : ∼(γ₁ ⋏ γ₂) ∈ v.1.1 := Ruv $ hu₁.2 $ by
      constructor <;>
      . apply SaturatedConsistentTableau.mdp_mem₁_provable CANNNK!;
        apply SaturatedConsistentTableau.iff_mem₁_or.mpr;
        tauto;
    apply SaturatedConsistentTableau.of_mem₁_neg' this;
    apply SaturatedConsistentTableau.iff_mem₁_and.mpr;
    tauto;
⟩

end Canonical

end canonicality

end Kripke

end LO.Propositional
