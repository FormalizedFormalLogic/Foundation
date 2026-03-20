module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Vorspiel.Rel.Euclidean
public import Foundation.Propositional.Entailment.KreiselPutnam
public import Foundation.Propositional.Kripke3.Logic.Int.Completeness

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

class KreiselPutnam (M : KripkeModel κ α) extends M.Intuitionistic where
  kreisel_putnam :
    ∀ x y z : M.world,
    (x ≺ y ∧ x ≺ z ∧ ¬y ≺ z ∧ ¬z ≺ y) →
    (∃ u, x ≺ u ∧ u ≺ y ∧ u ≺ z ∧ (∀ v, u ≺ v → ∃ w, v ≺ w ∧ (y ≺ w ∨ z ≺ w)))

export KreiselPutnam (kreisel_putnam)

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomKreiselPutnam_of_satisfiesKreiselPutnamCondition
  [M.KreiselPutnam] : M ⊧ (Axioms.KreiselPutnam φ ψ χ) := by
  intro x y Rxy h₁;
  apply forces_or.mpr;
  by_contra! hC;
  obtain ⟨h₂, h₃⟩ := hC;

  replace h₂ := forces_imp.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z₁, Ryz₁, ⟨hz₁φ, hz₁ψ⟩⟩ := h₂;

  replace h₃ := forces_imp.not.mp h₃;
  push_neg at h₃;
  obtain ⟨z₂, Ryz₂, ⟨hz₂φ, hz₂ψ⟩⟩ := h₃;

  obtain ⟨u, Ryu, ⟨Ruz₁, Ruz₂, h⟩⟩ := M.kreisel_putnam y z₁ z₂ ⟨
    Ryz₁, Ryz₂,
    by
      rcases forces_or.mp $ h₁ _ Ryz₁ hz₁φ with (h | h);
      . exfalso; exact hz₁ψ h;
      . by_contra hC; exact hz₂ψ $ M.formula_persistency h hC;
    ,
    by
      rcases forces_or.mp $ h₁ _ Ryz₂ hz₂φ with (h | h);
      . by_contra hC; exact hz₁ψ $ M.formula_persistency h hC;
      . exfalso; exact hz₂ψ h;
  ⟩;
  have : ¬u ⊩ (∼φ) := by
    by_contra hC;
    rcases forces_or.mp $ h₁ _ Ryu hC with (h | h);
    . apply hz₁ψ $ M.formula_persistency h Ruz₁;
    . apply hz₂ψ $ M.formula_persistency h Ruz₂;
  replace this := forces_neg.not.mp this;
  push_neg at this;
  obtain ⟨v, Ruv, hv⟩ := this;

  rcases h v Ruv with ⟨w, Rvw, (Rz₁w | Rz₂w)⟩
  . apply (forces_neg.mp $ M.formula_persistency hz₁φ Rz₁w) w $ Std.Refl.refl w;
    exact M.formula_persistency hv Rvw;
  . apply (forces_neg.mp $ M.formula_persistency hz₂φ Rz₂w) w $ Std.Refl.refl w;
    exact M.formula_persistency hv Rvw;

end KripkeModel

section

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
open canonicalKripkeModel
open SaturatedConsistentTableau
open Classical

instance [Entailment.HasAxiomKreiselPutnam 𝓢] : (canonicalKripkeModel 𝓢).KreiselPutnam := by
  constructor;
  rintro x y z ⟨Rxy, Rxz, nRyz, nRzy⟩;
  let ΓNyz := { φ | ∼φ ∈ (y.1.1 ∩ z.1.1)}.image (∼·);
  obtain ⟨u, hu₁, hu₂⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨x.1.1 ∪ ΓNyz, y.1.2 ∪ z.1.2⟩) $ by
    show Tableau.Consistent 𝓢 (x.1.1 ∪ ΓNyz, y.1.2 ∪ z.1.2);
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    let Γx := { φ ∈ Γ | φ ∈ x.1.1};
    let Γ₁ := { φ ∈ Γ | φ ∈ ΓNyz };
    let Γ₂ := Γ₁.preimage (∼·) $ by simp [Set.InjOn];
    let Δy := { φ ∈ Δ | φ ∈ y.1.2};
    let Δz := { φ ∈ Δ | φ ∈ z.1.2};
    replace hC : 𝓢 ⊢ (Γx ∪ Γ₁).conj 🡒 (Δy ∪ Δz).disj := C!_replace ?_ ?_ hC;
    . replace hC : 𝓢 ⊢ Γx.conj ⋏ Γ₁.conj 🡒 Δy.disj ⋎ Δz.disj := C!_replace CKFconjFconjUnion! CFdisjUnionAFdisj hC;
      generalize eδy : Δy.disj = δy at hC;
      generalize eδz : Δz.disj = δz at hC;
      replace hC : ↑Γx *⊢[𝓢] ∼(Γ₂.disj) 🡒 δy ⋎ δz := C!_trans ?_ $ FConj_DT.mp $ CK!_iff_CC!.mp hC;
      . generalize eγ : Γ₂.disj = γ at hC;
        replace hC : ↑Γx *⊢[𝓢] (∼γ 🡒 δy) ⋎ (∼γ 🡒 δz) := kreiselputnam'! hC;
        replace hC : ∼γ 🡒 δy ∈ x.1.1 ∨ ∼γ 🡒 δz ∈ x.1.1 := iff_mem₁_or.mp $ iff_provable_include₁.mp hC x ?_;
        . rcases hC with h | h;
          . apply iff_not_mem₂_mem₁.mpr $ of_mem₁_imp' (Rxy h) ?_
            . subst eδy;
              apply iff_mem₂_fdisj.mpr;
              intro φ hφ;
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Δy] at hφ;
              exact hφ.2;
            . subst eγ;
              apply mdp_mem₁_provable (φ := Γ₁.conj) ?_ ?_;
              . apply C!_trans ?_ CFconjNNFconj!;
                apply CFConj_FConj!_of_subset;
                intro φ;
                simp only [Finset.mem_image, Finset.mem_preimage, Finset.mem_filter, forall_exists_index, and_imp, Γ₁, Γ₂];
                rintro _ _ _ rfl;
                tauto;
              . apply iff_mem₁_fconj.mpr;
                intro φ;
                simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Finset.coe_filter, and_imp, forall_exists_index, Γ₁, ΓNyz];
                rintro _ _ _ _ rfl;
                assumption;
          . apply iff_not_mem₂_mem₁.mpr $ of_mem₁_imp' (Rxz h) ?_
            . subst eδz;
              apply iff_mem₂_fdisj.mpr;
              intro φ hφ;
              simp only [Finset.coe_filter, Set.mem_setOf_eq, Δz] at hφ;
              exact hφ.2;
            . subst eγ;
              apply mdp_mem₁_provable (φ := Γ₁.conj) ?_ ?_;
              . apply C!_trans ?_ CFconjNNFconj!;
                apply CFConj_FConj!_of_subset;
                intro φ;
                simp only [Finset.mem_image, Finset.mem_preimage, Finset.mem_filter, forall_exists_index, and_imp, Γ₁, Γ₂];
                rintro _ _ _ rfl;
                tauto;
              . apply iff_mem₁_fconj.mpr;
                intro φ;
                simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Finset.coe_filter, and_imp, forall_exists_index, Γ₁, ΓNyz];
                rintro _ _ _ _ rfl;
                assumption;
        . intro φ hφ;
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Γx] at hφ;
          exact hφ.2;
      . apply Context.of!;
        apply right_Fconj!_intro;
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Finset.mem_filter, and_imp, forall_exists_index, Γ₁, Γ₂, ΓNyz];
        rintro _ hψ ψ hψ₁ hψ₂ rfl;
        apply C!_trans CNFdisjFconj!;
        apply left_Fconj!_intro;
        suffices ∼ψ ∈ Γ ∧ ∼ψ ∈ y.1.1 ∧ ∼ψ ∈ z.1.1 by simpa [Γ₁, Γ₂] using this;
        tauto;
    . apply CFConj_FConj!_of_subset;
      intro φ hφ;
      simp only [Finset.mem_union, Finset.mem_filter, Γx, Γ₁];
      rcases hΓ hφ with h | h <;> tauto;
    . apply CFDisjFDisj_of_subset;
      intro φ hφ;
      simp only [Finset.mem_union, Finset.mem_filter, Δy, Δz];
      rcases hΔ hφ with h | h <;> tauto;
  replace hu₁ := Set.union_subset_iff.mp hu₁;
  replace hu₂ := Set.union_subset_iff.mp hu₂;
  use u;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . exact hu₁.1;
  . apply canonicalKripkeModel.def_rel₂.mpr; exact hu₂ |>.1;
  . apply canonicalKripkeModel.def_rel₂.mpr; exact hu₂ |>.2;
  . intro v Ruv;
    by_contra! hC;
    obtain ⟨γ₁, hγ₁₁, hγ₁₂⟩ : ∃ γ₁ ∈ v.1.1, ∼γ₁ ∈ y.1.1 := by
      have : Tableau.Inconsistent 𝓢 ⟨y.1.1 ∪ v.1.1, ∅⟩ := by
        by_contra hconsis;
        obtain ⟨t, ht⟩ := lindenbaum hconsis;
        apply hC t ?_ |>.1;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.1;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.2;
      dsimp [Tableau.Inconsistent, Tableau.Consistent] at this;
      push_neg at this;
      obtain ⟨Γ, Δ, hΓ, hΔ, hΓΔ⟩ := this;
      simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΔ;
      subst hΔ;
      simp only [Finset.disj_empty] at hΓΔ;
      use ({ φ ∈ Γ | φ ∈ v.1.1}).conj;
      constructor;
      . apply iff_mem₁_fconj.mpr;
        intro;
        simp;
      . apply iff_provable_include₁_finset (Γ := {x ∈ Γ | x ∈ y.1.1}) |>.mp ?_ y ?_;
        . apply N!_iff_CO!.mpr;
          apply FConj_DT'.mpr;
          apply Context.weakening! ?_ (FConj_DT.mp hΓΔ);
          intro φ hφ;
          simp only [Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq];
          rcases hΓ hφ with _ | _ <;> tauto;
        . intro;
          simp;
    obtain ⟨γ₂, hγ₂₁, hγ₂₂⟩ : ∃ γ₂ ∈ v.1.1, ∼γ₂ ∈ z.1.1 := by
      have : Tableau.Inconsistent 𝓢 ⟨z.1.1 ∪ v.1.1, ∅⟩ := by
        by_contra hconsis;
        obtain ⟨t, ht⟩ := lindenbaum hconsis;
        apply hC t ?_ |>.2;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.1;
        . exact Set.union_subset_iff.mp (Tableau.subset_def.mp ht |>.1) |>.2;
      dsimp [Tableau.Inconsistent, Tableau.Consistent] at this;
      push_neg at this;
      obtain ⟨Γ, Δ, hΓ, hΔ, hΓΔ⟩ := this;
      simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΔ;
      subst hΔ;
      simp only [Finset.disj_empty] at hΓΔ;
      use ({ φ ∈ Γ | φ ∈ v.1.1}).conj;
      constructor;
      . apply iff_mem₁_fconj.mpr;
        intro;
        simp;
      . apply iff_provable_include₁_finset (Γ := {x ∈ Γ | x ∈ z.1.1}) |>.mp ?_ z ?_;
        . apply N!_iff_CO!.mpr;
          apply FConj_DT'.mpr;
          apply Context.weakening! ?_ (FConj_DT.mp hΓΔ);
          intro φ hφ;
          simp only [Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq];
          rcases hΓ hφ with _ | _ <;> tauto;
        . intro;
          simp;
    have : ∼(γ₁ ⋏ γ₂) ∈ v.1.1 := Ruv $ hu₁.2 $ by
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Formula.neg_inj, exists_eq_right, ΓNyz];
      constructor <;>
      . apply mdp_mem₁_provable CANNNK!;
        apply iff_mem₁_or.mpr;
        tauto;
    apply of_mem₁_neg' this;
    apply iff_mem₁_and.mpr;
    tauto;

end

end LO.Propositional
end
