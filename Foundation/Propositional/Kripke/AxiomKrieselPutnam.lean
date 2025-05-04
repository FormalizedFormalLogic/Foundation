import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Entailment.Cl

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

@[simp]
lemma CFdisjUnionAFdisj [DecidableEq F] [HasAxiomEFQ 𝓢] {Γ Δ : Finset F} : 𝓢 ⊢! (Γ ∪ Δ).disj ➝ Γ.disj ⋎ Δ.disj := by
  apply left_Fdisj!_intro;
  simp only [Finset.mem_union];
  rintro ψ (hψ | hψ);
  . apply C!_trans (ψ := Γ.disj) ?_ or₁!;
    apply right_Fdisj!_intro;
    assumption;
  . apply C!_trans (ψ := Δ.disj) ?_ or₂!;
    apply right_Fdisj!_intro;
    assumption;

lemma C!_replace (h₁ : 𝓢 ⊢! ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! φ₁ ➝ φ₂ → 𝓢 ⊢! ψ₁ ➝ ψ₂ := λ h => C!_trans h₁ $ C!_trans h h₂

/-- List version of `CNAKNN!` -/
@[simp]
lemma CNDisj₁Conj₂! [DecidableEq F] : 𝓢 ⊢! ∼⋁Γ ➝ ⋀(Γ.map (∼·)) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    refine C!_trans CNAKNN! ?_;
    apply CKK!_of_C!' ih;

/--- Finset version of `CNAKNN!` -/
@[simp]
lemma CNFdisjFconj! [DecidableEq F] [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! ∼Γ.disj ➝ (Γ.image (∼·)).conj := by
  apply C!_replace ?_ ?_ $ CNDisj₁Conj₂! (Γ := Γ.toList);
  . apply contra!;
    exact CFDisjDisj₂;
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;

@[simp] lemma CONV! : 𝓢 ⊢! ⊤ ➝ ∼⊥ := by
  apply FiniteContext.deduct'!;
  exact NO!;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CConj₂NNDisj₂! [DecidableEq F] : 𝓢 ⊢! ⋀Γ.map (∼·) ➝ ∼⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    apply C!_trans ?_ CKNNNA!;
    apply CKK!_of_C!' ih;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CFconjNNFconj! [DecidableEq F] [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! (Γ.image (∼·)).conj ➝ ∼Γ.disj := by
  apply C!_replace ?_ ?_ $ CConj₂NNDisj₂! (Γ := Γ.toList);
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;
  . apply contra!;
    simp;

@[simp]
lemma CNDisj₂NConj₂! [DecidableEq F] [HasAxiomDNE 𝓢] {Γ : List F} : 𝓢 ⊢! ∼⋁(Γ.map (∼·)) ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢! ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) ➝ φ ⋏ ⋀Γ by
      apply C!_trans ?_ this;
      apply contra!;
      apply CAA!_of_C!_right;
      exact dne!;
    apply C!_trans CNAKNN! ?_;
    apply CKK!_of_C!_of_C!;
    . exact dne!;
    . exact C!_trans dne! ih;

lemma CNFdisj₂NFconj₂! [DecidableEq F] [HasAxiomDNE 𝓢] {Γ : Finset F} : 𝓢 ⊢! ∼(Γ.image (∼·)).disj ➝ Γ.conj := by
  apply C!_replace ?_ ?_ $ CNDisj₂NConj₂! (Γ := Γ.toList);
  . apply contra!;
    apply left_Disj₂!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    simpa using hψ;
  . simp;

end LO.Entailment


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
  let ΓNyz := { φ | ∼φ ∈ (y.1.1 ∩ z.1.1)}.image (∼·);
  obtain ⟨u, hu₁, hu₂⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨x.1.1 ∪ ΓNyz, y.1.2 ∪ z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    let Γx := { φ ∈ Γ | φ ∈ x.1.1};
    let Γ₁ := { φ ∈ Γ | φ ∈ ΓNyz };
    let Γ₂ := Γ₁.preimage (∼·) $ by simp [Set.InjOn];
    let Δy := { φ ∈ Δ | φ ∈ y.1.2};
    let Δz := { φ ∈ Δ | φ ∈ z.1.2};
    replace hC : 𝓢 ⊢! (Γx ∪ Γ₁).conj ➝ (Δy ∪ Δz).disj := C!_replace ?_ ?_ hC;
    . replace hC : 𝓢 ⊢! Γx.conj ⋏ Γ₁.conj ➝ Δy.disj ⋎ Δz.disj := C!_replace CKFconjFconjUnion! CFdisjUnionAFdisj hC;
      generalize eδy : Δy.disj = δy at hC;
      generalize eδz : Δz.disj = δz at hC;
      replace hC : ↑Γx *⊢[𝓢]! ∼(Γ₂.disj) ➝ δy ⋎ δz := C!_trans ?_ $ FConj_DT.mp $ CK!_iff_CC!.mp hC;
      . generalize eγ : Γ₂.disj = γ at hC;
        replace hC : ↑Γx *⊢[𝓢]! (∼γ ➝ δy) ⋎ (∼γ ➝ δz) := krieselputnam'! hC;
        replace hC : ∼γ ➝ δy ∈ x.1.1 ∨ ∼γ ➝ δz ∈ x.1.1 := iff_mem₁_or.mp $ iff_provable_include₁.mp hC x ?_;
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
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Γx, Δy, Δz] at hφ;
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
  . apply Kripke.canonicalFrame.rel₂.mpr; exact hu₂ |>.1;
  . apply Kripke.canonicalFrame.rel₂.mpr; exact hu₂ |>.2;
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
      simp only [Finset.disj_empty, Decidable.not_not] at hΓΔ;
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
      simp only [Finset.disj_empty, Decidable.not_not] at hΓΔ;
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
⟩

end Canonical

end canonicality

end Kripke

end LO.Propositional
