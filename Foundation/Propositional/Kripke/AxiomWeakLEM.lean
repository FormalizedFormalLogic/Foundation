import Foundation.Propositional.Entailment.KC
import Foundation.Propositional.Kripke.Completeness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_WeakLEM_of_confluent' : Confluent F → F ⊧ (Axioms.WeakLEM (.atom 0)) := by
  unfold Confluent Axioms.WeakLEM;
  contrapose;
  push_neg;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  unfold Satisfies at h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := Satisfies.neg_def.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, hy⟩ := h₁;

  replace h₂ := Satisfies.neg_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, hz⟩ := h₂;

  use x, y, z;
  constructor;
  . constructor <;> assumption;
  . intro u Ryu;
    by_contra Rzu;
    exact (Satisfies.neg_def.mp hz) Rzu $ Satisfies.formula_hereditary Ryu hy;


lemma validate_WeakLEM_of_confluent [IsConfluent _ F] : F ⊧ (Axioms.WeakLEM (.atom 0)) := by
  apply validate_WeakLEM_of_confluent';
  exact IsConfluent.confluent;


lemma confluent_of_validate_WeakLEM : F ⊧ (Axioms.WeakLEM (.atom 0)) → Confluent F := by
  rintro h x y z ⟨Rxy, Ryz⟩;
  let V : Kripke.Valuation F := ⟨λ {v a} => y ≺ v, by
    intro w v Rwv a Ryw;
    apply F.trans Ryw Rwv;
  ⟩;
  replace h : F ⊧ (Axioms.WeakLEM (.atom 0)) := by simpa using h;
  have : ¬Satisfies ⟨F, V⟩ x (∼(.atom 0)) := by
    suffices ∃ y, x ≺ y ∧ V y 0 by simpa [Satisfies];
    use y;
    constructor;
    . exact Rxy;
    . simp [V];
  have : Satisfies ⟨F, V⟩ x (∼∼(.atom 0)) := by
    apply or_iff_not_imp_left.mp $ Satisfies.or_def.mp $ @h V x;
    assumption;
  obtain ⟨w, Rzw, hw⟩ := by simpa [Satisfies] using @this z Ryz;
  use w;

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

instance [Entailment.HasAxiomWeakLEM 𝓢] : IsConfluent _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  suffices Tableau.Consistent 𝓢 (y.1.1 ∪ z.1.1, ∅) by
    obtain ⟨w, hw⟩ := lindenbaum (𝓢 := 𝓢) this;
    use w;
    simpa using hw;

  intro Γ Δ;
  intro hΓ hΔ h;
  simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ;
  subst hΔ;
  simp only [Finset.disj_empty] at h;

  let Θx := { φ ∈ Γ | (φ ∈ y.1.1 ∧ φ ∈ x.1.1) ∨ (φ ∈ z.1.1 ∧ φ ∈ x.1.1) }
  let Θy := { φ ∈ Γ | φ ∈ y.1.1 ∧ φ ∉ x.1.1 }
  let Θz := { φ ∈ Γ | φ ∈ z.1.1 ∧ φ ∉ x.1.1 }

  suffices ∼Θy.conj ∈ x.1.1 by
    apply not_mem₁_neg_of_mem₁ (φ := Θy.conj) (t := y) $ iff_mem₁_fconj.mpr $ by
      intro φ;
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Θy];
      tauto;
    exact Rxy this;

  have : 𝓢 ⊢! (Θx.conj ⋏ Θy.conj ⋏ Θz.conj) ➝ ⊥ := by
    apply C!_trans ?_ h;
    apply CK!_iff_CC!.mpr;
    apply FConj_DT.mpr;
    apply CK!_iff_CC!.mpr;
    apply FConj_DT'.mpr;
    apply FConj_DT'.mpr;
    apply FConj_DT.mp;
    apply CFConj_FConj!_of_subset;
    intro φ hφ;
    rcases hΓ hφ with h | h;
    . suffices φ ∈ Θx ∪ Θy by
        apply Finset.mem_union.mpr;
        tauto;
      simp [Θx, Θy, Θz];
      tauto;
    . suffices φ ∈ Θx ∪ Θz by
        rw [(show Θx ∪ Θy ∪ Θz = Θx ∪ Θz ∪ Θy by rw [Finset.union_assoc, Finset.union_comm Θy, ←Finset.union_assoc])]
        apply Finset.mem_union.mpr;
        tauto;
      simp [Θx, Θy, Θz];
      tauto;
  have : 𝓢 ⊢! Θx.conj ➝ Θy.conj ➝ ∼Θz.conj := CK!_iff_CC!.mp $
    (C!_trans (CK!_iff_CC!.mp $ C!_trans (K!_left K!_assoc) this) (K!_right $ neg_equiv!));
  replace : [Θx.conj] ⊢[𝓢]! Θy.conj ➝ ∼Θz.conj := FiniteContext.deductInv'! this;
  replace : [Θx.conj] ⊢[𝓢]! ∼∼Θz.conj ➝ ∼Θy.conj := contra! this;

  have mem_Θx_x : Θx.conj ∈ x.1.1 := iff_mem₁_fconj.mpr $ by
    intro φ;
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Θx, Θy, Θz];
    tauto;
  have mem_Θz_z : Θz.conj ∈ z.1.1 := iff_mem₁_fconj.mpr $ by
    intro φ;
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Θz, Θy, Θx];
    tauto;

  have nmem_nΘz_z : ∼Θz.conj ∉ z.1.1 := not_mem₁_neg_of_mem₁ mem_Θz_z;
  have nmem_nΘz_x : ∼Θz.conj ∉ x.1.1 := Set.not_mem_subset Rxz nmem_nΘz_z;
  have mem_nnΘz_x : ∼∼Θz.conj ∈ x.1.1 := or_iff_not_imp_left.mp (iff_mem₁_or.mp $ mem₁_of_provable $ wlem!) nmem_nΘz_x;

  exact mdp₁_mem mem_nnΘz_x $ mdp_mem₁_provable this mem_Θx_x;
⟩

end Canonical

end canonicality

end Kripke

end LO.Propositional
