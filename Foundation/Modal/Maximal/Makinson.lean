import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Hilbert.Maximal.Basic
import Foundation.Modal.Hilbert.NNFormula
import Foundation.Modal.Hilbert.KP
import Foundation.Propositional.Classical.Hilbert
import Foundation.Propositional.Classical.ZeroSubst


namespace LO.Modal

namespace Logic

variable {L : Logic} [L.Normal] [L.Consistent] {φ ψ : Formula ℕ}

class VerFamily (L : Logic) : Prop where
  subset_Ver : L ⊆ Logic.Ver

class TrivFamily (L : Logic) : Prop where
  KD_subset : Logic.KD ⊆ L
  subset_Triv : L ⊆ Logic.Triv

section

open Entailment

lemma KD_subset_of_not_subset_Ver.lemma₁ (hL : φ ∈ L) (hV : φ ∉ Logic.Ver) : ∃ ψ, ◇ψ ∈ L := by
  obtain ⟨ψ, ⟨Γ, rfl⟩, h⟩ := Hilbert.NNFormula.exists_CNF φ;
  generalize eγ : (⋀Γ.unattach).toFormula = γ at h;
  have : φ.toNNFormula.toFormula ⭤ γ ∈ L := Logic.of_mem_K h;

  have hγL : γ ∈ L := by sorry;
  have hγV : γ ∉ Logic.Ver := by sorry;

  obtain ⟨⟨_, ⟨Δ, rfl⟩⟩, hδΓ, hδL, hδV⟩ : ∃ δ, δ ∈ Γ ∧ δ.1.toFormula ∈ L ∧ δ.1.toFormula ∉ Logic.Ver := by
    sorry;
  have hΔ₁ : ∀ ψ ∈ Δ, ¬ψ.1.isPrebox := by
    rintro ⟨ψ, _⟩ hψ₁ hψ₂;
    obtain ⟨ξ, rfl⟩ := NNFormula.exists_isPrebox hψ₂;
    have : □ξ.toFormula ∈ Logic.Ver := by simp;
    sorry;

  have : ∃ Γ: List (Formula ℕ), φ ⭤ ⋀Γ ∈ L := by sorry;
  simp at hV;
  sorry;

lemma KD_subset_of_not_subset_Ver (hV : ¬L ⊆ Logic.Ver) : Logic.KD ⊆ L := by
  intro φ hφ;
  replace hφ := Hilbert.iff_provable_KP_provable_KD.mpr hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩);
    . apply Logic.subset_K; simp;
    . obtain ⟨ψ, hψ₁, hψ₂⟩ := Set.not_subset_iff_exists_mem_not_mem.mp hV;
      obtain ⟨ξ, hξ⟩ := KD_subset_of_not_subset_Ver.lemma₁ hψ₁ hψ₂;
      apply Logic.mdp (φ := ◇ξ);
      . exact Logic.subset_K $ contra₀'! $ axiomK'! $ nec! $ efq!;
      . exact hξ;
  | mdp hφψ hφ => exact Logic.mdp hφψ hφ;
  | nec hφ => exact Logic.nec hφ;
  | _ => apply Logic.subset_K; simp;

lemma KD_subset_of_not_VerFamily (h : ¬L.VerFamily) : Logic.KD ⊆ L := by
  apply KD_subset_of_not_subset_Ver;
  tauto;

end


section

open Entailment
open Formula

variable {v : Propositional.Classical.Valuation ℕ}

lemma KD_provability_of_classical_satisfiability (hl : φ.letterless) :
  (v ⊧ (φᵀ.toPropFormula) → Hilbert.KD ⊢! φ) ∧
  (¬(v ⊧ (φᵀ.toPropFormula)) → Hilbert.KD ⊢! ∼φ)
  := by
  induction φ using Formula.rec' with
  | hatom => simp at hl;
  | hfalsum => simp [trivTranslate, toPropFormula];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      simp only [trivTranslate, toPropFormula] at h;
      rcases imp_iff_not_or.mp h with (hφ | hψ);
      . exact efq_of_neg! $ ihφ (letterless.def_imp₁ hl) |>.2 hφ;
      . exact imply₁'! $ ihψ (letterless.def_imp₂ hl) |>.1 hψ;
    . intro h;
      simp only [trivTranslate, toPropFormula, Semantics.Realize, Propositional.Formula.Classical.val] at h;
      push_neg at h;
      rcases h with ⟨hφ, hψ⟩;
      replace hφ := ihφ (letterless.def_imp₁ hl) |>.1 hφ;
      replace hψ := ihψ (letterless.def_imp₂ hl) |>.2 hψ;
      -- TODO: need golf
      apply FiniteContext.deduct'!;
      replace hφ : [φ ➝ ψ] ⊢[Hilbert.KD]! φ := FiniteContext.of'! hφ;
      replace hψ : [φ ➝ ψ] ⊢[Hilbert.KD]! ∼ψ := FiniteContext.of'! hψ;
      exact hψ ⨀ (FiniteContext.by_axm! ⨀ hφ);
  | hbox φ ihφ =>
    constructor;
    . intro h;
      apply nec!;
      apply ihφ (letterless.def_box hl) |>.1;
      tauto;
    . intro h;
      have : Hilbert.KD ⊢! □(∼φ) := nec! $ ihφ (letterless.def_box hl) |>.2 $ by tauto;
      exact negbox_dne'! $ dia_duality'!.mp $ axiomD'! this;

lemma provable_KD_of_classical_satisfiability (hl : φ.letterless) : (v ⊧ φᵀ.toPropFormula) → Hilbert.KD ⊢! φ :=
  KD_provability_of_classical_satisfiability hl |>.1

lemma provable_not_KD_of_classical_unsatisfiable (hl : φ.letterless) : (¬(v ⊧ φᵀ.toPropFormula)) → Hilbert.KD ⊢! ∼φ :=
  KD_provability_of_classical_satisfiability hl |>.2

private lemma subset_Triv_of_KD_subset.lemma₁
  {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _} {v : Propositional.Classical.Valuation α} :
  v ⊧ (((φᵀ.toPropFormula)⟦s.1⟧)) ↔
  v ⊧ ((φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula)
  := by
  induction φ using Formula.rec' with
  | hatom a =>
    suffices v ⊧ (s.1 a) ↔ v ⊧ (s.1 a).toModalFormulaᵀ.toPropFormula by
      simpa [trivTranslate, toPropFormula];
    generalize eψ : s.1 a = ψ;
    have hψ : ψ.letterless := by
      rw [←eψ];
      exact s.2;
    clear eψ;
    induction ψ using Propositional.Formula.rec' with
    | hatom => simp at hψ;
    | hfalsum => tauto;
    | hand => unfold Propositional.Formula.letterless at hψ; simp_all [trivTranslate, toPropFormula];
    | himp => unfold Propositional.Formula.letterless at hψ; simp_all [trivTranslate, toPropFormula];
    | hor => unfold Propositional.Formula.letterless at hψ; simp_all [trivTranslate, toPropFormula]; tauto;
  | _ => simp_all [trivTranslate, toPropFormula];

lemma subset_Triv_of_KD_subset.lemma₂ {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _}
  :
  Semantics.Valid (Propositional.Classical.Valuation α) (∼((φᵀ.toPropFormula)⟦s.1⟧)) ↔
  Semantics.Valid (Propositional.Classical.Valuation α) ((∼φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula)
  := by
  constructor;
  . intro h v hφ;
    apply h v ?_;
    exact lemma₁.mpr hφ;
  . intro h v; exact lemma₁ (φ := ∼φ).mpr $ h v;

theorem subset_Triv_of_KD_subset (hS : Logic.KD ⊆ L) : L ⊆ Logic.Triv := by
  by_contra hC;
  obtain ⟨φ, hφ₁, hφ₂⟩ := Set.not_subset.mp hC;
  have := Hilbert.Triv.iff_provable_Cl.not.mp hφ₂;
  have := (not_imp_not.mpr Propositional.Hilbert.Cl.Classical.completeness) this;
  obtain ⟨s, h⟩ := Propositional.Classical.tautology_neg_zero_subst_instance_of_not_tautology this;
  let ψ := φ⟦(s : Modal.ZeroSubstitution _).1⟧;
  have : Semantics.Valid (Propositional.Classical.Valuation ℕ) (∼(ψᵀ.toPropFormula)) := subset_Triv_of_KD_subset.lemma₂.mp h;
  have : Hilbert.KD ⊢! ∼ψ := provable_not_KD_of_classical_unsatisfiable Formula.letterless_zeroSubst
    $ Semantics.Not.realize_not.mp
    $ this ⟨(λ _ => True)⟩;
  have : ∼ψ ∈ L := hS this;
  have : ∼ψ ∉ L := Modal.Logic.not_neg_mem_of_mem $ Modal.Logic.subst hφ₁;
  contradiction

end


theorem makinson : (L.VerFamily ∨ L.TrivFamily) ∧ ¬(L.VerFamily ∧ L.TrivFamily) := by
  constructor;
  . apply or_iff_not_imp_left.mpr;
    rintro h;
    constructor;
    . exact KD_subset_of_not_VerFamily h;
    . exact subset_Triv_of_KD_subset $ KD_subset_of_not_VerFamily h;
  . by_contra hC;
    have ⟨⟨hVer⟩, ⟨hKD, hTriv⟩⟩ := hC;
    have h₁ : ∼□⊥ ∈ Logic.Ver := by apply hVer; apply hKD; simp;
    have h₂ : □⊥ ∈ Logic.Ver := by simp;
    have : Hilbert.Ver ⊢! ⊥ := h₁ ⨀ h₂;
    have : Hilbert.Ver ⊬ ⊥ := Entailment.Consistent.not_bot inferInstance;
    contradiction;

lemma VerFamily.notTrivFamily [L.VerFamily] : ¬L.TrivFamily := by
  apply not_and.mp $ makinson (L := L) |>.2;
  assumption;

lemma TrivFamily.notVerFamily [L.TrivFamily] : ¬L.VerFamily := by
  apply not_and'.mp $ makinson (L := L) |>.2;
  assumption;


end Logic




end LO.Modal
