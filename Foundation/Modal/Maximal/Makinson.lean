module

public import Foundation.Modal.Hilbert.NNFormula
public import Foundation.Modal.Maximal.Basic
public import Foundation.Modal.Logic.SumNormal
public import Foundation.Modal.Kripke.Logic.Ver
public import Foundation.Propositional.Boolean.ZeroSubst

@[expose] public section

namespace LO.Modal

namespace Logic

variable {L : Logic ℕ} [L.IsNormal] [Entailment.Consistent L] {φ ψ : Formula ℕ}

class VerFamily (L : Logic ℕ) : Prop where
  subset_Ver : L ⪯ Modal.Ver

class TrivFamily (L : Logic ℕ) : Prop where
  KD_subset   : Modal.KD ⪯ L
  subset_Triv : L ⪯ Modal.Triv

section

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

lemma KD_subset_of_not_subset_Ver.lemma₁ (hL : L ⊢ φ) (hV : Modal.Ver ⊬ φ) : ∃ ψ, L ⊢ ◇ψ := by
  obtain ⟨ψ, ⟨Γ, rfl⟩, h⟩ := Hilbert.NNFormula.exists_CNF φ;
  generalize eγ : (⋀Γ.unattach).toFormula = γ at h;

  have : L ⊢ φ.toNNFormula.toFormula 🡘 γ := WeakerThan.pbl h;

  have hγL : γ ∈ L := by sorry;
  have hγV : γ ∉ Modal.Ver := by sorry;

  obtain ⟨⟨_, ⟨Δ, rfl⟩⟩, hδΓ, hδL, hδV⟩ : ∃ δ, δ ∈ Γ ∧ δ.1.toFormula ∈ L ∧ δ.1.toFormula ∉ Modal.Ver := by
    sorry;
  have hΔ₁ : ∀ ψ ∈ Δ, ¬ψ.1.isPrebox := by
    rintro ⟨ψ, _⟩ hψ₁ hψ₂;
    obtain ⟨ξ, rfl⟩ := NNFormula.exists_isPrebox hψ₂;
    have : Modal.Ver ⊢ □ξ.toFormula := by simp;
    sorry;

  have : ∃ Γ: List (Formula ℕ), L ⊢ φ 🡘 ⋀Γ := by sorry;
  sorry;

lemma KD_subset_of_not_subset_Ver (hV : ¬L ⪯ Modal.Ver) : Modal.KD ⪯ L := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  replace hφ : Modal.KP ⊢ φ := Entailment.Equiv.iff.mp inferInstance _ |>.mpr hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm _ h =>
    rcases h with (rfl | rfl);
    . simp;
    . obtain ⟨ψ, hψ₁, hψ₂⟩ := not_weakerThan_iff.mp hV;
      obtain ⟨ξ, hξ⟩ := KD_subset_of_not_subset_Ver.lemma₁ hψ₁ hψ₂;
      apply Entailment.mdp! (φ := ◇ξ);
      . exact contra! $ axiomK'! $ nec! $ efq!;
      . exact hξ;
  | mdp hφψ hφ => exact hφψ ⨀ hφ;
  | nec hφ => exact Entailment.nec! hφ;
  | _ => simp;

lemma KD_subset_of_not_VerFamily (h : ¬L.VerFamily) : Modal.KD ⪯ L := by
  apply KD_subset_of_not_subset_Ver;
  tauto;

end


section

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula
open Propositional

variable {v : Boolean.Valuation ℕ}

lemma KD_provability_of_classical_satisfiability (hl : φ.Letterless) :
  (v ⊧ (φᵀ.toPropFormula) → Modal.KD ⊢ φ) ∧
  (¬(v ⊧ (φᵀ.toPropFormula)) → Modal.KD ⊢ ∼φ)
  := by
  induction φ with
  | hatom => grind;
  | hfalsum => simp [trivTranslate, toPropFormula];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      simp only [trivTranslate, toPropFormula] at h;
      rcases imp_iff_not_or.mp h with (hφ | hψ);
      . exact C_of_N $ ihφ (by grind) |>.2 hφ;
      . exact C!_of_conseq! $ ihψ (by grind) |>.1 hψ;
    . intro h;
      simp only [trivTranslate, toPropFormula, Semantics.Models, Formula.Boolean.val] at h;
      push Not at h;
      rcases h with ⟨hφ, hψ⟩;
      replace hφ := ihφ (by grind) |>.1 hφ;
      replace hψ := ihψ (by grind) |>.2 hψ;
      -- TODO: need golf
      apply FiniteContext.deduct'!;
      replace hφ : [φ 🡒 ψ] ⊢[Modal.KD] φ := FiniteContext.of'! hφ;
      replace hψ : [φ 🡒 ψ] ⊢[Modal.KD] ∼ψ := FiniteContext.of'! hψ;
      exact hψ ⨀ (FiniteContext.by_axm! ⨀ hφ);
  | hbox φ ihφ =>
    constructor;
    . intro h;
      apply nec!;
      apply ihφ (by grind) |>.1;
      tauto;
    . intro h;
      have : Modal.KD ⊢ □(∼φ) := nec! $ ihφ (by grind) |>.2 $ by tauto;
      exact negbox_dne'! $ dia_duality'!.mp $ axiomD'! this;

lemma provable_KD_of_classical_satisfiability (hl : φ.Letterless) : (v ⊧ φᵀ.toPropFormula) → Modal.KD ⊢ φ :=
  KD_provability_of_classical_satisfiability hl |>.1

lemma provable_KD_of_classical_tautology (hl : φ.Letterless) (h : (Semantics.Valid (Boolean.Valuation ℕ) (φᵀ.toPropFormula)))
  : Modal.KD ⊢ φ := provable_KD_of_classical_satisfiability hl (h (λ _ => True))

lemma provable_not_KD_of_classical_unsatisfiable (hl : φ.Letterless) : (¬(v ⊧ φᵀ.toPropFormula)) → Modal.KD ⊢ ∼φ :=
  KD_provability_of_classical_satisfiability hl |>.2

private lemma subset_Triv_of_KD_subset.lemma₁
  {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _} {v : Boolean.Valuation α} :
  v ⊧ (((φᵀ.toPropFormula)⟦s.1⟧)) ↔
  v ⊧ ((φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula)
  := by
  induction φ with
  | hatom a =>
    let ψ : Propositional.Formula α := s.1 a;
    suffices v ⊧ ψ ↔ v ⊧ ψ.toModalFormulaᵀ.toPropFormula (by simp) by simpa [trivTranslate, toPropFormula];
    induction ψ with
    | hor => simp [trivTranslate, toPropFormula]; tauto;
    | _ => simp_all [trivTranslate, toPropFormula];
  | _ => simp_all [trivTranslate, toPropFormula];

lemma subset_Triv_of_KD_subset.lemma₂ {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _} :
  (∼((φᵀ.toPropFormula)⟦s.1⟧)).IsTautology ↔
  ((∼φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula).IsTautology
  := by
  constructor;
  . intro h v hφ;
    apply h v ?_;
    exact lemma₁.mpr hφ;
  . intro h v; exact lemma₁ (φ := ∼φ).mpr $ h v;

@[instance]
theorem subset_Triv_of_KD_subset [Modal.KD ⪯ L] : L ⪯ Modal.Triv := by
  by_contra! hC;
  obtain ⟨φ, hφ₁, hφ₂⟩ := not_weakerThan_iff.mp hC;
  replace hφ₂ := (not_imp_not.mpr Hilbert.Cl.completeness) $ Modal.Triv.iff_provable_Cl.not.mp $ hφ₂;
  obtain ⟨s, h⟩ := Boolean.exists_neg_zeroSubst_of_not_tautology hφ₂;
  let ψ := φ⟦(s : Modal.ZeroSubstitution _).1⟧;
  have : Semantics.Valid (Boolean.Valuation ℕ) (∼(ψᵀ.toPropFormula)) := subset_Triv_of_KD_subset.lemma₂.mp h;
  have : Modal.KD ⊢ ∼ψ := provable_not_KD_of_classical_unsatisfiable Formula.letterless_zeroSubst
    $ Semantics.Not.models_not.mp
    $ this (λ _ => True);
  have : L ⊢ ∼ψ := WeakerThan.pbl this;
  have : L ⊬ ∼ψ := L.not_neg_of! $ Logic.subst _ hφ₁;
  contradiction;

end

theorem makinson : (L.VerFamily ∨ L.TrivFamily) ∧ ¬(L.VerFamily ∧ L.TrivFamily) := by
  constructor;
  . apply or_iff_not_imp_left.mpr;
    rintro h;
    constructor;
    . exact KD_subset_of_not_VerFamily h;
    . have := KD_subset_of_not_VerFamily h;
      exact subset_Triv_of_KD_subset (L := L);
  . by_contra hC;
    apply Logic.no_bot (L := Modal.Ver);
    have ⟨⟨hVer⟩, ⟨hKD, hTriv⟩⟩ := hC;
    have : Modal.KD ⪯ Modal.Ver := by apply Entailment.WeakerThan.trans (𝓣 := L) <;> infer_instance;
    have h₁ : Modal.Ver ⊢ ∼□⊥ := by apply Entailment.WeakerThan.pbl (show Modal.KD ⊢ ∼□⊥ by simp);
    have h₂ : Modal.Ver ⊢ □⊥ := by simp;
    have : Modal.Ver ⊢ ⊥ := h₁ ⨀ h₂;
    assumption;

lemma VerFamily.notTrivFamily [L.VerFamily] : ¬L.TrivFamily := by
  apply not_and.mp $ makinson (L := L) |>.2;
  assumption;

lemma TrivFamily.notVerFamily [L.TrivFamily] : ¬L.VerFamily := by
  apply not_and'.mp $ makinson (L := L) |>.2;
  assumption;

end Logic

end LO.Modal
end
