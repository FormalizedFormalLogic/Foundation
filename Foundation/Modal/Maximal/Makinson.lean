import Foundation.Modal.Hilbert.NNFormula
import Foundation.Modal.Maximal.Basic
import Foundation.Modal.Logic.Extension
import Foundation.Modal.Kripke.Logic.Ver
import Foundation.Propositional.ClassicalSemantics.Hilbert

namespace LO.Modal

namespace Logic

variable {L : Logic ℕ} [L.IsNormal] [Entailment.Consistent L] {φ ψ : Formula ℕ}

class VerFamily (L : Logic ℕ) : Prop where
  subset_Ver : L ⪯ Logic.Ver

class TrivFamily (L : Logic ℕ) : Prop where
  KD_subset   : Logic.KD ⪯ L
  subset_Triv : L ⪯ Logic.Triv

section

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

lemma KD_subset_of_not_subset_Ver.lemma₁ (hL : L ⊢! φ) (hV : Logic.Ver ⊬ φ) : ∃ ψ, L ⊢! ◇ψ := by
  obtain ⟨ψ, ⟨Γ, rfl⟩, h⟩ := Hilbert.NNFormula.exists_CNF φ;
  generalize eγ : (⋀Γ.unattach).toFormula = γ at h;
  have : L ⊢! φ.toNNFormula.toFormula ⭤ γ := WeakerThan.pbl h;

  have hγL : γ ∈ L := by sorry;
  have hγV : γ ∉ Logic.Ver := by sorry;

  obtain ⟨⟨_, ⟨Δ, rfl⟩⟩, hδΓ, hδL, hδV⟩ : ∃ δ, δ ∈ Γ ∧ δ.1.toFormula ∈ L ∧ δ.1.toFormula ∉ Logic.Ver := by
    sorry;
  have hΔ₁ : ∀ ψ ∈ Δ, ¬ψ.1.isPrebox := by
    rintro ⟨ψ, _⟩ hψ₁ hψ₂;
    obtain ⟨ξ, rfl⟩ := NNFormula.exists_isPrebox hψ₂;
    have : Logic.Ver ⊢! □ξ.toFormula := by simp;
    sorry;

  have : ∃ Γ: List (Formula ℕ), L ⊢! φ ⭤ ⋀Γ := by sorry;
  sorry;

lemma KD_subset_of_not_subset_Ver (hV : ¬L ⪯ Logic.Ver) : Logic.KD ⪯ L := by
  apply weakerThan_iff.mpr;
  intro φ hφ;
  have : Logic.KD ⪯ Logic.KP := by apply Entailment.Equiv.le $ Entailment.Equiv.symm inferInstance -- TODO: remove!
  replace hφ : Logic.KP ⊢! φ := WeakerThan.pbl hφ;
  induction hφ using Hilbert.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩);
    . simp;
    . obtain ⟨ψ, hψ₁, hψ₂⟩ := not_weakerThan_iff.mp hV;
      obtain ⟨ξ, hξ⟩ := KD_subset_of_not_subset_Ver.lemma₁ hψ₁ hψ₂;
      apply Entailment.mdp! (φ := ◇ξ);
      . exact contra! $ axiomK'! $ nec! $ efq!;
      . exact hξ;
  | mdp hφψ hφ => exact hφψ ⨀ hφ;
  | nec hφ => exact Entailment.nec! hφ;
  | _ => simp;

lemma KD_subset_of_not_VerFamily (h : ¬L.VerFamily) : Logic.KD ⪯ L := by
  apply KD_subset_of_not_subset_Ver;
  tauto;

end


section

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula
open Propositional

variable {v : ClassicalSemantics.Valuation ℕ}

lemma KD_provability_of_classical_satisfiability (hl : φ.letterless) :
  (v ⊧ (φᵀ.toPropFormula) → Logic.KD ⊢! φ) ∧
  (¬(v ⊧ (φᵀ.toPropFormula)) → Logic.KD ⊢! ∼φ)
  := by
  induction φ with
  | hatom => simp at hl;
  | hfalsum => simp [trivTranslate, toPropFormula];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      simp only [trivTranslate, toPropFormula] at h;
      rcases imp_iff_not_or.mp h with (hφ | hψ);
      . exact C_of_N $ ihφ (letterless.def_imp₁ hl) |>.2 hφ;
      . exact C!_of_conseq! $ ihψ (letterless.def_imp₂ hl) |>.1 hψ;
    . intro h;
      simp only [trivTranslate, toPropFormula, Semantics.Realize, Formula.ClassicalSemantics.val] at h;
      push_neg at h;
      rcases h with ⟨hφ, hψ⟩;
      replace hφ := ihφ (letterless.def_imp₁ hl) |>.1 hφ;
      replace hψ := ihψ (letterless.def_imp₂ hl) |>.2 hψ;
      -- TODO: need golf
      apply FiniteContext.deduct'!;
      replace hφ : [φ ➝ ψ] ⊢[Logic.KD]! φ := FiniteContext.of'! hφ;
      replace hψ : [φ ➝ ψ] ⊢[Logic.KD]! ∼ψ := FiniteContext.of'! hψ;
      exact hψ ⨀ (FiniteContext.by_axm! ⨀ hφ);
  | hbox φ ihφ =>
    constructor;
    . intro h;
      apply nec!;
      apply ihφ (letterless.def_box hl) |>.1;
      tauto;
    . intro h;
      have : Logic.KD ⊢! □(∼φ) := nec! $ ihφ (letterless.def_box hl) |>.2 $ by tauto;
      exact negbox_dne'! $ dia_duality'!.mp $ axiomD'! this;

lemma provable_KD_of_classical_satisfiability (hl : φ.letterless) : (v ⊧ φᵀ.toPropFormula) → Logic.KD ⊢! φ :=
  KD_provability_of_classical_satisfiability hl |>.1

lemma provable_KD_of_classical_tautology (hl : φ.letterless) (h : (Semantics.Valid (ClassicalSemantics.Valuation ℕ) (φᵀ.toPropFormula)))
  : Logic.KD ⊢! φ := provable_KD_of_classical_satisfiability hl (h (λ _ => True))

lemma provable_not_KD_of_classical_unsatisfiable (hl : φ.letterless) : (¬(v ⊧ φᵀ.toPropFormula)) → Logic.KD ⊢! ∼φ :=
  KD_provability_of_classical_satisfiability hl |>.2

private lemma subset_Triv_of_KD_subset.lemma₁
  {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _} {v : ClassicalSemantics.Valuation α} :
  v ⊧ (((φᵀ.toPropFormula)⟦s.1⟧)) ↔
  v ⊧ ((φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula)
  := by
  induction φ with
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

lemma subset_Triv_of_KD_subset.lemma₂ {φ : Modal.Formula α} {s : Propositional.ZeroSubstitution _} :
  (∼((φᵀ.toPropFormula)⟦s.1⟧)).isTautology ↔
  ((∼φ⟦(s : Modal.ZeroSubstitution _).1⟧)ᵀ.toPropFormula).isTautology
  := by
  constructor;
  . intro h v hφ;
    apply h v ?_;
    exact lemma₁.mpr hφ;
  . intro h v; exact lemma₁ (φ := ∼φ).mpr $ h v;

@[instance]
theorem subset_Triv_of_KD_subset [Logic.KD ⪯ L] : L ⪯ Logic.Triv := by
  by_contra! hC;
  obtain ⟨φ, hφ₁, hφ₂⟩ := not_weakerThan_iff.mp hC;
  replace hφ₂ := (not_imp_not.mpr Propositional.Hilbert.Cl.completeness) $ Logic.Triv.iff_provable_Cl.not.mp hφ₂;
  obtain ⟨s, h⟩ := ClassicalSemantics.exists_neg_zeroSubst_of_not_isTautology hφ₂;
  let ψ := φ⟦(s : Modal.ZeroSubstitution _).1⟧;
  have : Semantics.Valid (ClassicalSemantics.Valuation ℕ) (∼(ψᵀ.toPropFormula)) := subset_Triv_of_KD_subset.lemma₂.mp h;
  have : Logic.KD ⊢! ∼ψ := provable_not_KD_of_classical_unsatisfiable Formula.letterless_zeroSubst
    $ Semantics.Not.realize_not.mp
    $ this (λ _ => True);
  have : L ⊢! ∼ψ := WeakerThan.pbl this;
  have : L ⊬ ∼ψ := L.not_neg_of! $ Logic.subst! _ hφ₁;
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
    have ⟨⟨hVer⟩, ⟨hKD, hTriv⟩⟩ := hC;
    have : Logic.KD ⪯ Logic.Ver := by apply Entailment.WeakerThan.trans (𝓣 := L) <;> infer_instance;
    have h₁ : Logic.Ver ⊢! ∼□⊥ := by apply Entailment.WeakerThan.pbl (show Logic.KD ⊢! ∼□⊥ by simp);
    have h₂ : Logic.Ver ⊢! □⊥ := by simp;
    have : Logic.Ver ⊢! ⊥ := h₁ ⨀ h₂;
    simpa;

lemma VerFamily.notTrivFamily [L.VerFamily] : ¬L.TrivFamily := by
  apply not_and.mp $ makinson (L := L) |>.2;
  assumption;

lemma TrivFamily.notVerFamily [L.TrivFamily] : ¬L.VerFamily := by
  apply not_and'.mp $ makinson (L := L) |>.2;
  assumption;

end Logic

end LO.Modal
