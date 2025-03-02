import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Hilbert.Maximal.Basic
import Foundation.IntProp.Kripke.Hilbert.Cl.Classical


namespace LO.Modal

namespace Formula

def letterless : Formula α → Prop
  | atom _ => False
  | ⊥ => True
  | □φ => φ.letterless
  | φ ➝ ψ => (φ.letterless) ∧ (ψ.letterless)

namespace letterless

variable {φ ψ : Formula α}

@[simp] lemma not_atom : ¬(letterless (atom p)) := by simp [letterless]

lemma def_imp : (φ ➝ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]

lemma def_imp₁ : (φ ➝ ψ).letterless → φ.letterless := λ h => def_imp h |>.1

lemma def_imp₂ : (φ ➝ ψ).letterless → ψ.letterless := λ h => def_imp h |>.2

lemma def_box : (□φ).letterless → φ.letterless := by simp [letterless]

end letterless

end Formula


namespace Logic

variable {L : Logic} [L.Normal] [L.Consistent] {φ ψ : Formula ℕ}

class VerFamily (L : Logic) : Prop where
  subset_Ver : L ⊆ Logic.Ver

class TrivFamily (L : Logic) : Prop where
  KD_subset : Logic.KD ⊆ L
  subset_Triv : L ⊆ Logic.Triv


section

lemma KD_subset_of_not_subset_Ver (h : ¬L.VerFamily) : Logic.KD ⊆ L := by
  sorry;

end


section

open Entailment
open Formula
open IntProp.Formula.Kripke (ClassicalSatisfies)

lemma KD_provability_of_classical_satisfiability (hl : φ.letterless) :
  ((ClassicalSatisfies V (φᵀᴾ)) → Hilbert.KD ⊢! φ) ∧
  (¬(ClassicalSatisfies V (φᵀᴾ)) → Hilbert.KD ⊢! ∼φ)
  := by
  induction φ using Formula.rec' with
  | hatom => simp at hl;
  | hfalsum =>
    simp [TrivTranslation, toPropFormula, ClassicalSatisfies, IntProp.Formula.Kripke.Satisfies];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      simp only [TrivTranslation, toPropFormula] at h;
      rcases IntProp.Formula.Kripke.ClassicalSatisfies.imp_def₂.mp h with (hφ | hψ);
      . exact efq_of_neg! $ ihφ (letterless.def_imp₁ hl) |>.2 hφ;
      . exact imply₁'! $ ihψ (letterless.def_imp₂ hl) |>.1 hψ;
    . intro h;
      simp only [TrivTranslation, toPropFormula] at h;
      have := IntProp.Formula.Kripke.ClassicalSatisfies.imp_def₂.not.mp h;
      push_neg at this;
      rcases this with ⟨hφ, hψ⟩;
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

lemma provable_KD_of_classical_satisfiability (hl : φ.letterless) : (ClassicalSatisfies V (φᵀᴾ)) → Hilbert.KD ⊢! φ :=
  KD_provability_of_classical_satisfiability hl |>.1

lemma provable_not_KD_of_classical_unsatisfiable (hl : φ.letterless) : (¬(ClassicalSatisfies V (φᵀᴾ))) → Hilbert.KD ⊢! ∼φ :=
  KD_provability_of_classical_satisfiability hl |>.2

lemma subset_Triv_of_KD_subset (h : Logic.KD ⊆ L) : L ⊆ Logic.Triv := by
  by_contra hC;
  obtain ⟨φ, hφ₁, hφ₂⟩ := Set.not_subset.mp hC;
  have := Hilbert.Triv.classical_reducible.not.mp hφ₂;
  -- TODO: need 0-subst,
  obtain ⟨V, hV⟩ : ∃ V, ¬(ClassicalSatisfies V (φᵀᴾ)) := by sorry;
  sorry;

end


theorem makinson : (L.VerFamily ∨ L.TrivFamily) ∧ ¬(L.VerFamily ∧ L.TrivFamily) := by
  constructor;
  . apply or_iff_not_imp_left.mpr;
    intro h;
    constructor;
    . exact KD_subset_of_not_subset_Ver h;
    . exact subset_Triv_of_KD_subset $ KD_subset_of_not_subset_Ver h;
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
