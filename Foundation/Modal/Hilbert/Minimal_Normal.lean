import Foundation.Modal.Hilbert.Minimal.Basic
import Foundation.Modal.Hilbert.Normal.Basic


namespace LO.Modal

open LO.Modal.Entailment

lemma Hilbert.equiv_WithRE_Normal
  {HE : Hilbert.WithRE α} {HN : Hilbert.Normal α}
  [RE HN] [Necessitation HE]
  (provable_HE : ∀ φ ∈ HE.axiomInstances, HN ⊢! φ)
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HE ⊢! φ)
  : HE ≊ HN := by
  apply Entailment.Equiv.iff.mpr
  intro φ
  suffices HE ⊢! φ ↔ HN ⊢! φ by
    simpa [Entailment.theory, Set.mem_setOf_eq]
  constructor
  . intro h
    induction h using Hilbert.WithRE.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ
    | re h => apply re! h
    | @axm ψ s h =>
      apply provable_HE
      use ψ
      constructor
      . assumption
      . use s
    | _ => simp
  . intro h
    induction h using Hilbert.Normal.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ
    | nec ihφ => apply Entailment.nec! ihφ
    | @axm ψ s h =>
      apply provable_HN
      use ψ
      constructor
      . assumption
      . use s
    | _ => simp

lemma Hilbert.equiv_logic_WithRE_Normal
  {HE : Hilbert.WithRE α} {HN : Hilbert.Normal α}
  [RE HN] [Necessitation HE]
  (provable_HE : ∀ φ ∈ HE.axiomInstances, HN ⊢! φ)
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HE ⊢! φ)
  : HE.logic ≊ HN.logic := by
  apply Entailment.Equiv.iff.mpr
  intro φ
  suffices HE ⊢! φ ↔ HN ⊢! φ by simpa [Entailment.theory, Set.mem_setOf_eq]
  exact Entailment.Equiv.iff.mp (Hilbert.equiv_WithRE_Normal provable_HE provable_HN) φ

instance : 𝐄𝐌𝐂𝐍 ≊ Modal.K := by
  apply Hilbert.equiv_logic_WithRE_Normal
  . rintro _ ⟨φ, (rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp
  . rintro _ ⟨φ, rfl, ⟨_, rfl⟩⟩; simp

instance : 𝐄𝐌𝐂𝐍𝐓 ≊ Modal.KT := by
  apply Hilbert.equiv_logic_WithRE_Normal
  . rintro _ ⟨φ, (rfl | rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp
  . rintro _ ⟨φ, (rfl | rfl), ⟨_, rfl⟩⟩ <;> simp

instance : 𝐄𝐌𝐂𝐍𝐓𝟒 ≊ Modal.S4 := by
  apply Hilbert.equiv_logic_WithRE_Normal
  . rintro _ ⟨φ, (rfl | rfl | rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp
  . rintro _ ⟨φ, (rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp

end LO.Modal
