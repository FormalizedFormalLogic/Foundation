import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Hilbert.WithLoeb.Basic
import Foundation.Modal.Hilbert.WithHenkin.Basic
import Mathlib.Tactic.TFAE

namespace LO.Modal

variable {α : Type*}

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

lemma Hilbert.equiv_Normal_WithLoeb
  {HN : Hilbert.Normal α} {HL : Hilbert.WithLoeb α}
  [LoebRule HN]
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HL ⊢! φ)
  (provable_HL : ∀ φ ∈ HL.axiomInstances, HN ⊢! φ)
  : HN ≊ HL := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  suffices HN ⊢! φ ↔ HL ⊢! φ by simpa [Entailment.theory, Set.mem_setOf_eq];
  constructor;
  . intro h;
    induction h using Hilbert.Normal.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | @axm ψ s h =>
      apply provable_HN;
      use ψ;
      constructor;
      . assumption;
      . use s;
    | _ => simp;
  . intro h;
    induction h using Hilbert.WithLoeb.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | loeb ihφ => apply Entailment.loeb! ihφ;
    | @axm ψ s h =>
      apply provable_HL;
      use ψ;
      constructor;
      . assumption;
      . use s;
    | _ => simp;

lemma Hilbert.equiv_logic_Normal_WithLoeb
  {HN : Hilbert.Normal α} {HL : Hilbert.WithLoeb α} [LoebRule HN]
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HL ⊢! φ)
  (provable_HL : ∀ φ ∈ HL.axiomInstances, HN ⊢! φ)
  : HN.logic ≊ HL.logic := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  suffices HN ⊢! φ ↔ HL ⊢! φ by simpa [Entailment.theory, Set.mem_setOf_eq];
  exact Entailment.Equiv.iff.mp (Hilbert.equiv_Normal_WithLoeb provable_HN provable_HL) φ;


lemma Hilbert.equiv_Normal_WithHenkin
  {HN : Hilbert.Normal α} {HH : Hilbert.WithHenkin α}
  [HenkinRule HN]
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HH ⊢! φ)
  (provable_HH : ∀ φ ∈ HH.axiomInstances, HN ⊢! φ)
  : HN ≊ HH := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  suffices HN ⊢! φ ↔ HH ⊢! φ by simpa [Entailment.theory, Set.mem_setOf_eq];
  constructor;
  . intro h;
    induction h using Hilbert.Normal.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | @axm ψ s h =>
      apply provable_HN;
      use ψ;
      constructor;
      . assumption;
      . use s;
    | _ => simp;
  . intro h;
    induction h using Hilbert.WithHenkin.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | henkin ihφ => apply Entailment.henkin! ihφ;
    | @axm ψ s h =>
      apply provable_HH;
      use ψ;
      constructor;
      . assumption;
      . use s;
    | _ => simp;

lemma Hilbert.equiv_logic_Normal_WithHenkin
  {HN : Hilbert.Normal α} {HH : Hilbert.WithHenkin α}
  [HenkinRule HN]
  (provable_HN : ∀ φ ∈ HN.axiomInstances, HH ⊢! φ)
  (provable_HH : ∀ φ ∈ HH.axiomInstances, HN ⊢! φ)
  : HN.logic ≊ HH.logic := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  suffices HN ⊢! φ ↔ HH ⊢! φ by simpa [Entailment.theory, Set.mem_setOf_eq];
  exact Entailment.Equiv.iff.mp (Hilbert.equiv_Normal_WithHenkin provable_HN provable_HH) φ;



theorem provable_GL_TFAE : [
  Hilbert.GL ⊢! φ,
  Hilbert.K4Loeb ⊢! φ,
  Hilbert.K4Henkin ⊢! φ,
  Hilbert.K4Hen ⊢! φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm _ h => rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_have 2 → 3 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithLoeb.rec! with
    | axm _ h => rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | loeb ihφ => exact loeb! ihφ;
    | _ => simp;
  tfae_have 3 → 4 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithHenkin.rec! with
    | axm _ h => rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | henkin ihφ => exact henkin! ihφ;
    | _ => simp;
  tfae_have 4 → 1 := by
    clear * -;
    intro h;
    induction h using Hilbert.Normal.rec! with
    | axm _ h => rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_finish;


instance : Modal.GL ≊ Modal.K4Loeb := by
  apply Entailment.Equiv.iff.mpr;
  simp only [
    Hilbert.Normal.iff_logic_provable_provable,
    Hilbert.WithLoeb.iff_logic_provable_provable
  ];
  intro φ;
  apply provable_GL_TFAE.out 0 1;

instance : Modal.GL ≊ Modal.K4Henkin := by
  apply Entailment.Equiv.iff.mpr;
  simp only [
    Hilbert.Normal.iff_logic_provable_provable,
    Hilbert.WithHenkin.iff_logic_provable_provable
  ];
  intro φ;
  apply provable_GL_TFAE.out 0 2;

instance : Modal.GL ≊ Modal.K4Hen := by
  apply Entailment.Equiv.iff.mpr;
  simp only [
    Hilbert.Normal.iff_logic_provable_provable,
  ];
  intro φ;
  apply provable_GL_TFAE.out 0 3;

end LO.Modal
