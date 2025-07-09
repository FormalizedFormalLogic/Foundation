import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Hilbert.WithLoeb.Basic
import Foundation.Modal.Hilbert.WithHenkin.Basic
import Mathlib.Tactic.TFAE

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

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

instance : (Hilbert.GL) ≊ (Hilbert.K4Loeb) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 1;

instance : (Hilbert.GL) ≊ (Hilbert.K4Henkin) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 2;

instance : (Hilbert.GL) ≊ (Hilbert.K4Hen) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 3;


end LO.Modal
