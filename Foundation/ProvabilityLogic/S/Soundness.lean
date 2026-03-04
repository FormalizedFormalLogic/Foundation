module

public import Foundation.Modal.Logic.S.Basic
public import Foundation.ProvabilityLogic.GL.Soundness

@[expose] public section
namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder
open FirstOrder.ProvabilityAbstraction

variable {T₀ T : FirstOrder.ArithmeticTheory} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : Provability T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.SoundOn ℕ]
         {A B : Formula ℕ}

theorem S.arithmetical_soundness (h : Modal.S ⊢ A) (f : Realization 𝔅) : ℕ ⊧ₘ f A := by
  induction h using S.rec' with
  | mem_GL h =>
    exact models_of_provable inferInstance (GL.arithmetical_soundness h);
  | axiomT =>
    simp only [Realization.interpret, Models, LO.Semantics.Imp.models_imply];
    intro h;
    exact models_of_provable inferInstance (𝔅.sound_on h)
  | mdp ihAB ihA =>
    simp only [Realization.interpret, Models, LO.Semantics.Imp.models_imply] at ihAB;
    apply ihAB ihA;

end ProvabilityLogic

end LO
