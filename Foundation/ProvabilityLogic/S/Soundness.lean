import Foundation.Modal.Logic.S.Basic
import Foundation.ProvabilityLogic.GL.Soundness

namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder
open Provability

variable {T₀ T : FirstOrder.Theory ℒₒᵣ} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : Provability T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.Sound ℕ]
         {A B : Formula ℕ}

theorem S.arithmetical_soundness (h : Modal.S ⊢! A) (f : Realization ℒₒᵣ) : ℕ ⊧ₘ₀ f.interpret 𝔅 A := by
  induction h using S.rec' with
  | mem_GL h =>
    exact models_of_provable₀ inferInstance (GL.arithmetical_soundness h);
  | axiomT =>
    simp only [Realization.interpret, models₀_imply_iff];
    intro h;
    exact models_of_provable₀ inferInstance (Iff.mp 𝔅.sound h)
  | mdp ihAB ihA =>
    simp only [Realization.interpret, models₀_imply_iff] at ihAB;
    apply ihAB ihA;

end ProvabilityLogic

end LO
