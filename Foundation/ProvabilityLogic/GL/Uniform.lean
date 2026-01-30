module

public import Foundation.ProvabilityLogic.GL.Completeness

@[expose] public section
namespace LO.ProvabilityLogic.GL

open LO.Entailment Entailment.FiniteContext
open FirstOrder Arithmetic
open Modal
open Modal.Kripke

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- TODO: prove this!
axiom uniform_arithmetical_completeness [T.SoundOnHierarchy 𝚺 1] : ∃ f : T.StandardRealization, ∀ A, T ⊢ f A ↔ Modal.GL ⊢ A

protected noncomputable def uniformStandardRealization (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T.StandardRealization := GL.uniform_arithmetical_completeness.choose

@[grind =]
lemma uniformStandardRealization_spec : T ⊢ (GL.uniformStandardRealization T) A ↔ Modal.GL ⊢ A := GL.uniform_arithmetical_completeness.choose_spec A

end LO.ProvabilityLogic.GL
