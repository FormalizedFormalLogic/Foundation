module

public import Foundation.FirstOrder.Bootstrapping.Syntax

@[expose] public section
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D1}$ and soundness of internal provability.
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open Classical FirstOrder

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁]

lemma derivable_quote {Γ : Finset (SyntacticFormula L)} (d : T ⟹₂ Γ) : T.Derivable (⌜Γ⌝ : V) :=
  ⟨⌜d⌝, by simp only [Derivation2.quote_def]; exact (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩

/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢ φ → T.Provable (⌜φ⌝ : V) := fun h ↦ by
  simpa [Theory.Provable, Theory.Derivable, Theory.Proof, Sentence.quote_def] using derivable_quote (V := V) (provable_iff_derivable2.mp h).some

theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝ := fun h ↦ by
  have h2 := internalize_provability (V := V) h
  rw [TProvable.iff_provable]
  exact h2

@[simp] lemma _root_.LO.FirstOrder.Theory.Provable.complete {φ : Sentence L} :
    T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ :=
  ⟨by simpa [TProvable.iff_provable, Sentence.quote_eq] using Theory.Provable.sound, internal_provable_of_outer_provable⟩

@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} :
    T.Provable (⌜φ⌝ : ℕ) ↔ T ⊢ φ := by
  have hc : T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ := Theory.Provable.complete
  simp only [TProvable.iff_provable, Sentence.quote_eq] at hc ⊢
  exact hc

end LO.FirstOrder.Arithmetic.Bootstrapping
