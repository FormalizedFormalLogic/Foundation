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

lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : T.Derivable (⌜Γ⌝ : V) :=
  ⟨⌜d⌝, by simpa [Semiformula.quote_def] using (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩

/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢ φ → T.Provable (⌜φ⌝ : V) := fun h ↦ by
  simpa using derivable_quote (V := V) (provable_iff_derivable2.mp h).some

theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝ := fun h ↦ by
  simpa [TProvable.iff_provable] using internalize_provability (V := V) h

@[simp] lemma _root_.LO.FirstOrder.Theory.Provable.complete {φ : Sentence L} :
    T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ :=
  ⟨by simpa [TProvable.iff_provable] using Theory.Provable.sound, internal_provable_of_outer_provable⟩

@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} :
    T.Provable (⌜φ⌝ : ℕ) ↔ T ⊢ φ := by simpa [TProvable.iff_provable] using Theory.Provable.complete

end LO.FirstOrder.Arithmetic.Bootstrapping
