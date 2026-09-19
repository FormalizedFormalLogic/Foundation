module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

@[expose] public section
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D1}$ and soundness of internal
provability.
-/

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

open Classical in
lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂Γ) : Derivable T (⌜Γ⌝ : V) :=
  open Classical in ⟨⌜d⌝, by
    simpa [Semiformula.quote_def] using! (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩

open Classical in
/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V) := fun h ↦ by
  simpa using! derivable_quote (V := V) (provable_iff_derivable2.mp h).some

open Classical in
theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝ := fun h ↦ by
  simpa [TProvable.iff_provable] using! internalize_provability (V := V) h

open Classical in
@[simp] lemma Provable.complete {φ : Sentence L} :
    T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ :=
  ⟨by simpa [TProvable.iff_provable] using! Provable.sound, internal_provable_of_outer_provable⟩

open Classical in
@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} :
    Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ := by simpa [TProvable.iff_provable] using! Provable.complete

end FFL.FirstOrder.Arithmetic.Bootstrapping
