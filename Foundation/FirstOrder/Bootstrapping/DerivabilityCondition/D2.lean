module

public import Foundation.FirstOrder.Bootstrapping.Syntax

@[expose] public section
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D2}$
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (T : Theory L) [T.Δ₁]

/-- Hilbert–Bernays provability condition D2 -/
theorem modus_ponens {φ ψ : Proposition L} (hφψ : Provable T (⌜φ 🡒 ψ⌝ : V)) (hφ : Provable T (⌜φ⌝ : V)) :
    Provable T (⌜ψ⌝ : V) := by
  apply (tprovable_tquote_iff_provable_quote (L := L)).mp
  have hφψ : Theory.internalize V T ⊢ ⌜φ⌝ 🡒 ⌜ψ⌝ := by simpa using (tprovable_tquote_iff_provable_quote (L := L)).mpr hφψ
  have hφ : Theory.internalize V T ⊢ ⌜φ⌝ := (tprovable_tquote_iff_provable_quote (L := L)).mpr hφ
  exact hφψ ⨀ hφ

theorem modus_ponens_sentence {σ τ : Sentence L} (hστ : Provable T (⌜σ 🡒 τ⌝ : V)) (hσ : Provable T (⌜σ⌝ : V)) :
    Provable T (⌜τ⌝ : V) := by
  apply (tprovable_tquote_iff_provable_quote (L := L)).mp
  have hστ : Theory.internalize V T ⊢ ⌜σ⌝ 🡒 ⌜τ⌝ := by simpa using (tprovable_tquote_iff_provable_quote (L := L)).mpr hστ
  have hσ : Theory.internalize V T ⊢ ⌜σ⌝ := (tprovable_tquote_iff_provable_quote (L := L)).mpr hσ
  exact hστ ⨀ hσ

end LO.FirstOrder.Arithmetic.Bootstrapping
