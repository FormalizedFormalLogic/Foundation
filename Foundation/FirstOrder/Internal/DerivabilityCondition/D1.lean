import Foundation.FirstOrder.Internal.Syntax

/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D1}$ and soundness of internal provability.
-/

namespace LO.ISigma1.Metamath

open Classical FirstOrder

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁]

lemma derivable_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₂ Γ) : T.Derivable (⌜Γ⌝ : V) :=
  ⟨⌜d⌝, by simpa [Semiformula.quote_def] using (⌜d⌝ : Theory.internalize V T ⊢ᵈᵉʳ ⌜Γ⌝).derivationOf⟩

/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢! φ → T.Provable (⌜φ⌝ : V) := fun h ↦ by
  simpa using derivable_quote (V := V) (provable_iff_derivable2.mp h).some

theorem provable_of_provable_arith₀ {σ} : T ⊢!. σ → T.Provable (⌜σ⌝ : V) := fun h ↦ by
  simpa using internalize_provability (T := T) (V := V) <| Axiom.provable_iff.mp h

theorem internal_provable_of_outer_provable {φ} : T ⊢! φ → T.internalize V ⊢! ⌜φ⌝ := fun h ↦ by
  simpa [TProvable.iff_provable] using internalize_provability (V := V) h

theorem internal_sentence_provable_of_outer_sentence_provable {σ} :
    T ⊢!. σ → T.internalize V ⊢! ⌜σ⌝ := fun h ↦
  internal_provable_of_outer_provable <| Axiom.provable_iff.mp h

@[simp] lemma _root_.LO.FirstOrder.Theory.Provable.complete {φ : SyntacticFormula L} :
    T.internalize ℕ ⊢! ⌜φ⌝ ↔ T ⊢! φ :=
  ⟨by simpa [TProvable.iff_provable] using Theory.Provable.sound, internal_provable_of_outer_provable⟩

@[simp] lemma _root_.LO.FirstOrder.Theory.Provable.complete₀ {σ : Sentence L} :
    T.internalize ℕ ⊢! ⌜σ⌝ ↔ T ⊢!. σ :=
  Iff.trans ⟨by simpa [TProvable.iff_provable] using Theory.Provable.smallSound, internal_provable_of_outer_provable⟩
  Axiom.provable_iff.symm

@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : SyntacticFormula L} :
    T.Provable (⌜φ⌝ : ℕ) ↔ T ⊢! φ := by simpa [TProvable.iff_provable] using Theory.Provable.complete

@[simp] lemma provable_iff_provable₀ {T : Theory L} [T.Δ₁] {σ : Sentence L} :
    T.Provable (⌜σ⌝ : ℕ) ↔ T ⊢!. σ := by simpa [TProvable.iff_provable] using Theory.Provable.complete₀

end LO.ISigma1.Metamath
