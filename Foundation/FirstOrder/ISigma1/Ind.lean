import Foundation.FirstOrder.ISigma1.Bit

/-!
# $\Sigma_n \lor \Pi_n$-Induction

-/

namespace LO.ISigma1

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

@[elab_as_elim] lemma sigma1_pos_succ_induction
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (one : P 1) (succ : ∀ x, P (x + 1) → P (x + 2)) : ∀ x, P x := by
  have : ∀ x, P (x + 1) := by
    intro x
    induction x using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa
    case succ x ih =>
      simpa [add_assoc, one_add_one_eq_two] using succ x ih
  intro x
  rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
  · exact zero
  · exact this x

end LO.ISigma1

namespace LO.Induction

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1

variable {V : Type*} [ORingStruc V]

variable (m : ℕ) [Fact (1 ≤ m)] [V ⊧ₘ* 𝐈𝐍𝐃𝚺 m]

lemma induction_sigma_or_pi {P Q : V → Prop} (hP : 𝚺-[m]-Predicate P) (hQ : 𝚷-[m]-Predicate Q)
    (zero : P 0 ∨ Q 0) (succ : ∀ x, P x ∨ Q x → P (x + 1) ∨ Q (x + 1)) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < Exp.exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < Exp.exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using ISigma1.sigma1_succ_induction
    · clear hp hq zero succ
      definability
    case zero => simpa [hp, hq] using zero
    case succ x ih =>
      have hx' : x ≤ a := le_trans le_self_add hx
      have : P x ∨ Q x := by simpa [hp x hx', hq x hx'] using ih hx'
      simpa [hp (x + 1) hx, hq (x + 1) hx] using succ x this
  have := this a (by rfl)
  simpa [hp, hq] using this

lemma order_induction_sigma_or_pi {P Q : V → Prop} (hP : 𝚺-[m]-Predicate P) (hQ : 𝚷-[m]-Predicate Q)
    (ind : ∀ x, (∀ y < x, P y ∨ Q y) → P x ∨ Q x) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_ISigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < Exp.exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < Exp.exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using ISigma1.sigma1_order_induction
    · clear hp hq ind
      apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.imp
      · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
        apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
        · simp [Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
        · simp [HierarchySymbol.BoldfaceFunction.const]
      · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.or
        · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
          · simp
          · simp
        · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
          · simp
          · simp
    case ind z ih =>
      have : P z ∨ Q z :=
        ind z (fun y hy ↦ by
          have hya : y ≤ a := le_trans (le_of_lt hy) hx
          have : y ∈ p ∨ y ∈ q := ih y hy hya
          simpa [hp, hq, hya] using this)
      simpa [hp, hq, hx] using this
  simpa [hp, hq] using this a (by rfl)

end LO.Induction
