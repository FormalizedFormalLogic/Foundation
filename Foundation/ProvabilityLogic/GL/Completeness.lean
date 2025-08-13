import Foundation.ProvabilityLogic.SolovaySentences
import Foundation.Modal.Kripke.Logic.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot


/-!
# Solovay's arithmetical completeness of $\mathsf{GL}$
-/

namespace LO.ProvabilityLogic

open Entailment Entailment.FiniteContext
open FirstOrder Arithmetic
open Modal
open Modal.Kripke

variable {T : ArithmeticTheory} [T.Δ₁] [𝐈𝚺₁ ⪯ T] {A : Modal.Formula _}

theorem unprovable_realization_exists
    (M₁ : Model) [Fintype M₁] {r₁ : M₁} [M₁.IsFiniteTree r₁]
    (hA : ¬r₁ ⊧ A) (h : M₁.finHeight < T.standardProvability.height) :
    ∃ f : T.PLRealization, T ⊬. f A := by
  let M₀ := M₁.extendRoot 1
  let r₀ : M₀ := Frame.extendRoot.root
  have hdnA : r₀ ⊧ ◇(∼A) := by
    suffices ∃ i, r₀ ≺ i ∧ ¬i ⊧ A by simpa [Formula.Kripke.Satisfies]
    refine ⟨.inr r₁, ?_, ?_⟩
    · simpa [r₀] using Frame.extendRoot.rooted_original
    · exact Model.extendRoot.inr_satisfies_iff |>.not.mpr hA
  let S : SolovaySentences T.standardProvability M₀.toFrame r₀ :=
    SolovaySentences.standard T M₀.toFrame
  use S.realization
  intro hC
  have : T.standardProvability.height ≤ M₁.finHeight := by
    apply PartENat.le_of_lt_add_one
    calc
      (Theory.standardProvability T).height < M₀.finHeight := S.theory_height hdnA hC
      _                                     = M₁.finHeight + 1 := by simp [M₀]
  exact not_lt_of_ge this h

/-- Arithmetical completeness of GL-/
theorem GL.arithmetical_completeness (height : T.standardProvability.height = ⊤) :
    (∀ f : T.PLRealization, T ⊢!. f A) → Modal.GL ⊢! A := by
  suffices ¬Hilbert.GL ⊢! A → ∃ f : T.PLRealization, T ⊬. f A by
    contrapose
    intro hA
    simpa using this <| Hilbert.Normal.iff_logic_provable_provable |>.not.mp hA
  intro hA
  obtain ⟨M₁, r₁, _, hA₁⟩ :=
    Logic.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA
  have : Fintype M₁ := Fintype.ofFinite _
  exact unprovable_realization_exists M₁ hA₁ <| by simp [height]

theorem GLBoxBot'.arithmetical_completeness {n : ℕ} (height : n ≤ T.standardProvability.height) :
    (∀ f : T.PLRealization, T ⊢!. f A) → Modal.GL ⊢! □^[n] ⊥ ➝ A := by
  suffices ¬Hilbert.GL ⊢! □^[n]⊥ ➝ A → ∃ f : T.PLRealization, T ⊬. f A by
    contrapose
    intro hA
    simpa using this <| Hilbert.Normal.iff_logic_provable_provable |>.not.mp hA
  intro hA
  obtain ⟨M₁, r₁, _, hA₁⟩ :=
    Logic.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA
  have : Fintype M₁ := Fintype.ofFinite _
  have hA₁ : r₁ ⊧ □^[n]⊥ ∧ ¬r₁ ⊧ A := by
    simpa [Formula.Kripke.Satisfies] using hA₁
  have M₁_height : M₁.finHeight < n :=
    finHeight_lt_iff_satisfies_boxbot.mpr hA₁.1
  exact unprovable_realization_exists M₁ hA₁.2 <| lt_of_lt_of_le (by simp [M₁_height]) height

theorem GL.arithmetical_completeness_iff (height : T.standardProvability.height = ⊤) {A} :
    (∀ f : T.PLRealization, T ⊢!. f A) ↔ Modal.GL ⊢! A :=
  ⟨GL.arithmetical_completeness height, GL.arithmetical_soundness⟩

theorem GL.arithmetical_completeness_sound_iff [T.SoundOnHierarchy 𝚺 1] {A} :
    (∀ f : T.PLRealization, T ⊢!. f A) ↔ Modal.GL ⊢! A :=
  GL.arithmetical_completeness_iff (Provability.hight_eq_top_of_sigma1_sound T)

end LO.ProvabilityLogic
