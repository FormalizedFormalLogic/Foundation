import Foundation.ProvabilityLogic.SolovaySentences
import Foundation.ProvabilityLogic.Arithmetic

/-!
# Solovay's arithmetical completeness of $\mathsf{GL}$ and $\mathsf{GL} + \square^n \bot$
-/

namespace LO.ProvabilityLogic

open Entailment Entailment.FiniteContext
open FirstOrder Arithmetic
open Modal
open Modal.Kripke
open ArithmeticTheory (ProvabilityLogic)

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {A : Modal.Formula _}

theorem unprovable_realization_exists
    (M₁ : Model) [Fintype M₁] {r₁ : M₁} [M₁.IsFiniteTree r₁]
    (hA : ¬r₁ ⊧ A) (h : M₁.finHeight < T.height) :
    ∃ f : T.StandardRealization, T ⊬. f A := by
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
  have : T.height ≤ M₁.finHeight := by
    apply PartENat.le_of_lt_add_one
    calc
      (Theory.standardProvability T).height < M₀.finHeight := S.theory_height hdnA hC
      _                                     = M₁.finHeight + 1 := by simp [M₀]
  exact not_lt_of_ge this h

/-- Arithmetical completeness of $\mathsf{GL}$-/
theorem GL.arithmetical_completeness (height : T.height = ⊤) :
    (∀ f : T.StandardRealization, T ⊢!. f A) → Modal.GL ⊢! A := by
  suffices ¬Modal.GL ⊢! A → ∃ f : T.StandardRealization, T ⊬. f A by
    contrapose!;
    assumption;
  intro hA
  obtain ⟨M₁, r₁, _, hA₁⟩ := GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA
  have : Fintype M₁ := Fintype.ofFinite _
  exact unprovable_realization_exists M₁ hA₁ <| by simp [height]

theorem GLPlusBoxBot.arithmetical_completeness_aux {n : ℕ} (height : n ≤ T.height) :
    (∀ f : T.StandardRealization, T ⊢!. f A) → Modal.GL ⊢! □^[n] ⊥ ➝ A := by
  suffices ¬Modal.GL ⊢! □^[n]⊥ ➝ A → ∃ f : T.StandardRealization, T ⊬. f A by
    contrapose!;
    assumption;
  intro hA
  obtain ⟨M₁, r₁, _, hA₁⟩ := GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA
  have : Fintype M₁ := Fintype.ofFinite _
  have hA₁ : r₁ ⊧ □^[n]⊥ ∧ ¬r₁ ⊧ A := by
    simpa [Formula.Kripke.Satisfies] using hA₁
  have M₁_height : M₁.finHeight < n :=
    finHeight_lt_iff_satisfies_boxbot.mpr hA₁.1
  exact unprovable_realization_exists M₁ hA₁.2 <| lt_of_lt_of_le (by simp [M₁_height]) height

theorem GL.arithmetical_completeness_iff (height : T.height = ⊤) {A} :
    (∀ f : T.StandardRealization, T ⊢!. f A) ↔ Modal.GL ⊢! A :=
  ⟨GL.arithmetical_completeness height, GL.arithmetical_soundness⟩

theorem GL.arithmetical_completeness_sound_iff [T.SoundOnHierarchy 𝚺 1] {A} :
    (∀ f : T.StandardRealization, T ⊢!. f A) ↔ Modal.GL ⊢! A :=
  GL.arithmetical_completeness_iff (Provability.hight_eq_top_of_sigma1_sound T)

/-- Provability logic of $\Sigma_1$-sound theory contains $\mathsf{I}\Sigma_1$ is $\mathsf{GL}$-/
theorem provabilityLogic_eq_GL_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] :
    ProvabilityLogic T T ≊ Modal.GL := by
  apply Logic.iff_equal_provable_equiv.mp
  ext A
  simpa [ArithmeticTheory.ProvabilityLogic] using
    GL.arithmetical_completeness_sound_iff

open Classical

/-- Arithmetical completeness of $\mathsf{GL} + \square^n \bot$-/
theorem GLPlusBoxBot.arithmetical_completeness
    {n : ℕ∞} (hn : n ≤ T.height) (h : ∀ f : T.StandardRealization, T ⊢!. f A) :
    Modal.GLPlusBoxBot n ⊢! A := by
  match n with
  | .none =>
    have : T.height = ⊤ := eq_top_iff.mpr hn
    simpa using GL.arithmetical_completeness this h
  | .some n =>
    apply iff_provable_GLPlusBoxBot_provable_GL.mpr
    exact GLPlusBoxBot.arithmetical_completeness_aux (n := n) (by simpa using hn) h

theorem GLPlusBoxBot.arithmetical_completeness_iff :
    (∀ f : T.StandardRealization, T ⊢!. f A) ↔ Modal.GLPlusBoxBot T.height.toWithTop ⊢! A :=
  ⟨GLPlusBoxBot.arithmetical_completeness (T := T) (by simp), GLPlusBoxBot.arithmetical_soundness⟩

/-- Provability logic of theory contains $\mathsf{I}\Sigma_1$ is $\mathsf{GL} + \square^{\text{height of } T} \bot$-/
theorem provabilityLogic_eq_GLPlusBoxBot :
    ProvabilityLogic T T ≊ Modal.GLPlusBoxBot T.height.toWithTop := by
  apply Logic.iff_equal_provable_equiv.mp
  ext A
  simpa [ArithmeticTheory.ProvabilityLogic] using
    GLPlusBoxBot.arithmetical_completeness_iff

instance : ProvabilityLogic 𝗣𝗔 𝗣𝗔 ≊ Modal.GL := provabilityLogic_eq_GL_of_sigma1_sound

end LO.ProvabilityLogic
