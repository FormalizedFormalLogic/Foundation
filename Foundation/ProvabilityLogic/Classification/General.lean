module

public import Foundation.ProvabilityLogic.Classification.UnivTrace

/-!
# Classification of provability logics

The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ⁻ X`, `D ∩ GLβ⁻ X`, and
`S ∩ GLβ⁻ X`, where `X` is its trace.

## References

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] {N : Set ℕ}

/-- `U` extended by the standard `T`-interpretations of `TBB n` for `n ∈ N`. -/
noncomputable def _root_.FFL.FirstOrder.ArithmeticTheory.addTBB
    (T U : ArithmeticTheory) [T.Δ₁] (N : Set ℕ) : ArithmeticTheory :=
  U ∪ (fun n ↦ (TBB n : LetterlessFormula).interpret ⟨Empty.elim⟩ T.standardProvability) '' N

lemma _root_.FFL.FirstOrder.ArithmeticTheory.weakerThan_addTBB : U ⪯ T.addTBB U N :=
  WeakerThan.ofSubset Set.subset_union_left

instance [𝗜𝚺₁ ⪯ U] : 𝗜𝚺₁ ⪯ T.addTBB U N :=
  (inferInstance : 𝗜𝚺₁ ⪯ U).trans ArithmeticTheory.weakerThan_addTBB

lemma provabilityLogic_subset_addTBB :
    (T.provabilityLogicRelativeTo U : Logic α) ⊆ T.provabilityLogicRelativeTo (T.addTBB U N) :=
  fun _ hA f ↦ ArithmeticTheory.weakerThan_addTBB.pbl (hA f)

lemma TBB_mem_provabilityLogic_addTBB {n : ℕ} (hn : n ∈ N) :
    (TBB n : Formula α) ∈ T.provabilityLogicRelativeTo (T.addTBB U N) :=
  fun f ↦ by_axm <| Set.mem_union_right U
    ⟨n, hn, by simpa using (interpret_lift (A := TBB n)).symm⟩

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma imp_mem_provabilityLogic_of_mem_addTBB (hN : N.Finite) {A : Formula α}
    (h : A ∈ T.provabilityLogicRelativeTo (T.addTBB U N)) :
    (⩕ n ∈ hN.toFinset, TBB n : LetterlessFormula).lift 🡒 A ∈ T.provabilityLogicRelativeTo U := by
  intro f;
  obtain ⟨⟨s, hs⟩, h₁⟩ := Theory.compact_add_right (h f);
  apply C_trans _ h₁;
  apply right_Fconj_intro;
  intro σ hσ;
  obtain ⟨n, hn, rfl⟩ := hs hσ;
  have h₂ : U ⊢ f T ((⩕ n ∈ hN.toFinset, TBB n) 🡒 TBB n : LetterlessFormula).lift :=
    provabilityLogic_of_GL (Logic.GL.lift_mem_iff.mpr <| by
      ext k; simpa using (em (k = n)).imp (· ▸ hn) id) f;
  simpa only [standardInterpret, interpret_lift, interpret] using h₂;

lemma trace_provabilityLogic_addTBB :
    (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α).trace = .univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_provabilityLogic_iff.mpr;
  by_cases hn : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace;
  · exact provabilityLogic_subset_addTBB <| TBB_mem_provabilityLogic_of_mem_trace hn;
  · exact TBB_mem_provabilityLogic_addTBB hn;

variable (hL : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite)

include hL in
lemma provabilityLogic_addTBB_subset_S (h : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α) ⊆ 𝐒 := by
  by_contra h₁;
  have h₂ : (𝐒 : Logic α) ⊢ (⩕ n ∈ hL.toFinset, TBB n : LetterlessFormula).lift :=
    Logic.GLAlpha.subset_S <| Logic.GLAlpha.mem_iff.mpr
      ⟨by simpa [LetterlessFormula.trace] using hL.biUnion fun _ _ ↦ Set.finite_singleton _,
        Set.subset_univ _⟩;
  exact Logic.S.consistent <| h (imp_mem_provabilityLogic_of_mem_addTBB hL <|
    (provabilityLogic_eq_GLBetaMinus h₁).symm.subset <| Logic.GLBetaMinus.mem_iff.mpr <| by
      simp [trace_provabilityLogic_addTBB]) ⨀ h₂;

lemma provabilityLogic_eq_inter_GLBetaMinus :
    (T.provabilityLogicRelativeTo U : Logic α) =
      T.provabilityLogicRelativeTo (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) ∩
        𝐆𝐋β⁻ _ hL := by
  apply subset_antisymm;
  · exact Set.subset_inter provabilityLogic_subset_addTBB (Logic.subset_GLBetaMinus_trace hL);
  · rintro A ⟨h₁, h₂⟩;
    have h₃ : 𝐆𝐋 ⊢ ∼(⩕ n ∈ hL.toFinset, TBB n : LetterlessFormula).lift 🡒 A :=
      GL_imp_of_height_not_mem_trace fun _ _ _ hM hn ↦ absurd (Logic.GLBetaMinus.mem_iff.mp h₂ hn)
        (by simpa [Kripke.RootedModel.height] using forces_lift_iff (A := ∼_) |>.mp hM);
    exact provabilityLogic_mdp (provabilityLogic_of_GL <| by cl_prover [h₃])
      (imp_mem_provabilityLogic_of_mem_addTBB hL h₁);

/-- The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ⁻ X`, `D ∩ GLβ⁻ X`, and
`S ∩ GLβ⁻ X`, where `X` is its trace.

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/
theorem provabilityLogic_classification :
    (T.provabilityLogicRelativeTo U : Logic α) =
        𝐆𝐋α (T.provabilityLogicRelativeTo U : Logic α).trace ∨
      ∃ hL : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite,
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐆𝐋β⁻ _ hL ∨
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐃 ∩ 𝐆𝐋β⁻ _ hL ∨
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐒 ∩ 𝐆𝐋β⁻ _ hL := by
  rcases (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.finite_or_infinite with hL | hL;
  · by_cases h : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒;
    · rcases provabilityLogic_eq_A_or_eq_D_or_eq_S trace_provabilityLogic_addTBB
        (provabilityLogic_addTBB_subset_S hL h) with h | h | h <;>
      grind [provabilityLogic_eq_inter_GLBetaMinus hL, Logic.GLAlpha.eq_inter_GLBetaMinus hL];
    · grind [provabilityLogic_eq_GLBetaMinus h];
  · grind [provabilityLogic_eq_GLAlpha hL];

end

end FFL.ProvabilityLogic

end
