module

public import Foundation.ProvabilityLogic.Arithmetic.ModifiedSolovaySentences
public import Foundation.ProvabilityLogic.Classification.ProvabilityLogicTrace
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Reflection

/-!
# Provability logics between `A` and `D`

If the provability logic of `T` relative to `U` has trace `ℕ` and contains a formula outside `𝐀`,
then `U` proves every `𝚺₁` reflection instance for `T`, and hence the logic contains `𝐃`.
So no such provability logic lies strictly between `𝐀` and `𝐃`.

## References

- [AB05, Lemma 51, Corollary 52(ii), Corollary 55]
- [Bek90, Lemma 5, Assertion 2, §6 Theorem 2]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder ProvabilityAbstraction Kripke Model Model.World RootedModel Formula

namespace Kripke.StrongReflexiveCountermodel

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : Formula α}

/-- The strong reflexive countermodel `M.graft v (Fin 1)` of `A`, whose `u` is the single point of
the chain, for a countermodel `M` of `A` whose root sees an `A`-reflexive world `v`.

- [Bek90, Lemma 5]
-/
def ofReflexive (M : RootedModel κ α) [M.IsGL] (hA : M.root ⊮[_] A) {v : M.World}
    (Rv : M.root ≺ v) (hv : v.IsReflexiveOf A.subfmls.prebox) :
    StrongReflexiveCountermodel (κ ⊕ Fin 1) A :=
  have ha : ∀ B, □B ∈ A.subfmls → v ⊩[_] □B 🡒 B :=
    fun B hB ↦ hv B (FormulaFinset.mem_prebox.mpr hB)
  let a : M.NonRoot := ⟨v, by rintro rfl; exact not_rel_root Rv⟩
  have h {B : Formula α} (hB : B ∈ A.subfmls) := graft.forces_iff (fun _ ↦ subfmls_trans) ha hB
  {
    toRootedModel := M.graft a (Fin 1)
    root_not_forces := ((h mem_subfmls_self).1 M.root).not.mpr hA
    u := .inr 0
    root_rel_u := rfl
    isReflexiveOf_u B hB hB' :=
      have hB₁ := FormulaFinset.mem_prebox.mp hB
      ((h (subfmls_trans hB₁ (by grind))).2 0).mpr <| ha B hB₁ <| ((h hB₁).2 0).mp hB'
    eq_root_of_rel_u := by
      rintro (z | j) hz <;> simp_all
  }

end Kripke.StrongReflexiveCountermodel

universe u

variable {α : Type u} {T U : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {A : Formula α}
  {σ : ArithmeticSentence}

variable [𝗜𝚺₁ ⪯ U]

theorem provable_sigma1_reflection_of_mem_of_not_A
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
    (hAL : A ∈ T.provabilityLogicRelativeTo U) (hAA : 𝐀 ⊬ A) (hσ : Arithmetic.Hierarchy 𝚺 1 σ) :
    U ⊢ T.standardProvability.refl σ := by
  classical
  obtain ⟨κ, _, N, _, v, hN, Rv, hv⟩ := Logic.A.exists_countermodel hAA;
  let M := StrongReflexiveCountermodel.ofReflexive N hN Rv hv;
  have : Fintype M.World := Fintype.ofFinite _;
  have : M.IsGL := inferInstanceAs (N.graft _ (Fin 1)).IsGL;
  let S := standardModifiedSolovaySentences T M hσ;
  have hf : 𝗜𝚺₁ ⊢ S.realization T (∼□^[M.height]⊥ ⋏ A) 🡒 T.standardProvability.refl σ := by
    have h := S.reflection;
    simp only [Provability.conItr, standardInterpret, interpret, interpret_boxItr] at h ⊢;
    cl_prover [h];
  exact WeakerThan.pbl hf ⨀ provabilityLogic_mdp (provabilityLogic_mdp (provabilityLogic_of_GL and₃)
    ((A_weakerThan_provabilityLogic hT).wk Logic.A.neg_boxItr_bot)) hAL S.realization;

lemma provable_localReflectionOn_sigma1_of_mem_of_not_A
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
    (hAL : A ∈ T.provabilityLogicRelativeTo U) (hAA : 𝐀 ⊬ A) :
    U ⊢* T.standardProvability.reflOn (Arithmetic.Hierarchy 𝚺 1) := by
  rintro _ ⟨σ, hσ, rfl⟩;
  apply provable_sigma1_reflection_of_mem_of_not_A hT hAL hAA hσ;

/-- If the provability logic of `T` relative to `U` has trace `ℕ` and strictly contains `𝐀`, then
it contains `𝐃`.

- [AB05, Lemma 51, Corollary 52(ii)]
-/
theorem D_weakerThan_provabilityLogic
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
    (h : 𝐀 ⪱ T.provabilityLogicRelativeTo U (α := α)) :
    𝐃 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  obtain ⟨-, A, hAA, hAL⟩ := strictlyWeakerThan_iff.mp h;
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ (rfl | ⟨B, C, rfl⟩);
  · exact (A_weakerThan_provabilityLogic hT).wk (Logic.A.neg_boxItr_bot (n := 1));
  · exact fun f ↦ provable_sigma1_reflection_of_mem_of_not_A hT hAL hAA <| by
      simp [interpret, Arithmetic.standardProvability_def]

/-- No provability logic with trace `ℕ` lies strictly between `𝐀` and `𝐃`.

- [AB05, Corollary 55]
-/
theorem not_A_strictlyWeakerThan_provabilityLogic_strictlyWeakerThan_D
    (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ) :
    ¬(𝐀 ⪱ T.provabilityLogicRelativeTo U (α := α) ∧ T.provabilityLogicRelativeTo U (α := α) ⪱ 𝐃) :=
  fun ⟨h₁, h₂⟩ ↦ h₂.notWT (D_weakerThan_provabilityLogic hT h₁)

end FFL.ProvabilityLogic

end
