module

public import Foundation.FirstOrder.Arithmetic.Omega1.Basic

/-!
# Elementary arithmetic $\mathsf{I}\Delta_0 + \mathrm{Exp}$

$\mathsf{I}\Delta_0$ proves the inductive properties of the $\Delta_0$-definable graph of
exponentiation wherever its values exist, but not that they always do. Adjoining the single
sentence saying that they do gives elementary arithmetic, which lies between
$\mathsf{I}\Delta_0 + \Omega_1$ and $\mathsf{I}\Sigma_1$.

## References

- [HP98, §V.1]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

def expAxiom : ArithmeticSentence := “∀ x, ∃ y, !exponentialDef x y”

abbrev ElementaryArithmetic : ArithmeticTheory := 𝗜𝚺₀ ∪ {expAxiom}

notation "𝗘𝗔" => ElementaryArithmetic

lemma expAxiom_mem_ElementaryArithmetic : expAxiom ∈ 𝗘𝗔 := Set.mem_union_right _ rfl

noncomputable section

variable {V : Type*} [ORingStructure V]

lemma models_expAxiom_iff [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] :
    V↓[ℒₒᵣ] ⊧ expAxiom ↔ ∀ x : V, ∃ y, Exponential x y := by simp [models_iff, expAxiom]

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : V↓[ℒₒᵣ] ⊧* 𝗘𝗔 :=
  Semantics.ModelsSet.union_iff.mpr
    ⟨inferInstance, Semantics.ModelsSet.singleton_iff.mpr <|
      models_expAxiom_iff.mpr Exponential.range_exists⟩

namespace ElementaryArithmetic

variable [V↓[ℒₒᵣ] ⊧* 𝗘𝗔]

instance : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := ModelsTheory.of_add_left V 𝗜𝚺₀ {expAxiom}

lemma exponential_total (x : V) : ∃ y, Exponential x y :=
  models_expAxiom_iff.mp (Theory.models _ _ expAxiom_mem_ElementaryArithmetic) x

lemma exponential_exists_unique (x : V) : ∃! y, Exponential x y := by
  obtain ⟨y, h⟩ := exponential_total x;
  exact ExistsUnique.intro y h fun _ h' ↦ h'.uniq h;

lemma models_omega1 : V↓[ℒₒᵣ] ⊧ Omega1.omega1 :=
  models_Omega1_iff.mpr fun x ↦ exponential_total (‖x‖ ^ 2)

lemma models_ISigma0_union_Omega1 : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ 𝝮₁ :=
  Semantics.ModelsSet.union_iff.mpr ⟨inferInstance, ⟨by rintro _ ⟨⟩; exact models_omega1⟩⟩

end ElementaryArithmetic

end

instance : 𝗜𝚺₀ ⪯ 𝗘𝗔 := inferInstance

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗘𝗔 :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) inferInstance

instance : 𝗜𝚺₀ ∪ 𝝮₁ ⪯ 𝗘𝗔 :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ ElementaryArithmetic.models_ISigma0_union_Omega1

instance : 𝗘𝗔 ⪯ 𝗜𝚺₁ := weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

instance : ℕ↓[ℒₒᵣ] ⊧* 𝗘𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
