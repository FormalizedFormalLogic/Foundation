module

public import Foundation.FirstOrder.Arithmetic.Basic

@[expose] public section
namespace LO.FirstOrder.Arithmetic

abbrev FirstOrderTrueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

notation "𝗧𝗔" => FirstOrderTrueArith

namespace TA

instance : ℕ↓[ℒₒᵣ] ⊧* 𝗧𝗔 :=
  models_theory_iff.mpr fun {φ} ↦ by simp

lemma provable_iff {φ : ArithmeticSentence} :
    𝗧𝗔 ⊢ φ ↔ ℕ↓[ℒₒᵣ] ⊧ φ :=
  ⟨fun h ↦ consequence_iff'.mp (Theory.Proof.sound h) ℕ, fun h ↦ Entailment.by_axm h⟩

instance (T : Theory ℒₒᵣ) [ℕ↓[ℒₒᵣ] ⊧* T] : T ⪯ 𝗧𝗔 := ⟨by
  rintro φ h
  have : ℕ↓[ℒₒᵣ] ⊧ φ := consequence_iff'.mp (Theory.Proof.sound h) ℕ
  exact provable_iff.mpr this⟩

end TA

end LO.FirstOrder.Arithmetic
