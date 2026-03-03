module

public import Foundation.FirstOrder.Arithmetic.Basic

@[expose] public section
namespace LO.FirstOrder.Arithmetic

abbrev FirstOrderTrueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

notation "𝗧𝗔" => FirstOrderTrueArith

namespace TA

instance : ℕ ⊧ₘ* 𝗧𝗔 :=
  modelsTheory_iff.mpr fun {φ} ↦ by simp

lemma provable_iff {φ : ArithmeticSentence} :
    𝗧𝗔 ⊢ φ ↔ ℕ ⊧ₘ φ :=
  ⟨fun h ↦ consequence_iff'.mp (smallSound! h) ℕ, fun h ↦ Entailment.by_axm _ h⟩

instance (T : Theory ℒₒᵣ) [ℕ ⊧ₘ* T] : T ⪯ 𝗧𝗔 := ⟨by
  rintro φ h
  have : ℕ ⊧ₘ φ := consequence_iff'.mp (smallSound! h) ℕ
  exact provable_iff.mpr this⟩

end TA

end LO.FirstOrder.Arithmetic
