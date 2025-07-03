import Foundation.FirstOrder.Arith.Basic

namespace LO

open FirstOrder Arith

abbrev FirstOrderTrueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

notation "𝐓𝐀" => FirstOrderTrueArith

namespace FirstOrderTrueArith

instance : ℕ ⊧ₘ* 𝐓𝐀 :=
  modelsTheory_iff.mpr fun {φ} ↦ by simp

lemma provable_iff {φ : SyntacticFormula ℒₒᵣ} :
    𝐓𝐀 ⊢! φ ↔ ℕ ⊧ₘ φ :=
  ⟨fun h ↦ consequence_iff'.mp (sound₀! h) ℕ, fun h ↦ Entailment.by_axm _ h⟩

instance (T : Theory ℒₒᵣ) [ℕ ⊧ₘ* T] : T ⪯ 𝐓𝐀 := ⟨by
  rintro φ h
  have : ℕ ⊧ₘ φ := consequence_iff'.mp (sound₀! h) ℕ
  exact provable_iff.mpr this⟩

end LO.FirstOrderTrueArith
