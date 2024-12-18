import Foundation.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

open Arith

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

namespace Theory

variable (L)

inductive CobhamR0 : Theory ℒₒᵣ
  | equal : ∀ φ ∈ 𝐄𝐐, CobhamR0 φ
  | Ω₁ (n m : ℕ)  : CobhamR0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : CobhamR0 “↑n * ↑m = ↑(n * m)”
  | Ω₃  (n m : ℕ)  : n ≠ m → CobhamR0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : CobhamR0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝐑₀" => CobhamR0

inductive PAMinus : Theory ℒₒᵣ
  | equal         : ∀ φ ∈ 𝐄𝐐, PAMinus φ
  | addZero       : PAMinus “x | x + 0 = x”
  | addAssoc      : PAMinus “x y z | (x + y) + z = x + (y + z)”
  | addComm       : PAMinus “x y | x + y = y + x”
  | addEqOfLt     : PAMinus “x y | x < y → ∃ z, x + z = y”
  | zeroLe        : PAMinus “x | 0 ≤ x”
  | zeroLtOne     : PAMinus “0 < 1”
  | oneLeOfZeroLt : PAMinus “x | 0 < x → 1 ≤ x”
  | addLtAdd      : PAMinus “x y z | x < y → x + z < y + z”
  | mulZero       : PAMinus “x | x * 0 = 0”
  | mulOne        : PAMinus “x | x * 1 = x”
  | mulAssoc      : PAMinus “x y z | (x * y) * z = x * (y * z)”
  | mulComm       : PAMinus “x y | x * y = y * x”
  | mulLtMul      : PAMinus “x y z | x < y ∧ 0 < z → x * z < y * z”
  | distr         : PAMinus “x y z | x * (y + z) = x * y + x * z”
  | ltIrrefl      : PAMinus “x | x ≮ x”
  | ltTrans       : PAMinus “x y z | x < y ∧ y < z → x < z”
  | ltTri         : PAMinus “x y | x < y ∨ x = y ∨ x > y”

notation "𝐏𝐀⁻" => PAMinus

def indScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = succInd φ }

abbrev iOpen : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Semiformula.Open

notation "𝐈open" => iOpen

abbrev indH (Γ : Polarity) (k : ℕ) : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ (Arith.Hierarchy Γ k)

prefix:max "𝐈𝐍𝐃" => indH

abbrev iSigma (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃𝚺 k

prefix:max "𝐈𝚺" => iSigma

notation "𝐈𝚺₀" => iSigma 0

abbrev iPi (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃𝚷 k

prefix:max "𝐈𝚷" => iPi

notation "𝐈𝚷₀" => iPi 0

notation "𝐈𝚺₁" => iSigma 1

notation "𝐈𝚷₁" => iPi 1

abbrev peano : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ

notation "𝐏𝐀" => peano

variable {L}

lemma coe_indH_subset_indH : (indScheme ℒₒᵣ (Arith.Hierarchy Γ ν) : Theory L) ⊆ indScheme L (Arith.Hierarchy Γ ν) := by
  simp only [indScheme, Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf, forall_exists_index, and_imp]
  rintro _ φ Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) φ, Hierarchy.oringEmb Hp,
    by simp [succInd, Semiformula.lMap_substs]⟩

instance PAMinus.subtheoryOfIndH : 𝐏𝐀⁻ ≼ 𝐈𝐍𝐃Γ n := System.Subtheory.ofSubset (by simp [indH, Theory.add_def])

instance EQ.subtheoryOfCobhamR0 : 𝐄𝐐 ≼ 𝐑₀ := System.Subtheory.ofSubset <| fun φ hp ↦ CobhamR0.equal φ hp

instance EQ.subtheoryOfPAMinus : 𝐄𝐐 ≼ 𝐏𝐀⁻ := System.Subtheory.ofSubset <| fun φ hp ↦ PAMinus.equal φ hp

instance EQ.subtheoryOfIndH : 𝐄𝐐 ≼ 𝐈𝐍𝐃Γ n := System.Subtheory.comp PAMinus.subtheoryOfIndH EQ.subtheoryOfPAMinus

instance EQ.subtheoryOfIOpen : 𝐄𝐐 ≼ 𝐈open := System.Subtheory.comp inferInstance EQ.subtheoryOfPAMinus

end Theory

end FirstOrder
