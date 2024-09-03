import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

open Arith

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def succInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “!p 0 → (∀ x, !p x → !p (x + 1)) → ∀ x, !p x”

def orderInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !p y) → !p x) → ∀ x, !p x”

def leastNumber {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !p x) → ∃ z, !p z ∧ ∀ x < z, ¬!p x”

namespace Theory

variable (L)

inductive CobhamR0 : Theory ℒₒᵣ
  | equal : ∀ p ∈ 𝐄𝐐, CobhamR0 p
  | Ω₁ (n m : ℕ)  : CobhamR0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : CobhamR0 “↑n * ↑m = ↑(n * m)”
  | Ω₃  (n m : ℕ)  : n ≠ m → CobhamR0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : CobhamR0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝐑₀" => CobhamR0

inductive PAMinus : Theory ℒₒᵣ
  | equal         : ∀ p ∈ 𝐄𝐐, PAMinus p
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
  { q | ∃ p : Semiformula L ℕ 1, Γ p ∧ q = succInd p }

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
  simp [Theory.indH, Theory.indScheme]
  rintro _ p Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) p, Hierarchy.oringEmb Hp,
    by simp [Formula.lMap_fvUnivClosure, succInd, Semiformula.lMap_substs]⟩

instance PAMinus.subtheoryOfIndH : 𝐏𝐀⁻ ≼ 𝐈𝐍𝐃Γ n := System.Subtheory.ofSubset (by simp [indH, Theory.add_def])

instance EQ.subtheoryOfCobhamR0 : 𝐄𝐐 ≼ 𝐑₀ := System.Subtheory.ofSubset <| fun p hp ↦ CobhamR0.equal p hp

instance EQ.subtheoryOfPAMinus : 𝐄𝐐 ≼ 𝐏𝐀⁻ := System.Subtheory.ofSubset <| fun p hp ↦ PAMinus.equal p hp

instance EQ.subtheoryOfIndH : 𝐄𝐐 ≼ 𝐈𝐍𝐃Γ n := System.Subtheory.comp PAMinus.subtheoryOfIndH EQ.subtheoryOfPAMinus

instance EQ.subtheoryOfIOpen : 𝐄𝐐 ≼ 𝐈open := System.Subtheory.comp inferInstance EQ.subtheoryOfPAMinus

end Theory

end FirstOrder
