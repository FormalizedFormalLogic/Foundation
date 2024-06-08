import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

namespace Arith

def succInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “!p 0 → (∀ x, !p x → !p (x + 1)) → ∀ x, !p x”

def orderInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !p y) → !p x) → ∀ x, !p x”

def leastNumber {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !p x) → ∃ z, !p z ∧ ∀ x < z, ¬!p x”

def succIndᵤ (p : Semiformula L ξ 1) : Sentence L := ∀ᶠ* succInd p

variable (L)

namespace Theory

inductive peanoMinus : Theory ℒₒᵣ
  | addZero       : peanoMinus “∀ x, x + 0 = #0”
  | addAssoc      : peanoMinus “∀ x y z, (x + y) + z = x + (y + z)”
  | addComm       : peanoMinus “∀ x y, x + y = y + x”
  | addEqOfLt     : peanoMinus “∀ x y, x < y → ∃ z, x + z = y”
  | zeroLe        : peanoMinus “∀ x, 0 ≤ x”
  | zeroLtOne     : peanoMinus “0 < 1”
  | oneLeOfZeroLt : peanoMinus “∀ x, 0 < x → 1 ≤ x”
  | addLtAdd      : peanoMinus “∀ x y z, x < y → x + z < y + z”
  | mulZero       : peanoMinus “∀ x, x * 0 = 0”
  | mulOne        : peanoMinus “∀ x, x * 1 = #0”
  | mulAssoc      : peanoMinus “∀ x y z, (x * y) * z = x * (y * z)”
  | mulComm       : peanoMinus “∀ x y, x * y = y * x”
  | mulLtMul      : peanoMinus “∀ x y z, x < y ∧ 0 < z → x * z < y * z”
  | distr         : peanoMinus “∀ x y z, x * (y + z) = x * y + x * z”
  | ltIrrefl      : peanoMinus “∀ x, x ≮ x”
  | ltTrans       : peanoMinus “∀ x y z, x < y ∧ y < z → x < z”
  | ltTri         : peanoMinus “∀ x y, x < y ∨ x = y ∨ x > y”

notation "𝐏𝐀⁻" => peanoMinus

def indScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { q | ∃ p : Semiformula L ℕ 1, Γ p ∧ q = ∀ᶠ* succInd p }

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

abbrev peano : Theory ℒₒᵣ := 𝐏𝐀⁻ + indScheme ℒₒᵣ Set.univ

notation "𝐏𝐀" => peano

variable {L}

lemma coe_indH_subset_indH : (indScheme ℒₒᵣ (Arith.Hierarchy Γ ν) : Theory L) ⊆ indScheme L (Arith.Hierarchy Γ ν) := by
  simp [Theory.indH, Theory.indScheme]
  rintro _ p Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) p, Hierarchy.oringEmb Hp,
    by simp [Formula.lMap_fvUnivClosure, succInd, Semiformula.lMap_substs]⟩

instance : 𝐏𝐀⁻ ≼ 𝐈𝐍𝐃Γ ν := System.Subtheory.ofSubset (by simp [indH, Theory.add_def])

end Theory

end Arith

end FirstOrder
