import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

namespace Arith

def succInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “!p [0] → ∀ (!p [#0] → !p [#0 + 1]) → ∀ !p [#0]”

def orderInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “∀ (∀[#0 < #1] !p [#0] → !p [#0]) → ∀ !p [#0]”

def leastNumber {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “∃ !p [#0] → ∃ (!p [#0] ∧ ∀[#0 < #1] ¬!p [#0])”

def succIndᵤ (p : Semiformula L ξ 1) : Sentence L := ∀ᶠ* succInd p

variable (L)

namespace Theory

inductive peanoMinus : Theory ℒₒᵣ
  | addZero       : peanoMinus “∀ #0 + 0 = #0”
  | addAssoc      : peanoMinus “∀ ∀ ∀ (#2 + #1) + #0 = #2 + (#1 + #0)”
  | addComm       : peanoMinus “∀ ∀ #1 + #0 = #0 + #1”
  | addEqOfLt     : peanoMinus “∀ ∀ (#1 < #0 → ∃ #2 + #0 = #1)”
  | zeroLe        : peanoMinus “∀ (0 ≤ #0)”
  | zeroLtOne     : peanoMinus “0 < 1”
  | oneLeOfZeroLt : peanoMinus “∀ (0 < #0 → 1 ≤ #0)”
  | addLtAdd      : peanoMinus “∀ ∀ ∀ (#2 < #1 → #2 + #0 < #1 + #0)”
  | mulZero       : peanoMinus “∀ #0 * 0 = 0”
  | mulOne        : peanoMinus “∀ #0 * 1 = #0”
  | mulAssoc      : peanoMinus “∀ ∀ ∀ (#2 * #1) * #0 = #2 * (#1 * #0)”
  | mulComm       : peanoMinus “∀ ∀ #1 * #0 = #0 * #1”
  | mulLtMul      : peanoMinus “∀ ∀ ∀ (#2 < #1 ∧ 0 < #0 → #2 * #0 < #1 * #0)”
  | distr         : peanoMinus “∀ ∀ ∀ #2 * (#1 + #0) = #2 * #1 + #2 * #0”
  | ltIrrefl      : peanoMinus “∀ ¬#0 < #0”
  | ltTrans       : peanoMinus “∀ ∀ ∀ (#2 < #1 ∧ #1 < #0 → #2 < #0)”
  | ltTri         : peanoMinus “∀ ∀ (#1 < #0 ∨ #1 = #0 ∨ #0 < #1)”

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
