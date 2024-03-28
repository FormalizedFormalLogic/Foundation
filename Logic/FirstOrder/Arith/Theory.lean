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

inductive PAminus : Theory ℒₒᵣ
  | addZero       : PAminus “∀ #0 + 0 = #0”
  | addAssoc      : PAminus “∀ ∀ ∀ (#2 + #1) + #0 = #2 + (#1 + #0)”
  | addComm       : PAminus “∀ ∀ #1 + #0 = #0 + #1”
  | addEqOfLt     : PAminus “∀ ∀ (#1 < #0 → ∃ #2 + #0 = #1)”
  | zeroLe        : PAminus “∀ (0 ≤ #0)”
  | zeroLtOne     : PAminus “0 < 1”
  | oneLeOfZeroLt : PAminus “∀ (0 < #0 → 1 ≤ #0)”
  | addLtAdd      : PAminus “∀ ∀ ∀ (#2 < #1 → #2 + #0 < #1 + #0)”
  | mulZero       : PAminus “∀ #0 * 0 = 0”
  | mulOne        : PAminus “∀ #0 * 1 = #0”
  | mulAssoc      : PAminus “∀ ∀ ∀ (#2 * #1) * #0 = #2 * (#1 * #0)”
  | mulComm       : PAminus “∀ ∀ #1 * #0 = #0 * #1”
  | mulLtMul      : PAminus “∀ ∀ ∀ (#2 < #1 ∧ 0 < #0 → #2 * #0 < #1 * #0)”
  | distr         : PAminus “∀ ∀ ∀ #2 * (#1 + #0) = #2 * #1 + #2 * #0”
  | ltIrrefl      : PAminus “∀ ¬#0 < #0”
  | ltTrans       : PAminus “∀ ∀ ∀ (#2 < #1 ∧ #1 < #0 → #2 < #0)”
  | ltTri         : PAminus “∀ ∀ (#1 < #0 ∨ #1 = #0 ∨ #0 < #1)”

notation "𝐏𝐀⁻" => PAminus

variable {L}

def IndScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { q | ∃ p : Semiformula L ℕ 1, Γ p ∧ q = ∀ᶠ* succInd p }

variable (L)

abbrev IOpen : Theory L := IndScheme Semiformula.Open

notation "𝐈open" => IOpen ℒₒᵣ

abbrev IHierarchy (Γ : Polarity) (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Γ k)

notation "𝐈𝐍𝐃" => IHierarchy ℒₒᵣ

abbrev ISigma (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Σ k)

prefix:max "𝐈𝚺" => ISigma ℒₒᵣ

notation "𝐈𝚺₀" => ISigma ℒₒᵣ 0

abbrev IPi (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Π k)

prefix:max "𝐈𝚷" => IPi ℒₒᵣ

notation "𝐈𝚷₀" => IPi ℒₒᵣ 0

abbrev Peano : Theory L := IndScheme Set.univ

notation "𝐏𝐀" => Peano ℒₒᵣ

variable {L}

lemma coe_IHierarchy_subset_IHierarchy : (𝐈𝐍𝐃 Γ ν : Theory L) ⊆ IHierarchy L Γ ν := by
  simp [Theory.IHierarchy, Theory.IndScheme]
  rintro _ p Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) p, Hierarchy.oringEmb Hp,
    by simp [Formula.lMap_fvUnivClosure, succInd, Semiformula.lMap_substs]⟩

end Theory

end Arith

end FirstOrder
