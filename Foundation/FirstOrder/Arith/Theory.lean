import Foundation.FirstOrder.Arith.Basic

namespace LO

namespace FirstOrder

open Arith

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

namespace Theory

variable (L)

inductive R0 : Theory ℒₒᵣ
  | equal : ∀ φ ∈ 𝐄𝐐, R0 φ
  | Ω₁ (n m : ℕ)  : R0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ)  : R0 “↑n * ↑m = ↑(n * m)”
  | Ω₃  (n m : ℕ)  : n ≠ m → R0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝐑₀" => R0

variable {L}

abbrev       Arith.addZero : SyntacticFormula L := “x | x + 0 = x”
abbrev      Arith.addAssoc : SyntacticFormula L := “x y z | (x + y) + z = x + (y + z)”
abbrev       Arith.addComm : SyntacticFormula L := “x y | x + y = y + x”
abbrev     Arith.addEqOfLt : SyntacticFormula L := “x y | x < y → ∃ z, x + z = y”
abbrev        Arith.zeroLe : SyntacticFormula L := “x | 0 ≤ x”
abbrev     Arith.zeroLtOne : SyntacticFormula L := “0 < 1”
abbrev Arith.oneLeOfZeroLt : SyntacticFormula L := “x | 0 < x → 1 ≤ x”
abbrev      Arith.addLtAdd : SyntacticFormula L := “x y z | x < y → x + z < y + z”
abbrev       Arith.mulZero : SyntacticFormula L := “x | x * 0 = 0”
abbrev        Arith.mulOne : SyntacticFormula L := “x | x * 1 = x”
abbrev      Arith.mulAssoc : SyntacticFormula L := “x y z | (x * y) * z = x * (y * z)”
abbrev       Arith.mulComm : SyntacticFormula L := “x y | x * y = y * x”
abbrev      Arith.mulLtMul : SyntacticFormula L := “x y z | x < y ∧ 0 < z → x * z < y * z”
abbrev         Arith.distr : SyntacticFormula L := “x y z | x * (y + z) = x * y + x * z”
abbrev      Arith.ltIrrefl : SyntacticFormula L := “x | x ≮ x”
abbrev       Arith.ltTrans : SyntacticFormula L := “x y z | x < y ∧ y < z → x < z”
abbrev         Arith.ltTri : SyntacticFormula L := “x y | x < y ∨ x = y ∨ x > y”

inductive PeanoMinus : Theory ℒₒᵣ
  | equal         : ∀ φ ∈ 𝐄𝐐, PeanoMinus φ
  | addZero       : PeanoMinus Arith.addZero
  | addAssoc      : PeanoMinus Arith.addAssoc
  | addComm       : PeanoMinus Arith.addComm
  | addEqOfLt     : PeanoMinus Arith.addEqOfLt
  | zeroLe        : PeanoMinus Arith.zeroLe
  | zeroLtOne     : PeanoMinus Arith.zeroLtOne
  | oneLeOfZeroLt : PeanoMinus Arith.oneLeOfZeroLt
  | addLtAdd      : PeanoMinus Arith.addLtAdd
  | mulZero       : PeanoMinus Arith.mulZero
  | mulOne        : PeanoMinus Arith.mulOne
  | mulAssoc      : PeanoMinus Arith.mulAssoc
  | mulComm       : PeanoMinus Arith.mulComm
  | mulLtMul      : PeanoMinus Arith.mulLtMul
  | distr         : PeanoMinus Arith.distr
  | ltIrrefl      : PeanoMinus Arith.ltIrrefl
  | ltTrans       : PeanoMinus Arith.ltTrans
  | ltTri         : PeanoMinus Arith.ltTri

notation "𝐏𝐀⁻" => PeanoMinus

variable (L)

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

lemma indScheme_subset (h : ∀ {φ : Semiformula ℒₒᵣ ℕ 1},  C φ → C' φ) : indScheme ℒₒᵣ C ⊆ indScheme ℒₒᵣ C' := by
  intro _; simp [indScheme]; rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma iSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⊆ 𝐈𝚺 s₂ :=
  Set.union_subset_union_right _ (indScheme_subset (fun H ↦ H.mono h))

instance : 𝐏𝐀⁻ ⪯ 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.ofSubset (by simp [indH, Theory.add_def])



instance : 𝐄𝐐 ⪯ 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance : 𝐄𝐐 ⪯ 𝐈open := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance (i) : 𝐈open ⪯ 𝐈𝚺i :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| indScheme_subset Hierarchy.of_open

lemma iSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⪯ 𝐈𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (iSigma_subset_mono h)

instance : 𝐈𝚺₀ ⪯ 𝐈𝚺₁ :=
  iSigma_weakerThan_of_le (by decide)

instance (i) : 𝐈𝚺i ⪯ 𝐏𝐀 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| indScheme_subset (by intros; trivial)

example (a b : ℕ) : Set.Finite {a, b} := by simp only [Set.finite_singleton, Set.Finite.insert]

@[simp] lemma PeanoMinus.finite : Set.Finite 𝐏𝐀⁻ := by
  have : 𝐏𝐀⁻ =
    𝐄𝐐 ∪
    { Arith.addZero,
      Arith.addAssoc,
      Arith.addComm,
      Arith.addEqOfLt,
      Arith.zeroLe,
      Arith.zeroLtOne,
      Arith.oneLeOfZeroLt,
      Arith.addLtAdd,
      Arith.mulZero,
      Arith.mulOne,
      Arith.mulAssoc,
      Arith.mulComm,
      Arith.mulLtMul,
      Arith.distr,
      Arith.ltIrrefl,
      Arith.ltTrans,
      Arith.ltTri } := by
    ext φ; constructor
    · rintro ⟨⟩
      case equal => left; assumption
      case addZero => tauto
      case addAssoc => tauto
      case addComm => tauto
      case addEqOfLt => tauto
      case zeroLe => tauto
      case zeroLtOne => tauto
      case oneLeOfZeroLt => tauto
      case addLtAdd => tauto
      case mulZero => tauto
      case mulOne => tauto
      case mulAssoc => tauto
      case mulComm => tauto
      case mulLtMul => tauto
      case distr => tauto
      case ltIrrefl => tauto
      case ltTrans => tauto
      case ltTri => tauto
    · rintro (h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact equal _ h
      · exact addZero
      · exact addAssoc
      · exact addComm
      · exact addEqOfLt
      · exact zeroLe
      · exact zeroLtOne
      · exact oneLeOfZeroLt
      · exact addLtAdd
      · exact mulZero
      · exact mulOne
      · exact mulAssoc
      · exact mulComm
      · exact mulLtMul
      · exact distr
      · exact ltIrrefl
      · exact ltTrans
      · exact ltTri
  rw [this]; simp only [Set.finite_union, EqAxiom.finite, true_and]
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.finite_singleton

end Theory

end FirstOrder
