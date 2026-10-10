module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Foundation.FirstOrder.Arithmetic.TA.Basic

/-!
# Induction and least number schemata of Arithmetic

The plain schemata are taken over prenex formulas `ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s`, the `⁺` ones
over the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy Γ s`.

## References

- [HP98, §I.2(a), I.2.3]
- [Bus98, p. 85]
-/

@[expose] public section
set_option autoImplicit true

namespace FFL.FirstOrder.Arithmetic

open Bounding (HierarchySymbol)
open scoped FFL.FirstOrder.Arithmetic

variable {Γ : Polarity} {i k m n : ℕ}

section axioms

/-! ### Axiom formulas -/

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

def collectionAxiom {ξ} (φ : Semiformula L ξ 2) : Formula L ξ :=
  “∀ a, (∀ x < a, ∃ y, !φ x y) → ∃ b, ∀ x < a, ∃ y < b, !φ x y”

/-! ### Induction schemata -/

variable (L)

def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ) }

abbrev IOpen : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Semiformula.Open

notation "𝗜𝗢𝗽𝗲𝗻" => IOpen

abbrev InductionOnPrenexHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)

prefix:max "𝗜𝗡𝗗 " => InductionOnPrenexHierarchy

abbrev ISigma (s : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚺 s

prefix:max "𝗜𝚺" => ISigma

notation "𝗜𝚺₀" => ISigma 0

notation "𝗜𝚺₁" => ISigma 1

abbrev IPi (s : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚷 s

prefix:max "𝗜𝚷" => IPi

notation "𝗜𝚷₀" => IPi 0

notation "𝗜𝚷₁" => IPi 1

/-- The induction scheme for the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy Γ s`, i.e. Buss's `IΓ_s⁺`. -/
abbrev InductionOnHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s)

prefix:max "𝗜𝗡𝗗⁺ " => InductionOnHierarchy

abbrev IBroadSigma (s : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗⁺ 𝚺 s

prefix:max "𝗜𝚺⁺" => IBroadSigma

notation "𝗜𝚺⁺₀" => IBroadSigma 0

notation "𝗜𝚺⁺₁" => IBroadSigma 1

abbrev IBroadPi (s : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗⁺ 𝚷 s

prefix:max "𝗜𝚷⁺" => IBroadPi

notation "𝗜𝚷⁺₀" => IBroadPi 0

notation "𝗜𝚷⁺₁" => IBroadPi 1

abbrev Peano : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Set.univ

notation "𝗣𝗔" => Peano

variable {L}

/-! ### Least number schemata -/

def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ) }

abbrev LeastNumberOnPrenexHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)

prefix:max "𝗟 " => LeastNumberOnPrenexHierarchy

abbrev LSigma (s : ℕ) : ArithmeticTheory := 𝗟 𝚺 s

prefix:max "𝗟𝚺" => LSigma

abbrev LPi (s : ℕ) : ArithmeticTheory := 𝗟 𝚷 s

prefix:max "𝗟𝚷" => LPi

/-- The least number scheme for the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy Γ s`. -/
abbrev LeastNumberOnHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (ℬ[<, ℒₒᵣ].Hierarchy Γ s)

prefix:max "𝗟⁺ " => LeastNumberOnHierarchy

abbrev LBroadSigma (s : ℕ) : ArithmeticTheory := 𝗟⁺ 𝚺 s

prefix:max "𝗟𝚺⁺" => LBroadSigma

abbrev LBroadPi (s : ℕ) : ArithmeticTheory := 𝗟⁺ 𝚷 s

prefix:max "𝗟𝚷⁺" => LBroadPi

/-! ### Collection schemata -/

def CollectionScheme (Γ : Set (ArithmeticSemiformula ℕ 2)) : Set ArithmeticSentence :=
  (fun φ => .univCl (collectionAxiom φ)) '' Γ

abbrev CollectionOnPrenexHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ CollectionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s)

prefix:max "𝗕 " => CollectionOnPrenexHierarchy

abbrev BSigma (s : ℕ) : ArithmeticTheory := 𝗕 𝚺 s

prefix:max "𝗕𝚺" => BSigma

notation "𝗕𝚺₁" => BSigma 1

abbrev BPi (s : ℕ) : ArithmeticTheory := 𝗕 𝚷 s

prefix:max "𝗕𝚷" => BPi

/-- The collection scheme for the broad hierarchy `ℬ[<, ℒₒᵣ].Hierarchy Γ s`, i.e. Buss's `BΓ_s⁺`. -/
abbrev CollectionOnHierarchy (Γ : Polarity) (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ CollectionScheme (ℬ[<, ℒₒᵣ].Hierarchy Γ s)

prefix:max "𝗕⁺ " => CollectionOnHierarchy

/-! ### Induction scheme lemmas -/

section

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma InductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_ofPred_eq, forall_exists_index, and_imp]
  rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma mem_InductionScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ C := by
  simpa [InductionScheme] using ⟨φ, hp, rfl⟩

lemma mem_IOpen_of_qfree {φ : ArithmeticSemiformula ℕ 1} (hp : φ.Open) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ Semiformula.Open := by
  exact ⟨φ, hp, rfl⟩

lemma IBroadSigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺⁺ s₁ ⊆ 𝗜𝚺⁺ s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma IBroadSigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺⁺ s₁ ⪯ 𝗜𝚺⁺ s₂ :=
  Entailment.WeakerThan.ofSubset (IBroadSigma_subset_mono h)

lemma IBroadSigma_weakerThan_of_le_trans {T : ArithmeticTheory} {s₁ s₂} (h : s₁ ≤ s₂)
    (hT : 𝗜𝚺⁺s₂ ⪯ T) :
    𝗜𝚺⁺ s₁ ⪯ T :=
  Entailment.WeakerThan.trans (IBroadSigma_weakerThan_of_le h) hT

lemma InductionOnPrenexHierarchy_subset_InductionOnHierarchy {Γ : Polarity} {s : ℕ} :
    𝗜𝗡𝗗 Γ s ⊆ 𝗜𝗡𝗗⁺ Γ s :=
  Set.union_subset_union_right _ (InductionScheme_subset (·.hierarchy))

lemma InductionOnPrenexHierarchy_zero_eq_InductionOnHierarchy_zero (Γ Γ' : Polarity) :
    𝗜𝗡𝗗 Γ 0 = 𝗜𝗡𝗗⁺ Γ' 0 :=
  Set.Subset.antisymm
    (Set.union_subset_union_right _
      (InductionScheme_subset fun H ↦ (Bounding.PrenexHierarchy.zero_iff.mp H).of_zero))
    (Set.union_subset_union_right _
      (InductionScheme_subset fun H ↦ Bounding.PrenexHierarchy.zero_iff.mpr H.of_zero))

lemma ISigmaZero_eq_IBroadSigmaZero : 𝗜𝚺₀ = 𝗜𝚺⁺₀ :=
  InductionOnPrenexHierarchy_zero_eq_InductionOnHierarchy_zero 𝚺 𝚺

lemma ISigmaZero_subset_IBroadSigma {s : ℕ} : 𝗜𝚺₀ ⊆ 𝗜𝚺⁺ s :=
  Set.union_subset_union_right _
    (InductionScheme_subset fun H ↦ (Bounding.PrenexHierarchy.zero_iff.mp H).of_zero)

lemma IBroadSigmaZero_subset_ISigmaZero : 𝗜𝚺⁺₀ ⊆ 𝗜𝚺₀ :=
  le_of_eq ISigmaZero_eq_IBroadSigmaZero.symm

end

/-! ### Least number scheme lemmas -/

section

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩;

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C := ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗟⁺ Γ s₁ ⊆ 𝗟⁺ Γ s₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗟⁺ Γ s₁ ⪯ 𝗟⁺ Γ s₂ :=
  Entailment.WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)

lemma LeastNumberOnPrenexHierarchy_subset_LeastNumberOnHierarchy {Γ : Polarity} {s : ℕ} :
    𝗟 Γ s ⊆ 𝗟⁺ Γ s :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (·.hierarchy))

end

/-! ### Collection scheme lemmas -/

section

variable {C C' : ArithmeticSemiformula ℕ 2 → Prop}

lemma CollectionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 2}, C φ → C' φ) :
    CollectionScheme C ⊆ CollectionScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩

lemma mem_CollectionScheme_of_mem {φ : ArithmeticSemiformula ℕ 2} (hφ : C φ) :
    .univCl (collectionAxiom φ) ∈ CollectionScheme C := ⟨φ, hφ, rfl⟩

variable {Γ : Polarity}

lemma CollectionOnPrenexHierarchy_subset_CollectionOnHierarchy {Γ : Polarity} {s : ℕ} :
    𝗕 Γ s ⊆ 𝗕⁺ Γ s :=
  Set.union_subset_union_right _ (CollectionScheme_subset (·.hierarchy))

end

/-! ### Relations between the theories -/

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗡𝗗 Γ s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗡𝗗⁺ Γ s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗢𝗽𝗲𝗻 :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝗡𝗗⁺ Γ s :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _ <|
    InductionScheme_subset Bounding.HierarchyOn.of_open

instance InductionOnPrenexHierarchy_weakerThan_InductionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜𝗡𝗗 Γ s ⪯ 𝗜𝗡𝗗⁺ Γ s :=
  Entailment.WeakerThan.ofSubset InductionOnPrenexHierarchy_subset_InductionOnHierarchy

instance : 𝗜𝚺⁺₀ ⪯ 𝗜𝚺⁺₁ := IBroadSigma_weakerThan_of_le (by decide)

instance : 𝗜𝚺₀ ⪯ 𝗜𝚺⁺ s :=
  Entailment.WeakerThan.ofSubset ISigmaZero_subset_IBroadSigma

instance : 𝗜𝚺₁ ⪯ 𝗜𝚺⁺₁ := InductionOnPrenexHierarchy_weakerThan_InductionOnHierarchy 𝚺 1

instance : 𝗜𝚺s ⪯ 𝗣𝗔 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _ <|
    InductionScheme_subset (by intros; trivial)

instance : 𝗜𝚺⁺s ⪯ 𝗣𝗔 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _ <|
    InductionScheme_subset (by intros; trivial)

instance : 𝗣𝗔⁻ ⪯ 𝗜𝗢𝗽𝗲𝗻 := inferInstance

instance : 𝗜𝚺₁ ⪯ 𝗣𝗔 := inferInstance

instance : 𝗜𝚺⁺₁ ⪯ 𝗣𝗔 := inferInstance

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔 :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟 Γ s :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟 Γ s :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance

instance (Γ : Polarity) (s : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟⁺ Γ s :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟⁺ Γ s :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance

instance LeastNumberOnPrenexHierarchy_weakerThan_LeastNumberOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗟 Γ s ⪯ 𝗟⁺ Γ s :=
  Entailment.WeakerThan.ofSubset LeastNumberOnPrenexHierarchy_subset_LeastNumberOnHierarchy

instance (Γ : Polarity) (s : ℕ) : 𝗜𝚺₀ ⪯ 𝗕 Γ s :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕 Γ s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance CollectionOnPrenexHierarchy_weakerThan_CollectionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗕 Γ s ⪯ 𝗕⁺ Γ s :=
  Entailment.WeakerThan.ofSubset CollectionOnPrenexHierarchy_subset_CollectionOnHierarchy

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `𝗘𝗤 ℒₒᵣ ⪯ T`, so instance search cannot infer it.
lemma eq_weakerThan_of_ISigma {T : ArithmeticTheory} {s : ℕ} [𝗜𝚺s ⪯ T] : 𝗘𝗤 ℒₒᵣ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺 s) ‹𝗜𝚺 s ⪯ T›

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `𝗘𝗤 ℒₒᵣ ⪯ T`, so instance search cannot infer it.
lemma eq_weakerThan_of_IBroadSigma {T : ArithmeticTheory} {s : ℕ} [𝗜𝚺⁺s ⪯ T] : 𝗘𝗤 ℒₒᵣ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺⁺₀)
    (IBroadSigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺⁺ s ⪯ T›)

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `𝗘𝗤 ℒₒᵣ ⪯ T`, so instance search cannot infer it.
lemma eq_weakerThan_of_BSigma {T : ArithmeticTheory} {s : ℕ} [𝗕𝚺s ⪯ T] : 𝗘𝗤 ℒₒᵣ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗕𝚺 s) ‹𝗕𝚺 s ⪯ T›

end axioms

section models

variable {V : Type*} [ORingStructure V]

namespace InductionScheme

variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ C]

private lemma induction_eval {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) (v : ℕ → V) :
    φ.Eval ![0] v →
    (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
    ∀ x, φ.Eval ![x] v := by
  have : V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) :=
    Theory.models (T := InductionScheme _ C) V (by simpa using mem_InductionScheme_of_mem hp)
  revert v
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this

@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end InductionScheme

namespace InductionOnPrenexHierarchy

/-! ### Induction over prenex formulas -/

variable (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s]

instance : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s := inferInstance
  models_of_subtheory this

@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1,
      ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s φ ∧ ∀ x, P x ↔ φ.Eval ![x] e)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s) hP zero succ

end InductionOnPrenexHierarchy

section

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma InductionScheme.models_of_exists_eval_iff [V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ C']
    (h : ∀ φ, C φ → ∃ ψ, C' ψ ∧
      ∀ (e : Fin 1 → V) (f : ℕ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ C := by
  apply Semantics.modelsSet_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  obtain ⟨ψ, hψ, H⟩ := h φ hφ;
  have : V↓[ℒₒᵣ] ⊧ .univCl (succInd ψ) :=
    Theory.models (T := InductionScheme _ C') V (mem_InductionScheme_of_mem hψ);
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs, H] using this;

lemma LeastNumberScheme.models_of_exists_eval_iff [V↓[ℒₒᵣ] ⊧* LeastNumberScheme C']
    (h : ∀ φ, C φ → ∃ ψ, C' ψ ∧
      ∀ (e : Fin 1 → V) (f : ℕ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    V↓[ℒₒᵣ] ⊧* LeastNumberScheme C := by
  apply Semantics.modelsSet_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  obtain ⟨ψ, hψ, H⟩ := h φ hφ;
  have : V↓[ℒₒᵣ] ⊧ .univCl (leastNumber ψ) :=
    Theory.models (T := LeastNumberScheme C') V (mem_LeastNumberScheme_of_mem hψ);
  simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs, H] using this;

end

lemma CollectionScheme.models_of_exists_eval_iff {C C' : ArithmeticSemiformula ℕ 2 → Prop}
    [V↓[ℒₒᵣ] ⊧* CollectionScheme C']
    (h : ∀ φ, C φ → ∃ ψ, C' ψ ∧
      ∀ (e : Fin 2 → V) (f : ℕ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    V↓[ℒₒᵣ] ⊧* CollectionScheme C := by
  apply Semantics.modelsSet_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  obtain ⟨ψ, hψ, H⟩ := h φ hφ;
  have : V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom ψ) :=
    Theory.models (T := CollectionScheme C') V (mem_CollectionScheme_of_mem hψ);
  simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs, H] using this;

/-! ### Monotonicity of the prenex schemata in models -/

section

variable {Γ Γ' : Polarity} {s s' : ℕ}

lemma models_InductionOnPrenexHierarchy_of_le (hs : s ≤ s') [h : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s'] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s :=
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    InductionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (hφ.exists_eval_iff_of_le hs).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_InductionOnPrenexHierarchy_of_lt (hs : s < s') [h : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ' s'] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s :=
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    InductionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (hφ.exists_eval_iff_of_lt Γ' hs).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_ISigmaZero_of_models_InductionOnPrenexHierarchy (V : Type*) [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [h : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    InductionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (Bounding.PrenexHierarchy.exists_eval_iff_of_deltaZero
        (Bounding.PrenexHierarchy.zero_iff.mp hφ) Γ s).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_IOpen_of_models_InductionOnPrenexHierarchy [h : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    InductionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (Bounding.PrenexHierarchy.exists_eval_iff_of_deltaZero (ℬ := ℬ[<, ℒₒᵣ])
        (Bounding.HierarchyOn.of_open hφ) Γ s).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_LeastNumberOnPrenexHierarchy_of_le (hs : s ≤ s') [h : V↓[ℒₒᵣ] ⊧* 𝗟 Γ s'] :
    V↓[ℒₒᵣ] ⊧* 𝗟 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* LeastNumberScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s') :=
    models_of_ss h Set.subset_union_right
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    LeastNumberScheme.models_of_exists_eval_iff fun _ hφ ↦
      (hφ.exists_eval_iff_of_le hs).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_CollectionOnPrenexHierarchy_of_le (hs : s ≤ s') [h : V↓[ℒₒᵣ] ⊧* 𝗕 Γ s'] :
    V↓[ℒₒᵣ] ⊧* 𝗕 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* CollectionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s') :=
    models_of_ss h Set.subset_union_right
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    CollectionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (hφ.exists_eval_iff_of_le hs).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

lemma models_CollectionOnPrenexHierarchy_of_lt (hs : s < s') [h : V↓[ℒₒᵣ] ⊧* 𝗕 Γ' s'] :
    V↓[ℒₒᵣ] ⊧* 𝗕 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* CollectionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy Γ' s') :=
    models_of_ss h Set.subset_union_right
  Semantics.ModelsSet.union_iff.mpr ⟨models_of_ss h Set.subset_union_left,
    CollectionScheme.models_of_exists_eval_iff fun _ hφ ↦
      (hφ.exists_eval_iff_of_lt Γ' hs).imp fun _ h ↦ ⟨h.1, h.2 V⟩⟩

end

lemma mod_ISigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺s₂] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s₁ :=
  models_InductionOnPrenexHierarchy_of_le h

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₀ :=
  models_of_ss inferInstance IBroadSigmaZero_subset_ISigmaZero

-- This is stated as a `lemma`, not an `instance`: together with the bridge above, instance search
-- would cycle between `V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀` and `V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₀`.
lemma mod_ISigma_of_IBroadSigma {s} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s :=
  models_of_ss inferInstance InductionOnPrenexHierarchy_subset_InductionOnHierarchy

namespace InductionOnHierarchy

/-! ### Induction over the broad hierarchy -/

section

variable (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s]

instance : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ s) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  models_of_subtheory this

lemma succ_induction {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  InductionScheme.succ_induction (P := P) (C := ℬ[<, ℒₒᵣ].Hierarchy Γ s) (by
    rcases hP with ⟨φ, hp⟩
    have : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using succ_induction
  · exact Γ
  · exact s
  · suffices Γᴬ_[s].DefinablePred fun x ↦ ∀ y < x, P y by exact this
    exact HierarchySymbol.Definable.arithmetic_ball_blt
      (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => infer_instance

private lemma neg_succ_induction {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using succ_induction
    · exact Γ
    · exact s
    · suffices Γᴬ_[s].DefinablePred fun x ↦ x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.arithmetic_bounded_comp₂
          (by definability) (by definability)
      · apply HierarchySymbol.Definable.arithmetic_bounded_comp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←Arithmetic.sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => infer_instance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

instance models_InductionScheme_alt :
    V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy Γ.alt s) := by
  suffices
      ∀ (φ : ArithmeticSemiformula ℕ 1), ℬ[<, ℒₒᵣ].Hierarchy Γ.alt s φ →
      ∀ (f : ℕ → V),
        φ.Eval ![0] f →
        (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
    simp only [InductionScheme]
    refine Semantics.ModelsSet.setOf_iff.mpr ?_
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_rew_q,
        Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
    using this φ hφ
  intro φ hp v
  simpa using
    neg_succ_induction Γ s (P := fun x ↦ ¬φ.Eval ![x] v)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
      (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))

instance models_alt : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ.alt s := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  simp only [InductionOnHierarchy, Semantics.ModelsSet.union_iff]
  constructor <;> infer_instance

lemma least_number {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using succ_induction
    · exact Γ.alt
    · exact s
    · suffices Γ.altᴬ_[s].DefinablePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Definable.arithmetic_ball_blt (by definability)
      apply HierarchySymbol.Definable.not
      apply HierarchySymbol.Definable.arithmetic_bounded_comp₁
        (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => infer_instance
  exact this (x + 1) x (by simp) h

end

section

variable (Γ : SigmaPiDelta) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚺 s]

lemma succ_induction_sigma {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => succ_induction 𝚺 s hP zero succ
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚷 s := models_alt 𝚺 s
    succ_induction 𝚷 s hP zero succ
  | 𝚫 => succ_induction 𝚺 s hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction 𝚺 s hP ind
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚷 s := models_alt 𝚺 s
    order_induction 𝚷 s hP ind
  | 𝚫 => order_induction 𝚺 s hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γᴬ_[s].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number 𝚺 s hP h
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚷 s := models_alt 𝚺 s
    least_number 𝚷 s hP h
  | 𝚫 => least_number 𝚺 s hP.of_delta h

end

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚺 s] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := by
  rcases Γ
  · infer_instance
  · exact models_alt 𝚺 s

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ 𝚷 s] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := by
  rcases Γ
  · exact models_alt 𝚷 s
  · infer_instance

lemma mod_IBroadSigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s₂] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s₁ :=
  models_of_ss inferInstance (IBroadSigma_subset_mono h)

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
  models_of_ss inferInstance (ISigmaZero_subset_IBroadSigma (s := 1))

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚷⁺s := inferInstance

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚷⁺s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := inferInstance

lemma models_IBroadSigma_iff_models_IBroadPi {s} : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s ↔ V↓[ℒₒᵣ] ⊧* 𝗜𝚷⁺ s :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance

end InductionOnHierarchy

@[elab_as_elim] lemma ISigma0.succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺ᴬ₀.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 0 hP zero succ

@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁]
    {P : V → Prop} (hP : 𝚺ᴬ₁.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 1 hP zero succ

@[elab_as_elim] lemma ISigma1.pi1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁]
    {P : V → Prop} (hP : 𝚷ᴬ₁.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚷 1 hP zero succ

@[elab_as_elim] lemma ISigma0.order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺ᴬ₀.DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 0 hP ind

@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁]
    {P : V → Prop} (hP : 𝚺ᴬ₁.DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 1 hP ind

@[elab_as_elim] lemma ISigma1.pi1_order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁]
    {P : V → Prop} (hP : 𝚷ᴬ₁.DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚷 1 hP ind

lemma ISigma0.least_number [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {P : V → Prop}
    (hP : 𝚺ᴬ₀.DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  InductionOnHierarchy.least_number 𝚺 0 hP h

@[elab_as_elim] lemma ISigma1.succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁] (Γ)
    {P : V → Prop} (hP : Γᴬ_[1].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction_sigma Γ 1 hP zero succ

@[elab_as_elim] lemma ISigma1.order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁] (Γ)
    {P : V → Prop} (hP : Γᴬ_[1].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP ind

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := inferInstance
  models_of_subtheory this

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_IOpen_of_models_InductionOnPrenexHierarchy (Γ := 𝚺) (s := 0)

instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

abbrev mod_IBroadSigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s₂] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s₁ :=
  models_of_ss inferInstance (IBroadSigma_subset_mono h)

abbrev mod_BSigma_of_le {s₁ s₂} (h : s₁ ≤ s₂) [V↓[ℒₒᵣ] ⊧* 𝗕𝚺s₂] : V↓[ℒₒᵣ] ⊧* 𝗕𝚺s₁ :=
  models_CollectionOnPrenexHierarchy_of_le h

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`, so instance search cannot infer it.
lemma mod_paMinus_of_ISigma {s} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺s] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (Nat.zero_le s)
  inferInstance

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`, so instance search cannot infer it.
lemma mod_paMinus_of_IBroadSigma {s} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₀ := mod_IBroadSigma_of_le (Nat.zero_le s)
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss inferInstance (ISigmaZero_subset_IBroadSigma (s := 0))
  inferInstance

instance [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := inferInstance
  models_of_subtheory this

instance [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := inferInstance
  models_of_subtheory this

end models

/-! ### Monotonicity of the prenex schemata -/

section

variable {Γ Γ' : Polarity} {s s' : ℕ}

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺 s₁ ⪯ 𝗜𝚺 s₂ :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ mod_ISigma_of_le h

lemma ISigma_weakerThan_of_le_trans {T : ArithmeticTheory} {s₁ s₂} (h : s₁ ≤ s₂) (hT : 𝗜𝚺s₂ ⪯ T) :
    𝗜𝚺 s₁ ⪯ T :=
  Entailment.WeakerThan.trans (ISigma_weakerThan_of_le h) hT

lemma InductionOnPrenexHierarchy_weakerThan_of_lt (h : s < s') : 𝗜𝗡𝗗 Γ s ⪯ 𝗜𝗡𝗗 Γ' s' :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_InductionOnPrenexHierarchy_of_lt (Γ' := Γ') h

lemma LeastNumberOnPrenexHierarchy_weakerThan_of_le (h : s ≤ s') : 𝗟 Γ s ⪯ 𝗟 Γ s' :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_LeastNumberOnPrenexHierarchy_of_le h

lemma CollectionOnPrenexHierarchy_weakerThan_of_le (h : s ≤ s') : 𝗕 Γ s ⪯ 𝗕 Γ s' :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_CollectionOnPrenexHierarchy_of_le h

lemma CollectionOnPrenexHierarchy_weakerThan_of_lt (h : s < s') : 𝗕 Γ s ⪯ 𝗕 Γ' s' :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_CollectionOnPrenexHierarchy_of_lt (Γ' := Γ') h

lemma CollectionOnPrenexHierarchy_zero_eq (Γ Γ' : Polarity) : 𝗕 Γ 0 = 𝗕 Γ' 0 := by
  have : ℬ[<, ℒₒᵣ].PrenexHierarchy (ξ := ℕ) (n := 2) Γ 0 = ℬ[<, ℒₒᵣ].PrenexHierarchy Γ' 0 :=
    funext fun _ ↦ propext <|
      Bounding.PrenexHierarchy.zero_iff_bounded.trans Bounding.PrenexHierarchy.zero_iff_bounded.symm
  simp [CollectionOnPrenexHierarchy, this]

lemma BSigmaZero_eq_BPiZero : 𝗕𝚺 0 = 𝗕𝚷 0 :=
  CollectionOnPrenexHierarchy_zero_eq 𝚺 𝚷

lemma CollectionOnPrenexHierarchy_weakerThan_BSigma_succ (Γ : Polarity) (s : ℕ) :
    𝗕 Γ s ⪯ 𝗕𝚺 (s + 1) :=
  CollectionOnPrenexHierarchy_weakerThan_of_lt (Nat.lt_succ_self s)

instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝗡𝗗 Γ s :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦
    models_IOpen_of_models_InductionOnPrenexHierarchy (Γ := Γ) (s := s)

instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₀ := inferInstance

instance : 𝗜𝚺₀ ⪯ 𝗜𝚺₁ := ISigma_weakerThan_of_le (by decide)

instance : 𝗜𝚺⁺₀ ⪯ 𝗜𝚺 s :=
  (Entailment.WeakerThan.ofSubset IBroadSigmaZero_subset_ISigmaZero).trans
    (ISigma_weakerThan_of_le (Nat.zero_le s))

instance ISigmaZero_equiv_IBroadSigmaZero : 𝗜𝚺₀ ≊ 𝗜𝚺⁺₀ :=
  Entailment.Equiv.antisymm ⟨inferInstance, inferInstance⟩

end

lemma models_succInd (φ : ArithmeticSemiformula ℕ 1) : ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := by
  suffices
    ∀ f : ℕ → ℕ,
    φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f by
    simpa [Semiformula.eval_univCl, succInd, models_iff, Matrix.constant_eq_singleton,
        Semiformula.eval_substs]
  intro e hzero hsucc x; induction x with
  | zero => exact hzero
  | succ x ih => exact hsucc x ih

instance models_ISigma (Γ s) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s := by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)

instance models_IBroadSigma (Γ s) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s := by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)

instance models_ISigmaZero : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := inferInstance

instance models_ISigmaOne : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance

instance models_IBroadSigmaOne : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺₁ := inferInstance

instance models_Peano : ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Peano, Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)

instance sigmaOneSound_IBroadSigmaOne : 𝗜𝚺⁺₁.SoundOnHierarchy 𝚺 1 := inferInstance

instance sigmaOneSound_Peano : 𝗣𝗔.SoundOnHierarchy 𝚺 1 := inferInstance

instance : Entailment.Consistent (𝗜𝗡𝗗 Γ s) := (𝗜𝗡𝗗 Γ s).consistent_of_sound (Eq ⊥) rfl

instance : Entailment.Consistent (𝗜𝗡𝗗⁺ Γ s) := (𝗜𝗡𝗗⁺ Γ s).consistent_of_sound (Eq ⊥) rfl

instance : Entailment.Consistent 𝗣𝗔 := 𝗣𝗔.consistent_of_sound (Eq ⊥) rfl

instance : 𝗣𝗔 ⪯ 𝗧𝗔 := inferInstance

instance (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T :=
  have : 𝗥₀ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝗜𝚺₀ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗜𝚺₀ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗜𝚺₁ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝗜𝚺⁺₁ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗜𝚺⁺₁ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗣𝗔 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance (T U : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] : 𝗜𝚺₁ ⪯ T ∪ U :=
  Entailment.WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) inferInstance

end FFL.FirstOrder.Arithmetic
