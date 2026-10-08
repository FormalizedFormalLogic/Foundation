module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The `Δ` induction scheme `𝗜𝚫` over the prenex hierarchy

A $\Delta_s$ formula is not a syntactic class, so the induction scheme for it carries its own
equivalence hypothesis: the axiom for a pair `φ`, `ψ` of $\Sigma_s$ formulas assumes that `φ` and
`¬ψ` define the same set and concludes successor induction for `φ`.

## References

- [Sla04, §1.2]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def deltaInd {ξ} (φ ψ : Semiformula L ξ 1) : Formula L ξ :=
  “(∀ x, !φ x ↔ ¬!ψ x) → !φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def DeltaInductionScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { σ | ∃ φ ψ : ArithmeticSemiformula ℕ 1, Γ φ ∧ Γ ψ ∧ σ = .univCl (deltaInd φ ψ) }

abbrev IDelta (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s)

prefix:max "𝗜𝚫 " => IDelta

abbrev IDeltaOnBroadHierarchy (s : ℕ) : ArithmeticTheory :=
  𝗜𝚺₀ ∪ DeltaInductionScheme (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s)

prefix:max "𝗜𝚫⁺ " => IDeltaOnBroadHierarchy

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma DeltaInductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    DeltaInductionScheme C ⊆ DeltaInductionScheme C' := by
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩; exact ⟨φ, ψ, h hφ, h hψ, rfl⟩

lemma mem_DeltaInductionScheme_of_mem {φ ψ : ArithmeticSemiformula ℕ 1} (hφ : C φ) (hψ : C ψ) :
    .univCl (deltaInd φ ψ) ∈ DeltaInductionScheme C := ⟨φ, ψ, hφ, hψ, rfl⟩

lemma IDelta_subset_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⊆ 𝗜𝚫⁺ s :=
  Set.union_subset_union_right _ (DeltaInductionScheme_subset (·.hierarchy))

instance IDelta_weakerThan_IDeltaOnBroadHierarchy (s : ℕ) : 𝗜𝚫 s ⪯ 𝗜𝚫⁺ s :=
  WeakerThan.ofSubset (IDelta_subset_IDeltaOnBroadHierarchy s)

instance (s : ℕ) : 𝗜𝚺₀ ⪯ 𝗜𝚫 s := WeakerThan.ofSubset Set.subset_union_left

instance (s : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚫 s :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀ := inferInstance
  WeakerThan.trans this inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma models_deltaInd_iff (φ ψ : ArithmeticSemiformula ℕ 1) :
    V↓[ℒₒᵣ] ⊧ .univCl (deltaInd φ ψ) ↔
      ∀ f : ℕ → V, (∀ x : V, φ.Eval ![x] f ↔ ¬ψ.Eval ![x] f) →
        φ.Eval ![0] f → (∀ x : V, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x : V, φ.Eval ![x] f := by
  simp [models_iff, Semiformula.eval_univCl, deltaInd, Semiformula.eval_substs]

lemma DeltaInductionScheme.models_of_exists_eval_iff [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {C C' : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* DeltaInductionScheme C']
    (h : ∀ φ, C φ → ∃ ψ, C' ψ ∧
      ∀ (e : Fin 1 → V) (f : ℕ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ) :
    V↓[ℒₒᵣ] ⊧* DeltaInductionScheme C := by
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩
  obtain ⟨φ', hφ', Hφ⟩ := h φ hφ
  obtain ⟨ψ', hψ', Hψ⟩ := h ψ hψ
  have := Theory.models (T := DeltaInductionScheme C') V
    (mem_DeltaInductionScheme_of_mem hφ' hψ')
  simp only [models_deltaInd_iff, Hφ, Hψ] at this ⊢
  exact this

lemma IDelta_weakerThan_of_le {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : 𝗜𝚫 s₁ ⪯ 𝗜𝚫 s₂ :=
  weakerThan_of_models.{0} _ _ fun V _ hV ↦ by
    have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss hV Set.subset_union_left
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
    apply Semantics.ModelsSet.union_iff.mpr
    and_intros
    · exact h₀
    · have : V↓[ℒₒᵣ] ⊧* DeltaInductionScheme (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 s₂) :=
        models_of_ss hV Set.subset_union_right
      exact DeltaInductionScheme.models_of_exists_eval_iff fun _ hφ ↦
        (hφ.exists_eval_iff_of_le h).imp fun _ H ↦ ⟨H.1, H.2 V⟩

end models

section standardModel

instance models_IDeltaOnBroadHierarchy (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺ s := by
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact inferInstance
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, ψ, -, -, rfl⟩
    apply models_deltaInd_iff _ _ |>.mpr
    intro f _ hzero hsucc x
    induction x with
    | zero => exact hzero
    | succ x ih => exact hsucc x ih

instance models_IDelta (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚫 s :=
  Semantics.ModelsSet.of_subset (models_IDeltaOnBroadHierarchy s)
    (IDelta_subset_IDeltaOnBroadHierarchy s)

instance (s : ℕ) : Consistent (𝗜𝚫 s) := (𝗜𝚫 s).consistent_of_sound (Eq ⊥) rfl

end standardModel

end FFL.FirstOrder.Arithmetic
