module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-! # End extensions and overspill

End extensions of `ℒₒᵣ`-structures, overspill, and cuts.

## References

- [HP98]
- [Kay91]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Semiformula Tarski.Structure

universe u v

variable {ξ : Type*} {M : Type u} {N : Type v} [ORingStructure M]

/-- `N` is an end extension of `M`. -/
class EndExtension (M : outParam (Type u)) (N : Type v) [ORingStructure M] where
  [oring : ORingStructure N]
  emb : M ↪ₛ[ℒₒᵣ] N
  mem_range_of_lt {a : M} {b : N} : b < emb a → b ∈ Set.range emb

@[inherit_doc] infix:50 " ⊆ₑ " => EndExtension

/-- `N` is a proper end extension of `M`. -/
class ProperEndExtension (M : outParam (Type u)) (N : Type v) [ORingStructure M]
    extends EndExtension M N where
  not_surjective : ¬Function.Surjective emb

@[inherit_doc] infix:50 " ⊂ₑ " => ProperEndExtension

namespace EndExtension

instance [hMN : M ⊆ₑ N] : Coe M N := ⟨fun x ↦ hMN.emb x⟩

instance [hMN : M ⊆ₑ N] : ORingStructure N := hMN.oring

variable [hMN : M ⊆ₑ N]

lemma emb_injective : Function.Injective hMN.emb := EmbeddingClass.map_inj hMN.emb

@[simp] lemma emb_zero : hMN.emb 0 = 0 := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Zero.zero ![]

@[simp] lemma emb_one : hMN.emb 1 = 1 := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.One.one ![]

@[simp] lemma emb_add (x y : M) : hMN.emb (x + y) = hMN.emb x + hMN.emb y := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Add.add ![x, y]

@[simp] lemma emb_mul (x y : M) : hMN.emb (x * y) = hMN.emb x * hMN.emb y := by
  simpa [Function.comp_def] using HomClass.func hMN.emb Language.Mul.mul ![x, y]

@[simp] lemma emb_lt_emb {x y : M} : hMN.emb x < hMN.emb y ↔ x < y := by
  simpa [Function.comp_def] using EmbeddingClass.rel hMN.emb Language.LT.lt ![x, y]

lemma emb_eq_emb {x y : M} : hMN.emb x = hMN.emb y ↔ x = y := hMN.emb_injective.eq_iff

theorem models_peanoMinus [N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_theory_iff.mpr <| by
  intro σ hσ
  rcases hσ
  case equal hσ =>
    have h₁ : M↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    exact models_theory_iff.mp h₁ _ hσ
  case addEqOfLt =>
    suffices ∀ x y : M, x < y → ∃ z < y + 1, x + z = y by
      simpa [models_iff, Semiformula.eval_bexsLTSucc] using this
    intro x y h
    obtain ⟨z, hz, hzeq⟩ :=
      Arithmetic.add_eq_of_lt_bounded (hMN.emb x) (hMN.emb y) (by simpa using h)
    have h₁ : z ≤ hMN.emb y := hzeq ▸ le_add_self
    obtain ⟨w, rfl⟩ : z ∈ Set.range hMN.emb :=
      h₁.lt_or_eq.elim hMN.mem_range_of_lt fun h₂ ↦ ⟨y, h₂.symm⟩
    exact ⟨w, hMN.emb_lt_emb.mp (by simpa using hz), hMN.emb_injective (by simpa using hzeq)⟩
  case zeroLe =>
    suffices ∀ x : M, 0 ≤ x by simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x
    rcases le_def.mp (Arithmetic.zero_le (hMN.emb x)) with h | h
    · exact le_def.mpr <| Or.inl <| hMN.emb_injective (by simpa using h)
    · exact le_def.mpr <| Or.inr <| hMN.emb_lt_emb.mp (by simpa using h)
  case oneLeOfZeroLt =>
    suffices ∀ x : M, 0 < x → 1 ≤ x by
      simpa [models_iff, le_iff_of_eq_of_lt, le_def] using this
    intro x h
    have h₁ : (0 : N) < hMN.emb x := by simpa using hMN.emb_lt_emb.mpr h
    rcases le_def.mp (one_le_of_zero_lt _ h₁) with h₂ | h₂
    · exact le_def.mpr <| Or.inl <| hMN.emb_injective (by simpa using h₂)
    · exact le_def.mpr <| Or.inr <| hMN.emb_lt_emb.mp (by simpa using h₂)
  case mulLtMul =>
    suffices ∀ x y z : M, x < y → 0 < z → x * z < y * z by simpa [models_iff] using this
    intro x y z h hz
    have h₁ : (0 : N) < hMN.emb z := by simpa using hMN.emb_lt_emb.mpr hz
    exact hMN.emb_lt_emb.mp (by simpa using mul_lt_mul _ _ (hMN.emb z) (hMN.emb_lt_emb.mpr h) h₁)
  case ltTrans =>
    suffices ∀ x y z : M, x < y → y < z → x < z by simpa [models_iff] using this
    intro x y z hxy hyz
    exact hMN.emb_lt_emb.mp
      (Arithmetic.lt_trans _ _ _ (hMN.emb_lt_emb.mpr hxy) (hMN.emb_lt_emb.mpr hyz))
  case ltTri =>
    suffices ∀ x y : M, x < y ∨ x = y ∨ y < x by simpa [models_iff] using this
    intro x y
    exact (lt_tri (hMN.emb x) (hMN.emb y)).imp hMN.emb_lt_emb.mp
      (Or.imp hMN.emb_eq_emb.mp hMN.emb_lt_emb.mp)
  all_goals
    simp [models_iff]
    simp only [← hMN.emb_lt_emb, ← hMN.emb_eq_emb]
    simp [add_comm, add_left_comm, mul_comm, mul_left_comm, mul_add]

instance : ℬ[<, ℒₒᵣ].IsInitial hMN.emb where
  operator_iff := by
    intro R hR a b
    obtain rfl := Set.mem_singleton_iff.mp hR
    simp
  initial := by
    intro R hR a b hb
    obtain rfl := Set.mem_singleton_iff.mp hR
    exact hMN.mem_range_of_lt (by simpa using hb)

theorem models_of_Pi1 {T : ArithmeticTheory} (hT : ∀ σ ∈ T, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 σ)
    [N↓[ℒₒᵣ] ⊧* T] :
    M↓[ℒₒᵣ] ⊧* T :=
  models_theory_iff.mpr <| by
    intro σ hσ
    by_contra! h
    have h₁ : ¬σ.Realize N := by
      suffices (∼σ).Eval ![] Empty.elim by simpa
      exact Eval.of_eq
        (Bounding.sigma_one_upward hMN.emb (hT σ hσ).neg ![] Empty.elim
          (by simpa [models_iff] using h))
        (funext (·.elim0))
        (funext (·.elim))
    exact notModels_iff.mpr h₁ (models_theory_iff.mp (inferInstance : N↓[ℒₒᵣ] ⊧* T) σ hσ)

end EndExtension

namespace ProperEndExtension

variable [hMN : M ⊂ₑ N]

lemma exists_not_mem_range : ∃ c : N, c ∉ Set.range hMN.emb := by
  simpa [Function.Surjective, Set.range, not_forall] using hMN.not_surjective

end ProperEndExtension

section Overspill

variable [hMN : M ⊂ₑ N]

theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (e : ℕ → N)
    (h : ∀ a : M, φ.Eval ![hMN.emb a] e) :
    ∃ c : N, c ∉ Set.range hMN.emb ∧ ∀ x < c, φ.Eval ![x] e := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m)
  by_contra! hc
  have h₁ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → x ∈ Set.range hMN.emb := by grind
  have h₂ : ∀ x : N, (∀ y < x, φ.Eval ![y] e) → ∀ y < x + 1, φ.Eval ![y] e := by
    intro x ih y hy
    obtain ⟨a, rfl⟩ := h₁ x ih
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hy) with hy' | rfl
    · exact ih y hy'
    · exact h a
  have h₃ : ∀ x : N, ∀ y < x, φ.Eval ![y] e :=
    InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy Γ m)
      ⟨e, (φ/[#0]).ballLT #0, by simp [hφ], fun x ↦ by simp [eval_ballLT]⟩
      (by simp) h₂
  exact hMN.not_surjective fun x ↦ h₁ x (h₃ x)

end Overspill

section Cut

structure Cut (M : Type u) [ORingStructure M] where
  carrier : Set M
  succ_mem {a : M} : a ∈ carrier → a + 1 ∈ carrier
  mem_of_lt {a b : M} : a < b → b ∈ carrier → a ∈ carrier

namespace Cut

class Closed (I : Cut M) : Prop where
  zero_mem : (0 : M) ∈ I.carrier
  one_mem : (1 : M) ∈ I.carrier
  add_mem {a b : M} : a ∈ I.carrier → b ∈ I.carrier → a + b ∈ I.carrier
  mul_mem {a b : M} : a ∈ I.carrier → b ∈ I.carrier → a * b ∈ I.carrier

variable (I : Cut M) [hI : I.Closed]

instance oringStructure : ORingStructure I.carrier where
  zero := ⟨0, hI.zero_mem⟩
  one := ⟨1, hI.one_mem⟩
  add a b := ⟨a.1 + b.1, hI.add_mem a.2 b.2⟩
  mul a b := ⟨a.1 * b.1, hI.mul_mem a.2 b.2⟩
  lt a b := a.1 < b.1

@[instance_reducible]
def endExtension : I.carrier ⊆ₑ M where
  emb := {
    toFun := Subtype.val,
    func' f v := by cases f <;> rfl
    rel' r _ := by cases r; exacts [congrArg Subtype.val, id]
    toFun_inj := Subtype.val_injective
    rel_inv' r _ := by cases r; exacts [Subtype.ext, id]
  }
  mem_range_of_lt {a b} h := ⟨⟨b, I.mem_of_lt h a.2⟩, rfl⟩

@[simp]
lemma endExtension_emb (x : I.carrier) : I.endExtension.emb x = x.val := rfl

end Cut

namespace EndExtension

variable [hMN : M ⊆ₑ N]

lemma models_ISigma0 [hN : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := hMN.models_peanoMinus
  simp only [Semantics.ModelsSet.union_iff, InductionScheme];
  and_intros;
  · exact this
  · apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩
    have hφ := Bounding.PrenexHierarchy.zero_iff_bounded.mp hφ
    suffices ∀ (v : ℕ → M), φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
        ∀ a, φ.Eval ![a] v by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs] using this
    intro v h0 hs a
    have h₁ : ∀ x : M, φ.Eval ![x] v ↔ φ.Eval ![hMN.emb x] (hMN.emb ∘ v) := by
      intro x;
      simpa [Matrix.comp_vecCons'', Matrix.empty_eq] using
        Bounding.bounded_absolute hMN.emb hφ ![x] v
    have h₂ : ∀ y : N, y < hMN.emb a + 1 → φ.Eval ![y] (hMN.emb ∘ v) := by
      refine InductionScheme.succ_induction (C := ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0)
        ⟨(hMN.emb a + 1) :>ₙ fun j ↦ hMN.emb (v j),
          “#0 < &0” 🡒 (Rew.rewriteMap Nat.succ ▹ φ),
          by simp [Bounding.Hierarchy.zero_iff_bounded.mpr hφ],
          by intro x; simp [Semiformula.eval_rewriteMap, Function.comp_def]⟩
        (by intro _; simpa using (h₁ 0).mp h0) ?_
      intro y ih hy
      have h₃ : y < hMN.emb a := lt_of_lt_of_le (lt_add_one y) (lt_succ_iff_le.mp hy)
      obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt h₃
      simpa using (h₁ (x + 1)).mp (hs x ((h₁ x).mpr (ih (lt_trans h₃ (lt_add_one _)))))
    exact (h₁ a).mpr (h₂ (hMN.emb a) (by simp))

end EndExtension

end Cut

end FFL.FirstOrder.Arithmetic
