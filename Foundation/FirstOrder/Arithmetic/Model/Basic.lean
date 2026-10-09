module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.LK.Axiomatizability
public import Foundation.FirstOrder.Arithmetic.Schemata

/-! # End extensions and overspill

End extensions of `ℒₒᵣ`-structures, absoluteness of bounded formulas, and overspill.

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

theorem eval_of_Sigma1 {n : ℕ} {φ : ArithmeticSemiformula ξ n} (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (e : Fin n → M) (f : ξ → M) : φ.Eval e f → φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f) :=
  Bounding.Hierarchy.arithmetic_sigma₁_induction'
    (P := fun n φ ↦ ∀ (e : Fin n → M) (f : ξ → M), φ.Eval e f → φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f))
    hφ
    (fun _ _ _ _ ↦ by simp)
    (fun _ _ _ h ↦ by simp at h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ h ↦ (eval_hom_iff_of_open hMN.emb (by simp)).mp h)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ ⟨ih₁ e f h.1, ih₂ e f h.2⟩)
    (fun _ _ _ _ _ ih₁ ih₂ e f h ↦ h.imp (ih₁ e f) (ih₂ e f))
    (fun _ t θ _ ih e f h ↦ by
      change (θ.ballLT t).Eval (hMN.emb ∘ e) (hMN.emb ∘ f)
      simp only [eval_ballLT, ← HomClass.val_term hMN.emb e f t]
      intro y hy
      obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
      rw [← Matrix.comp_vecCons'']
      exact ih (x :> e) f (eval_ballLT.mp h x (by simpa using hy)))
    (fun _ _ _ ih e f ↦ by
      rintro ⟨x, hx⟩
      exact ⟨hMN.emb x, by rw [← Matrix.comp_vecCons'']; exact ih (x :> e) f hx⟩)
    e f

theorem models_of_Pi1 {T : ArithmeticTheory} (hT : ∀ σ ∈ T, ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 σ)
    [N↓[ℒₒᵣ] ⊧* T] :
    M↓[ℒₒᵣ] ⊧* T :=
  models_theory_iff.mpr <| by
    intro σ hσ
    by_contra! h
    have h₁ : ¬σ.Realize N := by
      suffices (∼σ).Eval ![] Empty.elim by simpa
      exact Eval.of_eq
        (hMN.eval_of_Sigma1 (hT σ hσ).neg ![] Empty.elim (by simpa [models_iff] using h))
        (funext (·.elim0))
        (funext (·.elim))
    exact notModels_iff.mpr h₁ (models_theory_iff.mp (inferInstance : N↓[ℒₒᵣ] ⊧* T) σ hσ)

theorem models_of_Pi1Axiomatizable {T : ArithmeticTheory}
    (hT : Axiomatizable (ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1) T) [N↓[ℒₒᵣ] ⊧* T] : M↓[ℒₒᵣ] ⊧* T := by
  obtain ⟨U, hU, hTU⟩ := hT
  have : U ⪯ T := hTU.symm.le
  have : T ⪯ U := hTU.le
  have : N↓[ℒₒᵣ] ⊧* U := models_of_subtheory ‹N↓[ℒₒᵣ] ⊧* T›
  exact models_of_subtheory (hMN.models_of_Pi1 hU)

end EndExtension

namespace ProperEndExtension

variable [hMN : M ⊂ₑ N]

lemma exists_not_mem_range : ∃ c : N, c ∉ Set.range hMN.emb := by
  simpa [Function.Surjective, Set.range, not_forall] using hMN.not_surjective

end ProperEndExtension

section Absolute

def Absolute (T : ArithmeticTheory) {n : ℕ} (φ : ArithmeticSemiformula ξ n) : Prop :=
  ∀ (M : Type u) (N : Type v) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [hMN : M ⊆ₑ N] [N↓[ℒₒᵣ] ⊧* T]
    (e : Fin n → M) (f : ξ → M), φ.Eval e f ↔ φ.Eval (hMN.emb ∘ e) (hMN.emb ∘ f)

lemma absolute_of_open (T : ArithmeticTheory) {n} {φ : ArithmeticSemiformula ξ n} (hφ : φ.Open) :
    Absolute T φ := by
  intro M N _ _ hMN _ e f
  exact eval_hom_iff_of_open hMN.emb hφ

@[simp, grind .]
theorem absolute_of_bounded {T : ArithmeticTheory} {n : ℕ} {φ : ArithmeticSemiformula ξ n}
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) : Absolute T φ :=
  bounded_induction_open (P := fun _ φ ↦ Absolute T φ)
    (fun _ _ hφ ↦ absolute_of_open T hφ)
    (fun _ _ _ _ _ ihφ ihψ M N _ _ hMN _ e f ↦ by simp [ihφ M N e f, ihψ M N e f])
    (fun _ _ _ _ _ ihφ ihψ M N _ _ hMN _ e f ↦ by simp [ihφ M N e f, ihψ M N e f])
    (fun _ t θ _ ih ↦ show Absolute T (θ.ballLT t) from fun M N _ _ hMN _ e f ↦ by
      simp only [eval_ballLT, ← HomClass.val_term hMN.emb e f t]
      constructor
      · intro h y hy
        obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
        rw [← Matrix.comp_vecCons'']
        exact (ih M N (x :> e) f).mp (h x (by simpa using hy))
      · intro h x hx
        have h₁ := h (hMN.emb x) (by simpa using hx)
        rw [← Matrix.comp_vecCons''] at h₁
        exact (ih M N (x :> e) f).mpr h₁)
    (fun _ t θ _ ih ↦ show Absolute T (θ.bexsLT t) from fun M N _ _ hMN _ e f ↦ by
      simp only [eval_bexsLT, ← HomClass.val_term hMN.emb e f t]
      constructor
      · rintro ⟨x, hx, h⟩
        use hMN.emb x
        and_intros
        · simpa using hx
        · rw [← Matrix.comp_vecCons'']
          exact (ih M N (x :> e) f).mp h
      · rintro ⟨y, hy, h⟩
        obtain ⟨x, rfl⟩ := hMN.mem_range_of_lt hy
        rw [← Matrix.comp_vecCons''] at h
        exact ⟨x, by simpa using hy, (ih M N (x :> e) f).mpr h⟩)
    n φ hφ

end Absolute

section Overspill

variable [hMN : M ⊂ₑ N]

theorem overspill (Γ : Polarity) (m : ℕ) [N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ m φ) (e : ℕ → N)
    (h : ∀ a : M, φ.Eval ![hMN.emb a] e) :
    ∃ c : N, c ∉ Set.range hMN.emb ∧ ∀ x < c, φ.Eval ![x] e := by
  have : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : N↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ m)
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

end FFL.FirstOrder.Arithmetic
