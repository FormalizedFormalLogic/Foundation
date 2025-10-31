import Foundation.FirstOrder.SetTheory.Basic
import Mathlib.SetTheory.ZFC.Class

/-! # Standard model of set theory -/

namespace ZFSet

/-- ? -/
noncomputable instance allFunctionDefinable (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) : ZFSet.Definable n f where
  out v := Quotient.out <| f fun i ↦ ZFSet.mk (v i)

noncomputable def choose₁ (x : ZFSet) : ZFSet := Classical.epsilon fun z ↦ z ∈ x

lemma choose₁_mem_self {x : ZFSet} (h : x ≠ ∅) : x.choose₁ ∈ x := Classical.epsilon_spec (by contrapose! h; ext; simp_all)

noncomputable def choice' (𝓧 : ZFSet) : ZFSet := image choose₁ 𝓧

lemma choice'_uniqueExists {𝓧 X : ZFSet}
    (he : ∅ ∉ 𝓧)
    (pairwise_disjoint : ∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y)
    (hX : X ∈ 𝓧) : ∃! x, x ∈ 𝓧.choice' ∧ x ∈ X := by
  apply ExistsUnique.intro X.choose₁
  · exact ⟨ZFSet.mem_image.mpr ⟨X, hX, rfl⟩, choose₁_mem_self <| by rintro rfl; contradiction⟩
  · rintro y ⟨hy, hyx⟩
    rcases ZFSet.mem_image.mp hy with ⟨Y, hY, rfl⟩
    have : X = Y :=
      pairwise_disjoint X hX Y hY ⟨Y.choose₁, hyx, choose₁_mem_self <| by rintro rfl; contradiction⟩
    rcases this
    rfl

end ZFSet

namespace LO.FirstOrder.SetTheory

namespace Standard

@[simp] lemma isEmpty_iff_eq_empty {x : ZFSet.{u}} :
    IsEmpty x ↔ x = ∅ := by
  simpa [IsEmpty] using Iff.symm (ZFSet.eq_empty x)

instance models_zf : ZFSet.{u} ⊧ₘ* 𝗭𝗙 where
  models_set φ hφ := by
    rcases hφ
    case axiom_of_equality h =>
      have : ZFSet.{u} ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ) := inferInstance
      simpa [models_iff] using modelsTheory_iff.mp this h
    case axiom_of_empty_set =>
      suffices ∃ x, ∀ y : ZFSet.{u}, y ∉ x by simpa [models_iff, Axiom.empty]
      exact ⟨∅, by simp⟩
    case axiom_of_extentionality =>
      simp [models_iff, Axiom.extentionality, ZFSet.ext_iff]
    case axiom_of_pairing =>
      suffices
          ∀ x y : ZFSet.{u}, ∃ z, ∀ v : ZFSet.{u}, v ∈ z ↔ v = x ∨ v = y by
        simpa [models_iff, Axiom.pairing]
      intro x y
      exact ⟨{x, y}, by simp⟩
    case axiom_of_union =>
      suffices
          ∀ x : ZFSet.{u}, ∃ y, ∀ z : ZFSet.{u}, z ∈ y ↔ ∃ v ∈ x, z ∈ v by
        simpa [models_iff, Axiom.union]
      intro x
      exact ⟨x.sUnion, by simp⟩
    case axiom_of_power_set =>
      suffices
          ∀ x : ZFSet.{u}, ∃ y, ∀ z : ZFSet.{u}, z ∈ y ↔ z ⊆ x by
        simpa [models_iff, Axiom.power]
      intro x
      exact ⟨x.powerset, by simp⟩
    case axiom_of_infinity =>
      suffices
          ∃ ω, (∅ ∈ ω) ∧
            ∀ x ∈ ω, ∀ y : ZFSet.{u}, (∀ z, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ ω by
        simpa [models_iff, Axiom.infinity, val_isSucc_iff]
      refine ⟨ZFSet.omega, ?_, ?_⟩
      · simp
      · intro x hx y  hy
        have : y = insert x x := by
          ext; simp_all
        simpa [this] using ZFSet.omega_succ hx
    case axiom_of_foundation =>
      suffices
          ∀ x : ZFSet.{u}, IsNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y by
        simpa [models_iff, Axiom.foundation]
      intro x hx
      rcases hx with ⟨y, hx⟩
      refine ⟨ZFSet.mem_wf.min x.toSet ⟨y, by simpa using hx⟩,
        WellFounded.min_mem _ _ _,
        fun _ hx ↦ ZFSet.mem_wf.not_lt_min _ _ (by simpa using hx)⟩
    case axiom_of_separation φ =>
      let P (f : ℕ → ZFSet.{u}) (x : ZFSet.{u}) : Prop :=
        Semiformula.Eval (standardStructure ZFSet.{u}) ![x] f φ
      suffices
          ∀ (f : ℕ → ZFSet.{u}) (x : ZFSet.{u}),
          ∃ y, ∀ z : ZFSet.{u}, z ∈ y ↔ z ∈ x ∧ P f z by
        simpa [models_iff, Axiom.separationSchema, Matrix.constant_eq_singleton, P]
      intro f x
      refine ⟨ZFSet.sep (P f) x, ?_⟩
      intro z; simp
    case axiom_of_replacement φ =>
      let R (f : ℕ → ZFSet.{u}) (x y : ZFSet.{u}) : Prop :=
        Semiformula.Eval (standardStructure ZFSet.{u}) ![x, y] f φ
      suffices
          ∀ f : ℕ → ZFSet.{u},
          (∀ x, ∃! y, R f x y) →
          ∀ X : ZFSet.{u}, ∃ Y : ZFSet.{u}, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R f x y by
        simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
      intro f h X
      have : ∀ x, ∃ y, R f x y := fun x ↦ (h x).exists
      choose F hF using this
      have (x y : ZFSet) : R f x y ↔ F x = y :=
        ⟨fun hxy ↦ (h x).unique (hF x) hxy, by rintro rfl; exact hF x⟩
      refine ⟨ZFSet.image F X, fun _ ↦ by simp [this]⟩

instance models_ac : ZFSet.{u} ⊧ₘ* 𝗔𝗖 where
  models_set φ hφ := by
    rcases hφ
    suffices
        ∀ 𝓧 : ZFSet.{u},
          (∀ X ∈ 𝓧, IsNonempty X) →
          (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ x ∈ X, x ∈ Y) → X = Y) →
          ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X by
      simpa [models_iff, Axiom.choice]
    intro 𝓧 nonempty pairwise_disjoint
    refine ⟨𝓧.choice', ?_⟩
    intro X hX
    exact 𝓧.choice'_uniqueExists
      (by intro h; rcases nonempty ∅ h; simp_all) pairwise_disjoint hX

instance models_zfc : ZFSet.{u} ⊧ₘ* 𝗭𝗙𝗖 := inferInstance

instance models_z : ZFSet.{u} ⊧ₘ* 𝗭 := ModelsTheory.of_ss (inferInstanceAs (ZFSet.{u} ⊧ₘ* 𝗭𝗙)) Zermelo_subset_ZermeloFraenkel

end Standard

instance : Entailment.Consistent 𝗭 := consistent_of_model 𝗭 ZFSet.{0}

instance : Entailment.Consistent 𝗭𝗙 := consistent_of_model 𝗭𝗙 ZFSet.{0}

instance : Entailment.Consistent 𝗭𝗙𝗖 := consistent_of_model 𝗭𝗙𝗖 ZFSet.{0}

end LO.FirstOrder.SetTheory
