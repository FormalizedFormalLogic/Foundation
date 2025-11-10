import Foundation.FirstOrder.SetTheory.Z
import Mathlib.Data.QPF.Univariate.Basic

/-! # $\mathbf{P}$-name -/

namespace LO.FirstOrder.SetTheory

variable (ℙ : Type u) [Preorder ℙ]

/-- ref:
  https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ZFSet.20and.20computability
  https://github.com/vihdzp/combinatorial-games/blob/9130275873edbae2fba445e0c9fa4a9e17546b36/CombinatorialGames/Game/Functor.lean -/
@[ext]
structure NameFunctor (α : Type (u + 1)) : Type _ where
  toFun : ℙ → Set α
  small : ∀ p, Small.{u} (toFun p)
  monotone {p q} : q ≤ p → toFun p ⊆ toFun q

variable {ℙ}

instance : CoeFun (NameFunctor ℙ α) (fun _ ↦ ℙ → Set α) := ⟨fun F ↦ F.toFun⟩

instance (F : NameFunctor ℙ α) (p : ℙ) : Small.{u} (F p) := F.small p

#check QPF.abs

instance : Functor (NameFunctor ℙ) where
  map m F := ⟨fun p ↦ m '' F p, fun _ ↦ inferInstance, fun h b ↦ by
    simp only [Set.mem_image, forall_exists_index, and_imp]
    rintro a ha rfl
    exact ⟨a, F.monotone h ha, rfl⟩⟩

variable {F : NameFunctor ℙ α}

lemma mem_of_le {p q : ℙ} (x : F p) (hqp : q ≤ p) : ↑x ∈ F q := F.monotone hqp x.prop

noncomputable
instance : QPF (NameFunctor ℙ) where
  P := ⟨(C : Type u) × (ℙ → Set C), fun s ↦ s.1⟩
  abs {α} s := ⟨fun p ↦ s.2 '' s.1.2 p, fun _ ↦ inferInstance, fun h a ↦ by
    simp
    rintro c hc rfl
    sorry⟩
  repr F :=
    let C := (p : ℙ) × Shrink (F p)
    ⟨⟨C, fun p ↦ {c | p ≤ c.1}⟩, fun c ↦ ((equivShrink _).symm c.2).val⟩
  abs_repr {α} F := by
    ext p a; simp
    constructor
    · rintro ⟨q, h, x, rfl⟩
      exact mem_of_le _ h
    · rintro ha
      refine ⟨p, by rfl, equivShrink (F p) ⟨a, ha⟩, by simp⟩
  abs_map := by {
    rintro α β m ⟨⟨C, s⟩, s⟩
    simp at s
    ext p b; simp
    sorry
   }

end LO.FirstOrder.SetTheory
