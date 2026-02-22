module

public import Foundation.Modal.Kripke.Root
public import Mathlib.Data.Finite.Card


@[expose] public section

def IsEquiv.equivalence [IsEquiv α r] : Equivalence r where
  refl := Std.Refl.refl
  symm {_ _} := by apply Std.Symm.symm
  trans {_ _ _} := by apply IsTrans.trans


namespace LO.Modal

namespace Kripke

def clusterEquiv (F : Kripke.Frame) (x y : F.World) := x = y ∨ (x ≺ y ∧ y ≺ x)

section

variable {F : Kripke.Frame} {x y z : F.World}

instance : Std.Refl (clusterEquiv F) := by tauto;

instance : Std.Symm (clusterEquiv F) := ⟨by
  rintro x y (rfl | ⟨Rxy, Ryx⟩);
  . apply refl;
  . right; exact ⟨Ryx, Rxy⟩;
⟩

instance [F.IsTransitive] : IsTrans _ (clusterEquiv F) := ⟨by
  rintro x y z (rfl | ⟨Rxy, Ryx⟩) (rfl | ⟨Ryz, Rzy⟩);
  . apply refl;
  . right; exact ⟨Ryz, Rzy⟩;
  . right; exact ⟨Rxy, Ryx⟩;
  . right;
    constructor;
    . exact _root_.trans Rxy Ryz;
    . exact _root_.trans Rzy Ryx;
⟩

instance [F.IsTransitive] : IsEquiv _ (clusterEquiv F) where

end

abbrev Cluster (F : Frame) [F.IsTransitive] := Quotient (⟨clusterEquiv F, IsEquiv.equivalence⟩)

namespace Cluster

variable {F : Frame} [F.IsTransitive] {x y : F.World} {C : Cluster F}

instance [Finite F] : Finite (Cluster F) := Finite.of_surjective (λ x => ⟦x⟧) $ by
  intro C;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C;
  use x;

@[simp]
lemma iff_eq_cluster : (⟦x⟧ : Cluster F) = ⟦y⟧ ↔ (x = y ∨ (x ≺ y ∧ y ≺ x)) := by
  simp only [Quotient.eq, clusterEquiv];

protected abbrev rel : Rel (Cluster F) (Cluster F) := Quotient.lift₂ (λ x y => x ≺ y) $ by
    rintro x₁ y₁ x₂ y₂ (rfl | ⟨Rx₁x₂, Rx₂x₁⟩) (rfl | ⟨Ry₁y₂, Ry₂y₁⟩);
    . rfl;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact _root_.trans Rx₁y₁ Ry₁y₂;
      . intro Rx₁y₂;
        exact _root_.trans Rx₁y₂ Ry₂y₁;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact _root_.trans Rx₂x₁ Rx₁y₁;
      . intro Rx₂y₁;
        exact _root_.trans Rx₁x₂ Rx₂y₁;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact _root_.trans Rx₂x₁ $ _root_.trans Rx₁y₁ Ry₁y₂;
      . intro Rx₂y₂;
        exact _root_.trans (_root_.trans Rx₁x₂ Rx₂y₂) Ry₂y₁;
local infix:50 " ≼ " => Cluster.rel

instance : IsTrans (Cluster F) (· ≼ ·) := ⟨by
  rintro X Y Z RXY RYZ;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  obtain ⟨z, rfl⟩ := Quotient.exists_rep Z;
  simp only [Cluster.rel, Quotient.lift_mk] at RXY RYZ;
  apply _root_.trans RXY RYZ;
⟩

instance : IsAntisymm (Cluster F) (· ≼ ·) := ⟨by
  rintro X Y RXY RYX;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  simp only [Cluster.rel, Quotient.lift_mk] at RXY RYX;
  apply iff_eq_cluster.mpr;
  right;
  tauto;
⟩

instance [F.IsReflexive] : IsRefl (Cluster F) (· ≼ ·)  := ⟨by
  rintro X;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  simp only [Cluster.rel, Quotient.lift_mk];
  apply Std.Refl.refl;
⟩

instance [Std.Total F] : IsTotal (Cluster F) (· ≼ ·) := ⟨by
  rintro X Y;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  rcases total_of (· ≺ ·) x y with Rxy | Rxy <;> tauto;
⟩


protected abbrev strict_rel : Rel (Cluster F) (Cluster F) := λ X Y => X ≼ Y ∧ X ≠ Y
local infix:50 " ≺ " => Cluster.strict_rel

instance : IsTrans (Cluster F) (· ≺ ·) := ⟨by
  rintro X Y Z ⟨RXY, _⟩ ⟨RYZ, _⟩;
  constructor;
  . exact _root_.trans RXY RYZ;
  . by_contra hC;
    subst hC;
    have : X = Y := antisymm RXY RYZ;
    contradiction;
⟩

instance : IsIrrefl (Cluster F) (· ≺ ·) := ⟨by
  rintro X;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  simp [Cluster.strict_rel, Quotient.lift_mk];
⟩

instance : IsAsymm (Cluster F) (· ≺ ·) := ⟨by
  intro X Y ⟨RXY, _⟩;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  simp_all [Cluster.strict_rel, Quotient.lift_mk, clusterEquiv];
⟩

instance : IsStrictOrder (Cluster F) (· ≺ ·) where

instance [IsTrichotomous _ F] : IsTrichotomous (Cluster F) (· ≺ ·) := ⟨by
  rintro X Y;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  rcases (trichotomous (r := (· ≺ ·)) x y) with Rxy | rfl | Rxy <;> tauto;
⟩

instance [IsTrichotomous _ F] : IsStrictTotalOrder (Cluster F) (· ≺ ·) where


protected abbrev mem : Cluster F → F.World → Prop := λ C x => C = ⟦x⟧
instance : Membership (F.World) (Cluster F) := ⟨Cluster.mem⟩

@[simp]
lemma mem_iff : x ∈ C ↔ C = ⟦x⟧ := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  simp only [Quotient.eq, clusterEquiv, Cluster.mem, Membership.mem];

@[simp]
lemma mem_iff₂ : x ∈ (⟦y⟧ : Cluster F) ↔ y = x ∨ y ≺ x ∧ x ≺ y := by
  constructor;
  . intro h;
    replace h := mem_iff.mp h;
    simpa using h;
  . intro h;
    apply mem_iff.mpr;
    simpa using h;

lemma mem_same_cluster (hx : x ∈ C) (hy : y ∈ C): y = x ∨ (y ≺ x ∧ x ≺ y) := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  replace hx := mem_iff₂.mp hx;
  replace hy := mem_iff₂.mp hy;
  rcases hx with rfl | ⟨Rcx, Rxc⟩ <;>
  rcases hy with rfl | ⟨Rcy, Ryc⟩;
  . tauto;
  . tauto;
  . tauto;
  . right;
    constructor;
    . exact _root_.trans Ryc Rcx;
    . exact _root_.trans Rxc Rcy;

lemma refl_in_cluster_of_more_than_one (h : ∃ x y, x ≠ y ∧ x ∈ C ∧ y ∈ C) : ∀ z, z ∈ C → z ≺ z := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  obtain ⟨x, y, hxy, hx, hy⟩ := h;
  intro z hz;
  simp only [mem_iff₂] at hx hy hz;
  rcases hx with rfl | ⟨Rcx, Rxc⟩ <;>
  rcases hy with rfl | ⟨Rcy, Ryc⟩ <;>
  rcases hz with rfl | ⟨Rcz, Rzc⟩;
  . contradiction;
  . exact _root_.trans Rzc Rcz;
  . exact _root_.trans Rcy Ryc;
  . exact _root_.trans Rzc Rcz;
  . exact _root_.trans Rcx Rxc;
  . exact _root_.trans Rzc Rcz;
  . exact _root_.trans Rcy Ryc;
  . exact _root_.trans Rzc Rcz;

lemma refl_rel_of_more_than_one (h : ∃ x y, x ≠ y ∧ x ∈ C ∧ y ∈ C) : C ≼ C := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  apply refl_in_cluster_of_more_than_one h;
  tauto;

def degenerate (C : Cluster F) := ¬C ≼ C

lemma not_more_than_two_of_degenerate : C.degenerate → ¬∃ x y, x ≠ y ∧ x ∈ C ∧ y ∈ C := by
  apply not_imp_not.mpr $ refl_rel_of_more_than_one;

lemma degenerate_iff_exists_unique_irrefl_point : C.degenerate ↔ (∃! x, x ∈ C ∧ ¬x ≺ x) := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  constructor;
  . intro h;
    use c;
    constructor;
    . simpa;
    . rintro x ⟨hx₁, hx₂⟩;
      by_contra nexc;
      have := not_more_than_two_of_degenerate h;
      push_neg at this;
      replace this := this c x (by tauto) (by tauto);
      contradiction;
  . rintro ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩;
    rcases (mem_iff₂.mp hx₁) with rfl | ⟨Rxy, Ryx⟩;
    . apply hx₂;
    . exfalso;
      exact hx₂ $ _root_.trans Ryx Rxy;

def simple (C : Cluster F) := ∃! x, x ∈ C ∧ x ≺ x

lemma not_degenerate_of_simple (h : C.simple) : ¬C.degenerate := by
  apply degenerate_iff_exists_unique_irrefl_point.not.mpr;
  by_contra hC;
  obtain ⟨x, hx⟩ := h;
  obtain ⟨y, hy⟩ := hC;
  obtain ⟨⟨hx₁, hx₂⟩, hx₃⟩ := hx;
  obtain ⟨⟨hy₁, hy₂⟩, hy₃⟩ := hy;
  by_cases exy : x = y;
  . subst exy;
    contradiction;
  . exact hy₂ $ refl_in_cluster_of_more_than_one (by use x, y) y hy₁;

lemma refl_in_simple (h : C.simple) (hx : x ∈ C) : x ≺ x := by
  obtain ⟨y, ⟨hy, _⟩, _⟩ := h;
  rcases mem_same_cluster hx hy with rfl | ⟨Rxy, Ryx⟩;
  . assumption;
  . exact _root_.trans Ryx Rxy;

def proper (C : Cluster F) := ∃ x y, x ≠ y ∧ x ∈ C ∧ y ∈ C

lemma not_degenerate_of_proper (h : C.proper) : ¬C.degenerate := by
  by_contra hC;
  exact not_more_than_two_of_degenerate hC h;

lemma refl_in_proper (h : C.proper) (hx : x ∈ C) : x ≺ x := by
  obtain ⟨y, z, hxy, hy, hz⟩ := h;
  rcases mem_same_cluster hx hy with rfl | ⟨Rxy, Ryx⟩;
  . rcases mem_same_cluster hy hz with rfl | ⟨Ryz, Rzy⟩;
    . contradiction;
    . exact _root_.trans Rzy Ryz;
  . exact _root_.trans Ryx Rxy;

lemma either_simple_or_proper_of_non_degenerate (h : ¬C.degenerate) : C.simple ∨ C.proper := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C;
  by_cases ex : ∃ y, x ≠ y ∧ (⟦x⟧ : Cluster F) = ⟦y⟧;
  . right;
    obtain ⟨y, nexy, h⟩ := ex;
    use x, y;
    tauto;
  . left;
    use x;
    constructor;
    . simpa [degenerate] using h;
    . rintro y ⟨hy₁, hy₂⟩;
      simp only [ne_eq, Quotient.eq, not_exists, not_and] at ex;
      replace hy₁ := iff_eq_cluster.mp hy₁;
      rcases hy₁ with rfl | ⟨Rxy, Ryx⟩;
      . tauto;
      . apply not_imp_comm.mp (ex y) ?_ |>.symm;
        push_neg;
        dsimp [clusterEquiv];
        tauto;

lemma refl_of_mem_non_degenerate (h : ¬C.degenerate) (hx : x ∈ C) : x ≺ x := by
  rcases (either_simple_or_proper_of_non_degenerate h) with h | h;
  . apply refl_in_simple h hx;
  . apply refl_in_proper h hx;

theorem degenerate_or_simple_or_proper : C.degenerate ∨ C.simple ∨ C.proper := by
  by_cases h : C.degenerate;
  . left;
    exact h;
  . right;
    exact either_simple_or_proper_of_non_degenerate h;

end Cluster



def Frame.skeleton (F : Frame) [F.IsTransitive] : Kripke.Frame where
  World := Cluster F
  world_nonempty := ⟨⟦F.world_nonempty.some⟧⟩
  Rel := Cluster.rel

section

variable {F : Frame} [F.IsTransitive]

instance [Finite F] : Finite F.skeleton := by
  dsimp only [Frame.skeleton];
  infer_instance;

instance : F.skeleton.IsTransitive := by
  dsimp only [Frame.skeleton];
  infer_instance;

instance : F.skeleton.IsAntisymmetric :=  by
  dsimp only [Frame.skeleton];
  infer_instance;

instance [F.IsReflexive] : F.skeleton.IsReflexive :=  by
  dsimp only [Frame.skeleton];
  infer_instance;

instance [F.IsReflexive] : F.skeleton.IsPartialOrder where


instance [Std.Total F] : Std.Total F.skeleton := by
  dsimp only [Frame.skeleton];
  infer_instance;

instance [Std.Total F] : IsLinearOrder _ F.skeleton where

end


def Frame.strictSkelteon (F : Frame) [F.IsTransitive] : Kripke.Frame where
  World := Cluster F
  world_nonempty := ⟨⟦F.world_nonempty.some⟧⟩
  Rel := Cluster.strict_rel

namespace Frame.strictSkelteon

variable {F : Frame} [F.IsTransitive]

instance [Finite F] : Finite F.strictSkelteon := by
  dsimp only [Frame.strictSkelteon];
  infer_instance;

instance : F.strictSkelteon.IsTransitive := by
  dsimp only [Frame.strictSkelteon];
  infer_instance;

instance : F.strictSkelteon.IsIrreflexive := by
  dsimp only [Frame.strictSkelteon];
  infer_instance;

instance [IsTrichotomous _ F] : IsTrichotomous _ F.strictSkelteon := by
  dsimp only [Frame.strictSkelteon];
  infer_instance;

instance [IsTrichotomous _ F] : IsStrictTotalOrder _ F.strictSkelteon where

end Frame.strictSkelteon

end Kripke

end LO.Modal
end
