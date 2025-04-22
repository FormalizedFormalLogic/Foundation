import Foundation.Modal.Kripke.Preservation

def IsEquiv.equivalence [IsEquiv α r] : Equivalence r where
  refl := IsRefl.refl
  symm {_ _} := by apply IsSymm.symm
  trans {_ _ _} := by apply IsTrans.trans


namespace LO.Modal

namespace Kripke

def clusterEquiv (F : Kripke.Frame) (x y : F.World) := x = y ∨ (x ≺ y ∧ y ≺ x)

section

variable {F : Kripke.Frame} {x y z : F.World}

instance : IsRefl _ (clusterEquiv F) := by tauto;

instance : IsSymm _ (clusterEquiv F) := ⟨by
  rintro x y (rfl | ⟨Rxy, Ryx⟩);
  . apply refl;
  . right; exact ⟨Ryx, Rxy⟩;
⟩

instance [IsTrans _ F] : IsTrans _ (clusterEquiv F) := ⟨by
  rintro x y z (rfl | ⟨Rxy, Ryx⟩) (rfl | ⟨Ryz, Rzy⟩);
  . apply refl;
  . right; exact ⟨Ryz, Rzy⟩;
  . right; exact ⟨Rxy, Ryx⟩;
  . right;
    constructor;
    . exact _root_.trans Rxy Ryz;
    . exact _root_.trans Rzy Ryx;
⟩

instance [IsTrans _ F] : IsEquiv _ (clusterEquiv F) where

end


abbrev ClusterEqvSetoid (F : Frame) [IsTrans _ F] : Setoid (F.World) := ⟨clusterEquiv F, IsEquiv.equivalence⟩

abbrev Cluster (F : Frame) [IsTrans _ F] := Quotient (ClusterEqvSetoid F)

namespace Cluster

variable {F : Frame} [IsTrans _ F] {x y : F.World} {C Cx Cy : Cluster F}

@[simp]
lemma iff_eq_cluster : (⟦x⟧ : Cluster F) = ⟦y⟧ ↔ (x = y ∨ (x ≺ y ∧ y ≺ x)) := by
  simp only [ClusterEqvSetoid, Quotient.eq, clusterEquiv];

@[simp]
protected def rel : Rel (Cluster F) (Cluster F) := Quotient.lift₂ (λ x y => x ≺ y) $ by
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

protected def strict_rel : Rel (Cluster F) (Cluster F) := λ X Y => X ≼ Y ∧ X ≠ Y
local infix:50 " ≺ " => Cluster.strict_rel

lemma refl_in_cluster_of_more_than_one (h : ∃ x y, x ≠ y ∧ C = ⟦x⟧ ∧ C = ⟦y⟧) : ∀ z, C = ⟦z⟧ → z ≺ z := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  obtain ⟨x, y, hxy, hx, hy⟩ := h;
  intro z hz;
  simp only [ClusterEqvSetoid, Quotient.eq, clusterEquiv] at hx hy hz;
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

lemma refl_rel_of_more_than_one (h : ∃ x y, x ≠ y ∧ C = ⟦x⟧ ∧ C = ⟦y⟧) : C ≼ C := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  apply refl_in_cluster_of_more_than_one h;
  tauto;

def degenerate (C : Cluster F) := ¬C ≼ C

lemma not_more_than_two_of_degenerate : C.degenerate → ¬∃ x y, x ≠ y ∧ C = ⟦x⟧ ∧ C = ⟦y⟧ := by
  apply not_imp_not.mpr $ refl_rel_of_more_than_one;

lemma degenerate_iff_exists_unique_irrefl_point : C.degenerate ↔ (∃! x, C = ⟦x⟧ ∧ ¬x ≺ x) := by
  obtain ⟨c, rfl⟩ := Quotient.exists_rep C;
  constructor;
  . intro h;
    use c;
    constructor;
    . tauto;
    . rintro x ⟨hx₁, hx₂⟩;
      by_contra nexc;
      have := not_more_than_two_of_degenerate h;
      push_neg at this;
      replace this := this c x (by tauto) (by tauto);
      contradiction;
  . rintro ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩;
    simp only [ClusterEqvSetoid, Quotient.eq, clusterEquiv] at hx₁;
    rcases hx₁ with rfl | ⟨Rxy, Ryx⟩;
    . apply hx₂;
    . exfalso;
      exact hx₂ $ _root_.trans Ryx Rxy;

def simple (C : Cluster F) := ∃! x, C = ⟦x⟧ ∧ x ≺ x

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

def proper (C : Cluster F) := ∃ x y, x ≠ y ∧ C = ⟦x⟧ ∧ C = ⟦y⟧

lemma not_degenerate_of_proper (h : C.proper) : ¬C.degenerate := by
  by_contra hC;
  exact not_more_than_two_of_degenerate hC h;

lemma either_simple_or_proper_of_non_degenerate (h : ¬C.degenerate) : C.simple ∨ C.proper := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep C;
  by_cases ex : ∃ y, x ≠ y ∧ (⟦x⟧ : Cluster F) = ⟦y⟧;
  . right;
    obtain ⟨y, nexy, h⟩ := ex;
    use x, y;
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
        dsimp [ClusterEqvSetoid, clusterEquiv];
        tauto;

theorem degenerate_or_simple_or_proper : C.degenerate ∨ C.simple ∨ C.proper := by
  by_cases h : C.degenerate;
  . left;
    exact h;
  . right;
    exact either_simple_or_proper_of_non_degenerate h;

end Cluster



def Frame.skelton (F : Frame) [IsTrans _ F] : Kripke.Frame where
  World := Cluster F
  world_nonempty := ⟨⟦F.world_nonempty.some⟧⟩
  Rel := Quotient.lift₂ (λ x y => x ≺ y) $ by
    rintro x₁ y₁ x₂ y₂ (rfl | ⟨Rx₁x₂, Rx₂x₁⟩) (rfl | ⟨Ry₁y₂, Ry₂y₁⟩);
    . rfl;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact IsTrans.transitive Rx₁y₁ Ry₁y₂;
      . intro Rx₁y₂;
        exact IsTrans.transitive Rx₁y₂ Ry₂y₁;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact IsTrans.transitive Rx₂x₁ Rx₁y₁;
      . intro Rx₂y₁;
        exact IsTrans.transitive Rx₁x₂ Rx₂y₁;
    . apply eq_iff_iff.mpr;
      constructor;
      . intro Rx₁y₁;
        exact IsTrans.transitive Rx₂x₁ $ IsTrans.transitive Rx₁y₁ Ry₁y₂;
      . intro Rx₂y₂;
        exact IsTrans.transitive (IsTrans.transitive Rx₁x₂ Rx₂y₂) Ry₂y₁;

section

variable {F : Frame} [IsTrans _ F]

instance : IsTrans _ F.skelton := ⟨by
  rintro X Y Z RXY RYZ;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  obtain ⟨z, rfl⟩ := Quotient.exists_rep Z;
  simp only [Frame.skelton, Quotient.lift_mk] at RXY RYZ;
  apply IsTrans.transitive RXY RYZ;
⟩

instance : IsAntisymm _ F.skelton := ⟨by
  rintro X Y RXY RYX;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  obtain ⟨y, rfl⟩ := Quotient.exists_rep Y;
  simp only [Frame.skelton, Quotient.lift_mk] at RXY RYX;
  apply Quotient.eq.mpr;
  right;
  tauto;
⟩

instance [IsRefl _ F] : IsRefl _ F.skelton := ⟨by
  rintro X;
  obtain ⟨x, rfl⟩ := Quotient.exists_rep X;
  simp only [Frame.skelton, Quotient.lift_mk]
  apply IsRefl.refl;
⟩

instance [IsRefl _ F] : IsPartialOrder _ F.skelton where

end

end Kripke

end LO.Modal
