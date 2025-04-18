import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke


section cluster

def clusterEquiv (F : Kripke.Frame) (x y : F.World) := x = y ∨ (x ≺ y ∧ y ≺ x)

variable {F : Kripke.Frame} {x y z : F.World}

lemma clusterEquiv.refl : clusterEquiv F x x := by tauto;

lemma clusterEquiv.symm : clusterEquiv F x y → clusterEquiv F y x := by
  rintro (rfl | ⟨Rxy, Ryx⟩);
  . apply refl;
  . right; exact ⟨Ryx, Rxy⟩;

lemma clusterEquiv.trans [IsTrans _ F] : clusterEquiv F x y → clusterEquiv F y z → clusterEquiv F x z := by
  rintro (rfl | ⟨Rxy, Ryx⟩) (rfl | ⟨Ryz, Rzy⟩);
  . apply refl;
  . right; exact ⟨Ryz, Rzy⟩;
  . right; exact ⟨Rxy, Ryx⟩;
  . right;
    constructor;
    . exact IsTrans.trans _ _ _ Rxy Ryz;
    . exact IsTrans.trans _ _ _ Rzy Ryx;

lemma clusterEquiv.equivalence [IsTrans _ F] : Equivalence (clusterEquiv F) where
  refl _ := refl;
  symm {_ _} := symm;
  trans {_ _ _} := trans

def ClusterEqvSetoid (F : Frame) [IsTrans _ F] : Setoid (F.World) := ⟨clusterEquiv F, clusterEquiv.equivalence⟩

def ClusterEqvQuotient (F : Frame) [IsTrans _ F] := Quotient (ClusterEqvSetoid F)


namespace ClusterEqvQuotient

variable {F : Frame} [IsTrans _ F] {x y : F.World}

/-- cluster of `x` has only one element -/
def isSimple (x : F) := ∀ y : F, (⟦x⟧ : ClusterEqvQuotient F) = ⟦y⟧ → x = y

/-- cluster of `x` has more than one element -/
def isProper (x : F) := ∃ y : F, (⟦x⟧ : ClusterEqvQuotient F) = ⟦y⟧ ∧ x ≠ y

lemma neither_simple_proper : ¬(isSimple x ∧ isProper x) := by
  by_contra hC;
  have ⟨hSimple, ⟨y, eXY, nexy⟩⟩ := hC;
  exact nexy $ hSimple y eXY;

def isDegenerate (x : F) := isSimple x ∧ ¬x ≺ x

end ClusterEqvQuotient

def Frame.skelton (F : Frame) [IsTrans _ F] : Kripke.Frame where
  World := ClusterEqvQuotient F
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

end cluster


section bulldozer

open ClusterEqvQuotient

variable {F BF : Frame} [IsTrans _ F]

open Classical in
structure IrreflBulldozedOf (BF : Frame) (F : Frame) [IsTrans _ F] where
  def_world : BF.World = (F.World × ℕ) := by rfl
  def_rel : ∀ {X Y : BF.World}, X ≺ Y ↔ (
    let ⟨x, i⟩ := cast def_world X;
    let ⟨y, j⟩ := cast def_world Y;
    if clusterEquiv F x y then
      i < j ∨ (x ≺ y ∧ i = j)
    else
      x ≺ y
  )

lemma IrreflBulldozedOf.isIrrefl (bulldozedOf : IrreflBulldozedOf BF F) : IsIrrefl _ BF := ⟨by
  intro X;
  obtain ⟨x, i⟩ := cast (bulldozedOf.def_world) X;
  apply bulldozedOf.def_rel.not.mpr;
  simp;
  sorry
⟩

lemma IrreflBulldozedOf.isTrans (bulldozedOf : IrreflBulldozedOf BF F) : IsTrans _ BF := ⟨by
  intro X Y Z RXY RYZ;
  replace RXY := bulldozedOf.def_rel.mp RXY;
  replace RYZ := bulldozedOf.def_rel.mp RYZ;
  simp at RXY RYZ;
  apply bulldozedOf.def_rel.mpr;
  split at RXY <;> split at RYZ;
  . simp;
    split;
    . sorry;
    . sorry;
  . simp;
    split;
    . sorry;
    . sorry;
  . simp;
    split;
    . sorry;
    . sorry;
  . simp;
    split;
    . sorry;
    . sorry;
⟩

noncomputable def IrreflBulldozedOf.pMorphism (bulldozedOf : IrreflBulldozedOf BF F) : BF →ₚ F where
  toFun X := (cast bulldozedOf.def_world X).1
  forth := by
    rintro X Y RXY;
    replace RXY := bulldozedOf.def_rel.mp RXY;
    simp only at RXY;
    split at RXY;
    case isTrue hCl =>
      dsimp [clusterEquiv] at hCl;
      rcases hCl with e | ⟨Rxy, _⟩;
      . rcases RXY with (a | ⟨b, _⟩);
        . simp [e];
          -- TODO: `if clusterEquiv F x y then`を`degenerate`に置き換える
          sorry;
        . exact b;
      . simpa;
    case isFalse hCl =>
      replace ⟨hCl₁, hCl₂⟩ := not_or.mp hCl;
      rcases not_and_or.mp hCl₂ with _ | _;
      . contradiction;
      . exact RXY;
  back := by
    rintro X y RXy;
    use (cast (bulldozedOf.def_world.symm) ⟨y, (cast bulldozedOf.def_world X).2⟩);
    constructor;
    . simp_all;
    . apply bulldozedOf.def_rel.mpr;
      simp_all;

end bulldozer

end Kripke

end LO.Modal
