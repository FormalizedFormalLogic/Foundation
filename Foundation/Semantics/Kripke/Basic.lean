module

public import Foundation.Logic.LindenbaumAlgebra

@[expose] public section

namespace LO

variable {α : Type u}

structure KripkeFrame (α : Type u) where
  points : Set α
  points_nonempty : points.Nonempty
  rel : α → α → Prop

namespace KripkeFrame

variable {K : KripkeFrame α}

abbrev restrictedRel {K : KripkeFrame α} (x y : K.points) := K.rel x y
infix:50 " ≺ " => restrictedRel


class Generated (K : KripkeFrame α) (R : Set K.points) (hR : R ≠ ∅) : Prop where
  generated : ∀ x, ∃ r ∈ R, r ≺ x
alias generated := Generated.generated


class Rooted (K : KripkeFrame α) (r : K.points) extends Generated K {r} (by simp)
@[grind .]
lemma rooted {r} [hR : K.Rooted r] : ∀ x : K.points, r ≺ x := by simpa using hR.generated;


class Reflexive (K : KripkeFrame α) extends Std.Refl (α := K.points) (· ≺ ·)
@[grind .]
lemma refl [hRefl : K.Reflexive] : ∀ x : K.points, x ≺ x := hRefl.refl


class Transitive (K : KripkeFrame α) extends IsTrans (α := K.points) (· ≺ ·)
@[trans]
lemma trans [hTrans : K.Transitive] : ∀ x y z : K.points, x ≺ y → y ≺ z → x ≺ z := hTrans.trans


class Preorder (K : KripkeFrame α) extends IsPreorder (α := K.points) (· ≺ ·)
instance [K.Preorder] : K.Reflexive where
instance [K.Preorder] : K.Transitive where

section Iterate

variable {K : KripkeFrame α}
variable {x y : K.points}
variable {n m : ℕ}

def restrictedRelI {K : KripkeFrame α} : ℕ → Rel K.points K.points
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, x ≺ z ∧ K.restrictedRelI n z y
notation x:80 " ≺^[" n "] " y:80 => restrictedRelI n x y

@[simp, grind .] lemma relI_zero : x ≺^[0] y ↔ (x = y) := by tauto;
@[simp, grind .] lemma relI_one : x ≺^[1] y ↔ x ≺ y := by simp [restrictedRelI];
lemma relI_succ_right : x ≺^[n + 1] y ↔ (∃ z, x ≺ z ∧ z ≺^[n] y) := by tauto;

lemma relI_comp : x ≺^[n + m] y ↔ ∃ z, x ≺^[n] z ∧ z ≺^[m] y := by
  induction n generalizing x y with
  | zero => grind;
  | succ n ih =>
    suffices x ≺^[(n + m) + 1] y ↔ ∃ z, x ≺^[(n + 1)] z ∧ z ≺^[m] y by grind;
    constructor;
    . rintro ⟨w, Rxw, Rwy⟩;
      obtain ⟨z, Rwz, Rzy⟩ := ih.mp Rwy;
      use z;
      constructor;
      . use w;
      . assumption;
    . rintro ⟨z, ⟨w, Rxw, Rwz⟩, Rzy⟩;
      use w;
      constructor;
      . assumption;
      . apply ih.mpr;
        use z;

lemma relI_succ_left : x ≺^[n + 1] y ↔ ∃ z, x ≺^[n] z ∧ z ≺ y := by simpa using relI_comp (n := n) (m := 1);

@[grind →]
lemma unwrap_of_trans [K.Transitive] {n : ℕ+} (Rxy : x ≺^[n] y) : x ≺ y := by
  induction n using PNat.recOn generalizing x with
  | one => simpa using Rxy;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := Rxy;
    exact K.trans x z y Rxz $ ih Rzy;

@[grind →]
lemma unwrap_of_trans' [K.Transitive] {n : ℕ} (hn : 0 < n) (Rxy : x ≺^[n] y) : x ≺ y :=
  unwrap_of_trans (n := ⟨n, by omega⟩) Rxy

@[grind →]
lemma unwrap_of_preorder [K.Preorder] {n : ℕ} (Rxy : x ≺^[n] y) : x ≺ y := by
  induction n with
  | zero =>
    subst Rxy;
    apply K.refl;
  | succ n ih =>
    exact unwrap_of_trans' (by omega) Rxy;

end Iterate



end KripkeFrame



end LO

end
