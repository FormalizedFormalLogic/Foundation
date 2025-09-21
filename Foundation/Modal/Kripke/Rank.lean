import Foundation.Modal.Kripke.Logic.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot

namespace LO.Modal

noncomputable section

namespace Kripke

variable {φ ψ : Formula ℕ}
         {F : Frame} {r : F} [Fintype F] [F.IsTree r] {x y i j : F}

def Frame.World.finHeight (i : F) : ℕ := fcwHeight (· ≺ ·) i

def Frame.finHeight (F : Frame) {r : F} [Fintype F] [F.IsTree r] : ℕ := Frame.World.finHeight r

namespace Frame

lemma World.finHeight_lt_whole_finHeight {i : F} (hi : r ≺ i) :
    Frame.World.finHeight i < F.finHeight := fcwHeight_gt_of hi

lemma World.finHeight_le_whole_finHeight (i : F) :
    Frame.World.finHeight i ≤ F.finHeight := by
  by_cases hi : i = r
  · rcases hi; rfl
  · have : r ≺ i := root_genaretes'! i hi
    exact le_of_lt (fcwHeight_gt_of this)

lemma World.finHeight_lt_of_rel (hij : i ≺ j) : Frame.World.finHeight i > Frame.World.finHeight j := fcwHeight_gt_of hij

lemma World.exists_of_lt_finHeight (hn : n < Frame.World.finHeight i) : ∃ j : F, i ≺ j ∧ Frame.World.finHeight j = n := fcwHeight_lt hn

lemma finHeight_lt_iff_relItr {i : F} :
    Frame.World.finHeight i < n ↔ ∀ j, ¬i ≺^[n] j  := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices Frame.World.finHeight i ≤ n ↔ ∀ j : F, i ≺ j → Frame.World.finHeight j < n by
      calc
        Frame.World.finHeight i < n + 1
          ↔ Frame.World.finHeight i ≤ n := Nat.lt_add_one_iff
        _ ↔ ∀ j, i ≺ j → Frame.World.finHeight j < n := this
        _ ↔ ∀ j, i ≺ j → ∀ k, ¬j ≺^[n] k := by simp [finHeight_lt_iff_relItr (n := n)]
        _ ↔ ∀ k j, i ≺ j → ¬j ≺^[n] k    := by grind
        _ ↔ ∀ j, ¬i ≺^[n + 1] j  := by simp
    constructor
    · exact fun h j hij ↦ lt_of_lt_of_le (fcwHeight_gt_of hij) h
    · exact fcwHeight_le

lemma le_finHeight_iff_relItr {i : F} :
    n ≤ Frame.World.finHeight i ↔ ∃ j, i ≺^[n] j := calc
  n ≤ Frame.World.finHeight i ↔ ¬Frame.World.finHeight i < n := Iff.symm Nat.not_lt
  _                           ↔ ∃ j, i ≺^[n] j := by simp [finHeight_lt_iff_relItr]

lemma finHeight_eq_iff_relItr {i : F} :
    Frame.World.finHeight i = n ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := calc
  Frame.World.finHeight i = n
    ↔ Frame.World.finHeight i < n + 1 ∧ n ≤ Frame.World.finHeight i := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge
  _ ↔ (∀ j, ¬i ≺^[n + 1] j) ∧ (∃ j, i ≺^[n] j) := by simp [finHeight_lt_iff_relItr, le_finHeight_iff_relItr]
  _ ↔ (∀ k j, i ≺^[n] j → ¬j ≺ k) ∧ (∃ j, i ≺^[n] j) := by simp only [HRel.Iterate.forward, not_exists, not_and]
  _ ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := by grind

lemma exists_terminal (i : F) : ∃ j, i ≺^[Frame.World.finHeight i] j := le_finHeight_iff_relItr.mp (by simp)

lemma eq_finHeight_root : Frame.World.finHeight x = F.finHeight ↔ x = r := by
  constructor;
  . rintro h;
    contrapose! h;
    apply Nat.ne_of_lt;
    apply Frame.World.finHeight_lt_whole_finHeight;
    apply F.root_genaretes'!;
    assumption;
  . tauto;

lemma terminal_rel_finHeight (h : x ≺^[World.finHeight x] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices World.finHeight x + 1 ≤ World.finHeight x by omega;
  exact le_finHeight_iff_relItr.mpr ⟨z, HRel.Iterate.forward.mpr ⟨y, h, Ryz⟩⟩;

namespace extendRoot

@[simp] lemma finHeight_pos : 0 < (F.extendRoot 1).finHeight := by
  apply lt_fcwHeight ?_ (by simp)
  · exact Sum.inr r
  trivial

@[simp] lemma finHeight₁ : (F.extendRoot 1).finHeight = F.finHeight + 1 := by
  let l := World.finHeight (extendRoot.root : F.extendRoot 1)
  suffices
      l ≤ Frame.World.finHeight r + 1 ∧
      Frame.World.finHeight r < l by
    simpa using Nat.eq_iff_le_and_ge.mpr this
  constructor
  · suffices l - 1 ≤ World.finHeight r from Nat.le_add_of_sub_le this
    apply le_finHeight_iff_relItr.mpr
    by_cases hl : l - 1 = 0
    · exact ⟨r, by simp [hl]⟩
    have lpos : 0 < l - 1 := Nat.zero_lt_of_ne_zero hl
    have e : l = (l - 1) + 1 := by
      symm; exact Nat.sub_add_cancel Frame.extendRoot.finHeight_pos
    have : ∃ j, extendRoot.root ≺^[l] j := exists_terminal (extendRoot.root : F.extendRoot 1)
    rcases this with ⟨j, hj⟩
    have : ∃ z, extendRoot.root ≺ z ∧ z ≺^[l - 1] j := by
      rw [e] at hj
      simpa using hj
    rcases this with ⟨z, hz, hzj⟩
    have : ∃ x, j = embed x := eq_inr_of_root_rel <| HRel.Iterate.unwrap_of_trans_of_pos finHeight_pos hj
    rcases this with ⟨j, rfl⟩
    rcases not_root_of_from_root'₁ hz with (rfl | ⟨z, rfl, Rrz⟩)
    · exact ⟨j, embed_rel_iterate_embed_iff_rel.mp hzj⟩
    use j
    exact HRel.Iterate.constant_trans_of_pos lpos Rrz (embed_rel_iterate_embed_iff_rel.mp hzj)
  · suffices World.finHeight r + 1 ≤ World.finHeight extendRoot.root from this
    apply le_finHeight_iff_relItr.mpr
    rcases exists_terminal r with ⟨j, hj⟩
    exact ⟨j, r, by trivial, embed_rel_iterate_embed_iff_rel.mpr hj⟩

lemma eq_original_finHeight : Frame.World.finHeight (x : F.extendRoot 1) = Frame.World.finHeight x := by
  apply finHeight_eq_iff_relItr.mpr;
  constructor;
  . obtain ⟨y, Rxy⟩ := exists_terminal (i := x);
    use y;
    apply extendRoot.embed_rel_iterate_embed_iff_rel.mpr;
    exact Rxy;
  . rintro (_ | y) Rxy (_ | z);
    . simp;
    . -- TODO: extract no loop lemma (x ≺^[n] i cannot happen where x is original and i is new elements by extension)
      exfalso;
      have : extendRoot.root ≺ (x : F.extendRoot 1) := Frame.root_genaretes'! (F := F.extendRoot 1) x (by simp);
      have : (x : F.extendRoot 1) ≺ x :=
        HRel.Iterate.unwrap_of_trans_of_pos (by omega) $
        HRel.Iterate.comp (m := 1) |>.mp ⟨_, Rxy, by simpa⟩;
      exact Frame.irrefl _ this;
    . apply Frame.asymm;
      exact Frame.root_genaretes'! (F := F.extendRoot 1) y (by simp);
    . have := terminal_rel_finHeight $ extendRoot.embed_rel_iterate_embed_iff_rel.mp Rxy;
      exact extendRoot.embed_rel_embed_iff_rel.not.mpr $ this z;

lemma eq_original_finHeight_root : Frame.World.finHeight (r : F.extendRoot 1) = F.finHeight := eq_original_finHeight

@[grind]
lemma iff_eq_finHeight_eq_original_root {x : F.extendRoot 1} : Frame.World.finHeight x = F.finHeight ↔ x = r := by
  constructor;
  . rcases x with (a | x);
    . intro h;
      have := h ▸ finHeight₁ (F := F);
      simp [Frame.finHeight] at this;
    . intro h;
      suffices x = r by simp [this];
      apply Frame.eq_finHeight_root.mp;
      exact h ▸ Frame.extendRoot.eq_original_finHeight.symm;
  . rintro rfl;
    exact eq_original_finHeight_root;

end extendRoot


namespace pointGenerate

open Classical in
instance [Fintype F] : Fintype (F↾x) := by apply Subtype.fintype;

instance [F.IsTree r] : (F↾x).IsTree ⟨x, by tauto⟩ := by constructor;

axiom eq_original_finHeight (hxy : y = x ∨ x ≺^+ y) : Frame.World.finHeight (F := F↾x) (⟨y, hxy⟩) = Frame.World.finHeight y

end pointGenerate

end Frame


section

variable {M : Model} {r : M.World} [M.IsFiniteTree r] [Fintype M]

lemma finHeight_lt_iff_satisfies_boxbot {i : M} :
    Frame.World.finHeight i < n ↔ i ⊧ □^[n] ⊥ := by
  simp only [Frame.finHeight_lt_iff_relItr, Formula.Kripke.Satisfies.multibox_def]
  simp

lemma finHeight_pos_of_dia {i : M} (hA : i ⊧ ◇ A) : 0 < Frame.World.finHeight i := by
  have : ∃ j, i ≺ j ∧ j ⊧ A := Formula.Kripke.Satisfies.dia_def.mp hA
  rcases this with ⟨j, hj, _⟩
  apply lt_fcwHeight hj (by simp)

@[simp] lemma Model.extendRoot.finHeight₁ :
    (M.extendRoot 1).finHeight = M.finHeight + 1 := Frame.extendRoot.finHeight₁

end

end Kripke

end

end LO.Modal
