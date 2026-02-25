module

public import Foundation.Modal.Kripke.ExtendRoot

@[expose] public section

namespace LO.Modal

noncomputable section

namespace Kripke

variable {φ ψ : Formula ℕ}
         {F : Frame} [Fintype F] [F.IsConverseWellFounded] [F.IsTransitive] {x y i j : F}

def Frame.rank [Fintype F] [F.IsConverseWellFounded] [F.IsTransitive] (i : F) : ℕ := fcwHeight (· ≺ ·) i

def Frame.height (F : Frame) [Fintype F] [F.IsConverseWellFounded] [F.IsTransitive] [F.IsRooted] : ℕ := Frame.rank F.root.1

namespace Frame

lemma rank_lt_of_rel (hij : i ≺ j) : F.rank i > Frame.rank j := fcwHeight_gt_of hij

lemma exists_of_lt_height (hn : n < F.rank i) : ∃ j : F, i ≺ j ∧ Frame.rank j = n := fcwHeight_lt hn

lemma height_lt_iff_relItr {i : F} :
    F.rank i < n ↔ ∀ j, ¬i ≺^[n] j  := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices F.rank i ≤ n ↔ ∀ j : F, i ≺ j → Frame.rank j < n by
      calc
        F.rank i < n + 1
          ↔ F.rank i ≤ n := Nat.lt_add_one_iff
        _ ↔ ∀ j, i ≺ j → Frame.rank j < n := this
        _ ↔ ∀ j, i ≺ j → ∀ k, ¬j ≺^[n] k := by simp [height_lt_iff_relItr (n := n)]
        _ ↔ ∀ k j, i ≺ j → ¬j ≺^[n] k    := by grind
        _ ↔ ∀ j, ¬i ≺^[n + 1] j  := by simp
    constructor
    · exact fun h j hij ↦ lt_of_lt_of_le (fcwHeight_gt_of hij) h
    · exact fcwHeight_le

lemma le_height_iff_relItr {i : F} :
    n ≤ F.rank i ↔ ∃ j, i ≺^[n] j := calc
  n ≤ F.rank i ↔ ¬F.rank i < n := Iff.symm Nat.not_lt
  _                           ↔ ∃ j, i ≺^[n] j := by simp [height_lt_iff_relItr]

lemma height_eq_iff_relItr {i : F} :
    F.rank i = n ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := calc
  F.rank i = n
    ↔ F.rank i < n + 1 ∧ n ≤ F.rank i := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge
  _ ↔ (∀ j, ¬i ≺^[n + 1] j) ∧ (∃ j, i ≺^[n] j) := by simp [height_lt_iff_relItr, le_height_iff_relItr]
  _ ↔ (∀ k j, i ≺^[n] j → ¬j ≺ k) ∧ (∃ j, i ≺^[n] j) := by simp only [Rel.Iterate.forward, not_exists, not_and]
  _ ↔ (∃ j, i ≺^[n] j) ∧ (∀ j, i ≺^[n] j → ∀ k, ¬j ≺ k) := by grind

lemma exists_rank_terminal (i : F) : ∃ j, i ≺^[F.rank i] j := le_height_iff_relItr.mp (by simp)

lemma terminal_rel_height (h : x ≺^[rank x] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices rank x + 1 ≤ rank x by omega;
  exact le_height_iff_relItr.mpr ⟨z, Rel.Iterate.forward.mpr ⟨y, h, Ryz⟩⟩;


variable [F.IsRooted]

@[grind <=]
lemma rank_lt_whole_height {i : F} (hi : F.root ≺ i) : F.rank i < F.height := fcwHeight_gt_of hi

@[grind .]
lemma rank_le_whole_height (i : F) : F.rank i ≤ F.height := by
  by_cases hi : i = F.root
  · subst hi; rfl;
  · apply le_of_lt;
    apply rank_lt_whole_height;
    grind;

lemma eq_height_root : Frame.rank x = F.height ↔ x = F.root := by
  constructor;
  . rintro h;
    contrapose! h;
    apply Nat.ne_of_lt;
    apply Frame.rank_lt_whole_height;
    grind;
  . tauto;

namespace extendRoot

omit [F.IsRooted] in
lemma eq_extendRoot_height_rank_extendRoot_root : (F.extendRoot n).height = Frame.rank (F.extendRoot n).root.1 := by
  dsimp [Frame.height];

@[simp]
lemma height_pos : 0 < (Frame.extendRoot F n).height := by
  rw [eq_extendRoot_height_rank_extendRoot_root];
  apply lt_fcwHeight ?_ (by simp);
  · exact ↑F.root.1;
  . grind;

@[simp]
lemma height_succ : (F.extendRoot 1).height = F.height + 1 := by
  let l := (F.extendRoot 1).height;
  let r := (Frame.extendRoot F 1).root;
  suffices l ≤ F.height + 1 ∧ F.height < l by omega;

  constructor
  · suffices l - 1 ≤ F.height from Nat.le_add_of_sub_le this;
    apply le_height_iff_relItr.mpr;
    wlog lpos : 0 < l - 1;
    . use F.root;
      simp [(show l - 1 = 0 by omega)];

    have el : l = (l - 1) + 1 := by
      symm;
      exact Nat.sub_add_cancel $ Frame.extendRoot.height_pos;

    obtain ⟨j, Rrj⟩ : ∃ j, r.1 ≺^[l] j := exists_rank_terminal _;
    obtain ⟨z, Rrz, Rzj⟩ : ∃ z, r.1 ≺ z ∧ z ≺^[l - 1] j := Rel.Iterate.iff_succ.mp (el ▸ Rrj);
    obtain ⟨j, rfl⟩ : ∃ x, j = embed x :=
      eq_original_of_rel_extendRoot_root₁ j
      $ Rel.Iterate.unwrap_of_trans_of_pos height_pos Rrj;

    use j;
    by_cases ez : z = F.root;
    . exact embed_rel_iterate_embed_iff_rel.mp $ ez ▸ Rzj;
    . obtain ⟨z₀, rfl⟩ := eq_original_of_rel_extendRoot_root₁ z (by grind);
      exact Rel.Iterate.constant_trans_of_pos lpos (by grind) (embed_rel_iterate_embed_iff_rel.mp Rzj);

  · suffices F.height + 1 ≤ rank r.1 from this;
    apply le_height_iff_relItr.mpr;
    rcases exists_rank_terminal F.root.1 with ⟨j, hj⟩;
    use j, F.root;
    constructor;
    . grind;
    . exact embed_rel_iterate_embed_iff_rel.mpr hj;

omit [F.IsRooted] in
lemma eq_original_height : Frame.rank (x : F.extendRoot 1) = Frame.rank x := by
  apply height_eq_iff_relItr.mpr;
  constructor;
  . obtain ⟨y, Rxy⟩ := exists_rank_terminal (i := x);
    use y;
    apply extendRoot.embed_rel_iterate_embed_iff_rel.mpr;
    exact Rxy;
  . rintro (_ | y) Rxy (_ | z);
    . simp;
    . -- TODO: extract no loop lemma (x ≺^[n] i cannot happen where x is original and i is new elements by extension)
      exfalso;
      have : (F.extendRoot 1).root ≺ (x : F.extendRoot 1) := by grind;
      have : (x : F.extendRoot 1) ≺ x :=
        Rel.Iterate.unwrap_of_trans_of_pos (by omega) $
        Rel.Iterate.comp (m := 1) |>.mp ⟨_, Rxy, by simpa⟩;
      exact Frame.irrefl _ this;
    . apply Frame.asymm;
      grind;
    . have := terminal_rel_height $ extendRoot.embed_rel_iterate_embed_iff_rel.mp Rxy;
      exact extendRoot.embed_rel_embed_iff_rel.not.mpr $ this z;

lemma eq_original_height_root : (F.extendRoot 1).rank F.root = F.height := eq_original_height

omit [F.IsRooted] in
@[grind =]
lemma iff_eq_height_eq_original_root [F.IsRooted] {x : F.extendRoot 1} : Frame.rank x = F.height ↔ x = F.root.1 := by
  constructor;
  . rcases x with (a | x);
    . intro h;
      have := h ▸ height_succ (F := F);
      simp [Frame.height, Frame.root, default] at this;
    . intro h;
      suffices x = F.root.1 by simp [this];
      apply Frame.eq_height_root.mp;
      exact h ▸ Frame.extendRoot.eq_original_height.symm;
  . rintro rfl;
    exact eq_original_height_root;

end extendRoot


namespace pointGenerate

open Classical in
instance [Fintype F] : Fintype (F↾x) := by apply Subtype.fintype;

instance [F.IsRooted] [F.IsTree] : (F↾x).IsTree := by constructor;

axiom eq_original_height (hxy : y = x ∨ x ≺ y) : Frame.rank (F := F↾x) (⟨y, hxy⟩) = Frame.rank y

end pointGenerate

end Frame


section

variable {M : Model} [Fintype M] [M.IsTransitive] [M.IsConverseWellFounded]

lemma height_lt_iff_satisfies_boxbot {i : M} :
    M.rank i < n ↔ i ⊧ □^[n] ⊥ := by
  simp only [Frame.height_lt_iff_relItr, Formula.Kripke.Satisfies.boxItr_def]
  simp

lemma height_pos_of_dia {i : M} (hA : i ⊧ ◇A) : 0 < M.rank i := by
  have : ∃ j, i ≺ j ∧ j ⊧ A := Formula.Kripke.Satisfies.dia_def.mp hA
  rcases this with ⟨j, hj, _⟩
  apply lt_fcwHeight hj (by simp)

@[simp]
lemma Model.extendRoot.height₁ [M.IsRooted] : (Frame.extendRoot M.toFrame 1).height = (M.height) + 1 := Frame.extendRoot.height_succ

end

end Kripke

end

end LO.Modal
end
