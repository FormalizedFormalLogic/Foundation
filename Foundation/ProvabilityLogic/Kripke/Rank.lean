module

public import Foundation.ProvabilityLogic.Kripke.RootedModel

/-!
# Rank and height
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace Model

open Classical

variable {M : Model κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {n : ℕ}

noncomputable def World.rank (x : M.World) : ℕ := cwfHeight (· ≺ ·) x

lemma rank_lt_of_rel (h : x ≺ y) : y.rank < x.rank := cwfHeight_gt_of h

lemma rank_lt_iff : x.rank < n ↔ ∀ y, x ⊀^[n] y := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    calc
      _ ↔ x.rank ≤ n                 := Nat.lt_add_one_iff
      _ ↔ ∀ y, x ≺ y → y.rank < n    :=
        ⟨fun h _ Rxy ↦ lt_of_lt_of_le (rank_lt_of_rel Rxy) h, cwfHeight_le⟩
      _ ↔ ∀ y, x ⊀^[n + 1] y         := by simp only [notRelItr_iff, ih, relItr_succ]; grind;

lemma forces_boxItr_bot_iff : x ⊩[M] □^[n]⊥ ↔ x.rank < n := by
  simp [forces_boxItr, rank_lt_iff];

lemma rank_pos_of_forces_dia {A : Formula α} (h : x ⊩[M] ◇A) : 0 < x.rank := by
  obtain ⟨y, Rxy, -⟩ := forces_dia.mp h;
  exact lt_of_le_of_lt (Nat.zero_le _) (rank_lt_of_rel Rxy);

/-- - [AB05, Lemma 26] -/
lemma exists_isReflexiveOf_of_card_lt_rank {X : FormulaFinset α} (h : X.card < x.rank) :
    ∃ y, x ≺ y ∧ y.IsReflexiveOf X := by
  have hsucc : ∀ {x : M.World} {n}, n < x.rank → ∃ y, x ≺ y ∧ n ≤ y.rank := by
    intro x n h;
    by_contra! hy;
    exact absurd (cwfHeight_le hy) (by simpa [World.rank] using h);
  induction hn : X.card generalizing X x with
  | zero =>
    obtain ⟨y, Rxy, -⟩ := hsucc (hn ▸ h);
    exact ⟨y, Rxy, by simp_all [World.IsReflexiveOf]⟩;
  | succ n ih =>
    obtain ⟨z, Rxz, hz⟩ := hsucc (hn ▸ h);
    by_cases hzX : z.IsReflexiveOf X;
    . exact ⟨z, Rxz, hzX⟩;
    . obtain ⟨B, hB, hzB⟩ : ∃ B ∈ X, z ⊩[M] □B ∧ z ⊮[M] B := by
        simpa [World.IsReflexiveOf, forces_imp] using hzX;
      obtain ⟨y, Rzy, hy⟩ := ih (X := X.erase B) (x := z) (by grind) (by grind);
      use y, IsTrans.trans _ _ _ Rxz Rzy;
      intro C hC _;
      by_cases hCB : C = B;
      . exact hCB ▸ hzB.1 y Rzy;
      . exact hy C (by simp_all) (by assumption);

end Model

namespace RootedModel

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {x : M.World} {n : ℕ}

noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ :=
  Model.World.rank (M := M.toModel) M.root

lemma rank_lt_height (h : M.root ≺ x) : Model.World.rank (M := M.toModel) x < M.height :=
  Model.rank_lt_of_rel h

lemma rank_le_height : Model.World.rank (M := M.toModel) x ≤ M.height := by
  by_cases hx : x = M.root;
  . subst hx; rfl;
  . exact (rank_lt_height (M.root_rel x hx)).le;

lemma root_forces_boxItr_bot_iff : M.root ⊩[M.toModel] □^[n]⊥ ↔ M.height < n :=
  Model.forces_boxItr_bot_iff

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
