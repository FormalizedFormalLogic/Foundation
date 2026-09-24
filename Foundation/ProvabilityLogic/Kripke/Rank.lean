module

public import Foundation.ProvabilityLogic.Kripke.RootedModel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Rank and height
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace Model

section

variable {M : Model κ α} {x y : M.World} {n : ℕ}

lemma exists_chain_of_relItr (h : x ≺^[n] y) :
    ∃ c : ℕ → M.World, c 0 = x ∧ c n = y ∧ ∀ i < n, c i ≺ c (i + 1) := by
  induction n generalizing x with
  | zero => exact ⟨fun _ ↦ x, rfl, h, by simp⟩;
  | succ n ih =>
    obtain ⟨z, Rxz, Rzy⟩ := h;
    obtain ⟨c, hc₀, hcn, hc⟩ := ih Rzy;
    use fun | 0 => x | i + 1 => c i;
    and_intros;
    . rfl;
    . exact hcn;
    . rintro (_ | i) hi;
      . simpa [hc₀] using Rxz;
      . exact hc i (by omega);

lemma rel_of_chain [IsTrans _ M.Rel] {c : ℕ → M.World} (hc : ∀ i < n, c i ≺ c (i + 1))
    {i j : ℕ} (hij : i < j) (hj : j ≤ n) : c i ≺ c j := by
  induction j with
  | zero => omega;
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | rfl;
    . exact IsTrans.trans _ _ _ (ih h (by omega)) (hc j (by omega));
    . exact hc i (by omega);

end

end Model

namespace Model.World

variable {M : Model κ α}

/-- Called `Σ`-reflexivity in the source.

- [KK23]
-/
def IsReflexiveOf (X : FormulaFinset α) (x : M.World) : Prop := ∀ A ∈ X, x ⊩[M] □A 🡒 A

/-- Along `≺`, `□B 🡒 B` fails at most once: it holds at every successor of a world where it
fails. -/
lemma forces_axiomT_of_rel {y z : M.World} {B : Formula α} (Ryz : y ≺ z) (hy : y ⊮[M] □B 🡒 B) :
    z ⊩[M] □B 🡒 B := fun _ ↦ (not_forces_imp.mp hy).1 z Ryz

end Model.World

namespace Model

open Classical

variable {M : Model κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {n : ℕ}

noncomputable def World.rank (x : M.World) : ℕ := cwfHeight (· ≺ ·) x

lemma rank_lt_of_rel (h : x ≺ y) : y.rank < x.rank := cwfHeight_gt_of h

lemma exists_rel_rank_eq_of_lt (h : n < x.rank) : ∃ y, x ≺ y ∧ y.rank = n :=
  exists_cwfHeight_eq_of_lt h

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
  obtain ⟨y, hxy⟩ : ∃ y, x ≺^[x.rank] y := by simpa using rank_lt_iff.not.mp (lt_irrefl _);
  obtain ⟨c, hc₀, -, hc⟩ := exists_chain_of_relItr hxy;
  have hle : ∀ B, ((Finset.Icc 1 x.rank).filter fun i ↦ c i ⊮[M] □B 🡒 B).card ≤ 1 := by
    intro B;
    apply Finset.card_le_one.mpr;
    intro i hi j hj;
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj;
    by_contra hij;
    rcases Nat.lt_or_gt_of_ne hij with hij | hij;
    . exact hj.2 (forces_axiomT_of_rel (rel_of_chain hc hij hj.1.2) hi.2);
    . exact hi.2 (forces_axiomT_of_rel (rel_of_chain hc hij hi.1.2) hj.2);
  have hbad : (X.biUnion fun B ↦ (Finset.Icc 1 x.rank).filter fun i ↦ c i ⊮[M] □B 🡒 B).card <
      (Finset.Icc 1 x.rank).card := calc
    _ ≤ ∑ B ∈ X, ((Finset.Icc 1 x.rank).filter fun i ↦ c i ⊮[M] □B 🡒 B).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ X, 1 := Finset.sum_le_sum fun B _ ↦ hle B
    _ < _ := by simpa using h
  obtain ⟨i, hi, hib⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad;
  simp only [Finset.mem_Icc] at hi;
  use c i;
  and_intros;
  . simpa [hc₀] using rel_of_chain hc (i := 0) (by omega) hi.2;
  . intro B hB;
    by_contra hiB;
    exact hib (Finset.mem_biUnion.mpr ⟨B, hB, by simp [hi, hiB]⟩);

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
