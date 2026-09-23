module

public import Foundation.ProvabilityLogic.Kripke.Rank
public import Mathlib.Data.Fintype.Option

/-!
# Root extension

The extension of a rooted model by a new root below the old one.
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace RootedModel

variable (M : RootedModel κ α)

/-- `M` with a new root below the old one, which forces the same atoms as the old root. -/
def extendRoot : RootedModel (Option κ) α where
  Rel' x y := match x, y with
    | some x, some y => M.Rel x y
    | none, some _ => True
    | _, none => False
  Val' x a := match x with
    | some x => M.Val x a
    | none => M.Val M.root a
  root := none
  root_rel x hx := by
    rcases x with _ | x;
    . exact absurd rfl hx;
    . trivial;

namespace extendRoot

variable {M} {x y : M.World} {A : Formula α}

@[simp] lemma rel_some_some : (M.extendRoot.Rel (some x) (some y)) ↔ M.Rel x y := Iff.rfl

@[simp] lemma rel_none_some : M.extendRoot.Rel none (some x) := trivial

@[simp] lemma not_rel_none {x : M.extendRoot.World} : ¬M.extendRoot.Rel x none := by
  rcases x with _ | _ <;> exact id

instance [IsTrans _ M.Rel] : IsTrans _ M.extendRoot.Rel where
  trans x y z := by
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;>
    simp only [rel_some_some, rel_none_some, not_rel_none, IsEmpty.forall_iff, implies_true,
      forall_const];
    exact IsTrans.trans _ _ _

instance [Std.Irrefl M.Rel] : Std.Irrefl M.extendRoot.Rel where
  irrefl x := by
    rcases x with _ | x;
    . exact not_rel_none;
    . exact Std.Irrefl.irrefl (r := M.Rel) x;

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ M.extendRoot.Rel where
  cwf := by
    have hsome : ∀ x : M.World, Acc (flip M.extendRoot.Rel) (some x) := by
      intro x;
      induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
      | h x ih =>
        constructor;
        rintro (_ | y) h;
        . exact absurd h not_rel_none;
        . exact ih y h;
    constructor;
    rintro (_ | x);
    . constructor;
      rintro (_ | y) h;
      . exact absurd h not_rel_none;
      . exact hsome y;
    . exact hsome x;

instance [M.IsGL] : M.extendRoot.IsGL where

instance [Fintype M.World] : Fintype M.extendRoot.World := inferInstanceAs (Fintype (Option κ))

lemma forces_some : some x ⊩[M.extendRoot.toModel] A ↔ x ⊩[M.toModel] A := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    constructor;
    . intro h y Rxy;
      exact ih.mp (h (some y) Rxy);
    . rintro h (_ | y) Rxy;
      . exact absurd Rxy not_rel_none;
      . exact ih.mpr (h y Rxy);

lemma relItr_some_iff {n : ℕ} {y : M.extendRoot.World} :
    M.extendRoot.RelItr n (some x) y ↔ ∃ y', y = some y' ∧ M.RelItr n x y' := by
  induction n generalizing x with
  | zero => simp [eq_comm];
  | succ n ih =>
    simp only [Model.relItr_succ];
    constructor;
    . rintro ⟨(_ | z), Rxz, Rzy⟩;
      . exact absurd Rxz not_rel_none;
      . obtain ⟨y', rfl, h⟩ := ih.mp Rzy;
        exact ⟨y', rfl, z, Rxz, h⟩;
    . rintro ⟨y', rfl, z, Rxz, Rzy⟩;
      exact ⟨some z, Rxz, ih.mpr ⟨y', rfl, Rzy⟩⟩;

variable [Fintype M.World] [M.IsGL]

lemma rank_some : Model.World.rank (M := M.extendRoot.toModel) (some x) = Model.World.rank (M := M.toModel) x := by
  have h : ∀ n, Model.World.rank (M := M.extendRoot.toModel) (some x) < n ↔
      Model.World.rank (M := M.toModel) x < n := by
    intro n;
    simp only [Model.rank_lt_iff, relItr_some_iff];
    grind;
  exact le_antisymm (Nat.le_of_lt_succ ((h _).mpr (Nat.lt_succ_self _)))
    (Nat.le_of_lt_succ ((h _).mp (Nat.lt_succ_self _)));

lemma height_extendRoot : M.extendRoot.height = M.height + 1 := by
  apply le_antisymm;
  . apply cwfHeight_le;
    rintro (_ | y) h;
    . exact absurd h not_rel_none;
    . have := rank_some (M := M) (x := y);
      have := RootedModel.rank_le_height (M := M) (x := y);
      simp only [Model.World.rank] at *;
      omega;
  . exact Nat.succ_le_of_lt <| lt_cwfHeight (b := some M.root) trivial <| by
      have := rank_some (M := M) (x := M.root);
      simp only [RootedModel.height, Model.World.rank] at *;
      omega;

end extendRoot

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
