module

public import Foundation.ProvabilityLogic.Kripke.Bisimulation
public import Foundation.ProvabilityLogic.Kripke.Graft
public import Mathlib.Data.Fintype.Powerset

/-!
# Tree unravelling

Unravelling a rooted model into a tree is folklore in modal logic; its commutation with grafting
is used in the source.

## References

- [Bek90, Lemma 8]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace Model

/-- The predecessors of every point are linearly ordered. -/
class IsTree (M : Model κ α) : Prop where
  tree {x y z : M.World} : x ≺ z → y ≺ z → x = y ∨ x ≺ y ∨ y ≺ x

end Model

namespace RootedModel

variable (M : RootedModel κ α)

/-- `M.Rel`-chains from the root, listed from the last point back to the root. -/
abbrev unravelling.World : Type _ :=
  { l : List M.World // [M.root] <:+ l ∧ l.Pairwise (flip M.Rel) }

namespace unravelling.World

variable {M} (x : unravelling.World M)

lemma ne_nil : x.1 ≠ [] := by
  intro h;
  simpa [h] using x.2.1;

/-- The last point of the chain. -/
def tip : M.World := x.1.head x.ne_nil

end unravelling.World

instance : Nonempty (unravelling.World M) := ⟨⟨[M.root], List.suffix_refl _, by simp⟩⟩

/-- The unravelling of `M`: chains from the root, ordered by proper extension. -/
def unravelling : RootedModel (unravelling.World M) α where
  Rel' x y := x.1 <:+ y.1 ∧ x.1.length < y.1.length
  Val' x p := M.Val x.tip p
  root := ⟨[M.root], List.suffix_refl _, by simp⟩
  root_rel x hx := by
    use x.2.1;
    rcases x.2.1.length_le.lt_or_eq with h | h;
    . exact h;
    . exact absurd (Subtype.ext (x.2.1.eq_of_length h).symm) hx;

namespace unravelling

variable {M}

@[simp, grind =]
lemma rel_iff {x y : M.unravelling.World} : x ≺ y ↔ x.1 <:+ y.1 ∧ x.1.length < y.1.length :=
  Iff.rfl

@[simp] lemma root_val : M.unravelling.root.1 = [M.root] := rfl

instance : IsTrans _ M.unravelling.Rel where
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

instance : Std.Irrefl M.unravelling.Rel where
  irrefl _ h := lt_irrefl _ h.2

instance : M.unravelling.IsTree where
  tree {x y z} h₁ h₂ := by
    rcases List.suffix_or_suffix_of_suffix h₁.1 h₂.1 with h | h;
    . rcases h.length_le.lt_or_eq with hl | hl;
      . exact .inr (.inl ⟨h, hl⟩);
      . exact .inl (Subtype.ext (h.eq_of_length hl));
    . rcases h.length_le.lt_or_eq with hl | hl;
      . exact .inr (.inr ⟨h, hl⟩);
      . exact .inl (Subtype.ext (h.eq_of_length hl).symm);

instance [M.IsFiniteGL] : M.unravelling.IsFiniteGL where
  finite := by
    have : Std.Irrefl (flip M.Rel) := ⟨fun x ↦ Std.Irrefl.irrefl (r := M.Rel) x⟩;
    have : Std.Antisymm (flip M.Rel) :=
      ⟨fun x y h h' ↦ absurd (IsTrans.trans (r := M.Rel) _ _ _ h h') (Std.Irrefl.irrefl _)⟩;
    apply Finite.of_injective (fun x : M.unravelling.World ↦ {a | a ∈ x.1});
    intro x y h;
    exact Subtype.ext (x.2.2.eq_of_mem_iff y.2.2 fun a ↦ by simpa using congrArg (a ∈ ·) h);

/-- The map to the last point is a pseudo-epimorphism. -/
def tipMap [IsTrans _ M.Rel] : M.unravelling.toModel →ₚ M.toModel where
  toFun x := x.tip
  forth {x y} h := by
    obtain ⟨y, hy⟩ := y;
    obtain ⟨t, rfl⟩ := h.1;
    rcases t with _ | ⟨a, t⟩;
    . simp at h;
    . exact List.rel_of_pairwise_cons hy.2 (List.mem_append_right _ (List.head_mem _));
  back {x v} h := by
    obtain ⟨_ | ⟨w, l⟩, hx₁, hx₂⟩ := x;
    . simp at hx₁;
    . have : ∀ b ∈ w :: l, b ≺ v := by
        simp only [List.mem_cons, forall_eq_or_imp];
        exact ⟨h, fun b hb ↦ IsTrans.trans _ _ _ (List.rel_of_pairwise_cons hx₂ hb) h⟩;
      exact ⟨⟨v :: w :: l, hx₁.trans (List.suffix_cons _ _), List.pairwise_cons.mpr ⟨this, hx₂⟩⟩,
        rfl, List.suffix_cons _ _, by simp⟩;
  atomic := Iff.rfl

lemma forces_root_iff [IsTrans _ M.Rel] {A : Formula α} :
    M.unravelling.root ⊩[M.unravelling.toModel] A ↔ M.root ⊩[M.toModel] A :=
  tipMap.forces_iff

/-- The chain from the root to `a`, which covers the root. -/
def coverPoint (a : M.NonRoot) : M.unravelling.NonRoot :=
  ⟨⟨[a.1, M.root], List.suffix_cons _ _, by simpa [flip] using M.root_rel a.1 a.2⟩,
    fun h ↦ by simpa using congrArg (·.1.length) h⟩

lemma eq_root_of_rel_coverPoint {a : M.NonRoot} {x : M.unravelling.World}
    (h : x ≺ (coverPoint a).1) : x = M.unravelling.root := by
  have := x.2.1.length_le;
  have : x.1.length < 2 := h.2;
  simp only [List.length_singleton] at *;
  exact Subtype.ext (x.2.1.eq_of_length (by simp; omega)).symm;

lemma eq_root_of_tip_eq_root [Std.Irrefl M.Rel] {x : M.unravelling.World}
    (h : x.tip = M.root) : x = M.unravelling.root := by
  obtain ⟨_ | ⟨w, l⟩, hx₁, hx₂⟩ := x;
  . simp at hx₁;
  . have hw : w = M.root := h;
    subst hw;
    rcases l with _ | ⟨v, l⟩;
    . rfl;
    . have : M.root ∈ v :: l := by
        rcases List.suffix_cons_iff.mp hx₁ with h' | h';
        . simp at h';
        . exact h'.subset (by simp);
      exact absurd (List.rel_of_pairwise_cons hx₂ this) (Std.Irrefl.irrefl (r := M.Rel) _);

variable [IsTrans _ M.Rel] [Std.Irrefl M.Rel] {ι : Type*} [LT ι]

/-- Unravelling commutes with grafting at a point covering the root.

- [Bek90, Lemma 8]
-/
def graftTipMap (a : M.NonRoot) (ι : Type*) [LT ι] :
    (M.unravelling.graft (coverPoint a) ι).toModel →ₚ (M.graft a ι).toModel where
  toFun
    | .inl t => .inl t.tip
    | .inr i => .inr i
  forth {x y} R := by
    rcases x with x | i <;> rcases y with y | j;
    . exact tipMap.forth R;
    . subst R;
      rfl;
    . rcases R with rfl | R;
      . exact .inl rfl;
      . exact .inr (tipMap.forth R);
    . exact R;
  back {x v} h := by
    rcases x with x | i <;> rcases v with w | j;
    . obtain ⟨y, rfl, R⟩ := tipMap.back h;
      exact ⟨.inl y, rfl, R⟩;
    . exact ⟨.inr j, rfl, eq_root_of_tip_eq_root h⟩;
    . rcases h with rfl | h;
      . exact ⟨.inl (coverPoint a).1, rfl, .inl rfl⟩;
      . obtain ⟨y, rfl, R⟩ := tipMap.back (x := (coverPoint a).1) h;
        exact ⟨.inl y, rfl, .inr R⟩;
    . exact ⟨.inr j, rfl, h⟩;
  atomic {x} := by
    rcases x with x | i <;> exact Iff.rfl;

lemma forces_graft_root_iff {a : M.NonRoot} {A : Formula α} :
    (M.unravelling.graft (coverPoint a) ι).root
      ⊩[(M.unravelling.graft (coverPoint a) ι).toModel] A ↔
    (M.graft a ι).root ⊩[(M.graft a ι).toModel] A :=
  (graftTipMap a ι).forces_iff

end unravelling

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
