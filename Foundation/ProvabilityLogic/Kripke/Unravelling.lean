module

public import Foundation.ProvabilityLogic.Kripke.Bisimulation
public import Foundation.ProvabilityLogic.Kripke.RootedModel
public import Mathlib.Data.Fintype.Powerset

/-!
# Tree unravelling

## References

- [CZ97]
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

/-- The last point of the chain. -/
def tip : M.World := x.1.head fun h ↦ by simpa [h] using x.2.1

end unravelling.World

instance : Nonempty (unravelling.World M) := ⟨⟨[M.root], List.suffix_refl _, by simp⟩⟩

/-- The unravelling of `M`: chains from the root, ordered by proper extension. -/
def unravelling : RootedModel (unravelling.World M) α where
  Rel' x y := x.1 <:+ y.1 ∧ x.1.length < y.1.length
  Val' x p := M x.tip p
  root := ⟨[M.root], List.suffix_refl _, by simp⟩
  root_rel x hx :=
    ⟨x.2.1, x.2.1.length_le.lt_of_ne fun h ↦ hx <| Subtype.ext (x.2.1.eq_of_length h).symm⟩

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
    rcases List.suffix_or_suffix_of_suffix h₁.1 h₂.1 with h | h <;>
      rcases h.length_le.lt_or_eq with hl | hl <;> simp_all [Subtype.ext_iff, h.eq_of_length]

instance [M.IsFiniteGL] : M.unravelling.IsFiniteGL where
  finite := by
    have : Std.Irrefl (flip M.Rel) := ⟨Std.Irrefl.irrefl (r := M.Rel)⟩;
    have : Std.Antisymm (flip M.Rel) :=
      ⟨fun _ _ h h' ↦ absurd (IsTrans.trans (r := M.Rel) _ _ _ h h') (Std.Irrefl.irrefl _)⟩;
    exact Finite.of_injective (fun x : M.unravelling.World ↦ {a | a ∈ x.1}) fun x y h ↦
      Subtype.ext <| x.2.2.eq_of_mem_iff y.2.2 <| Set.ext_iff.mp h;

/-- The map to the last point is a pseudo-epimorphism. -/
def tipMap [IsTrans _ M.Rel] : M.unravelling.toModel →ₚ M.toModel where
  toFun x := x.tip
  forth {x y} h := by
    obtain ⟨y, hy⟩ := y;
    obtain ⟨t, rfl⟩ := h.1;
    rcases t with _ | ⟨a, t⟩;
    · simp at h;
    · exact List.rel_of_pairwise_cons hy.2 <| List.mem_append_right _ <| List.head_mem _;
  back {x v} h := by
    obtain ⟨_ | ⟨w, l⟩, hx₁, hx₂⟩ := x;
    · simp at hx₁;
    · have : ∀ b ∈ w :: l, b ≺ v := List.forall_mem_cons.mpr
        ⟨h, fun _ hb ↦ _root_.trans (r := M.Rel) (List.rel_of_pairwise_cons hx₂ hb) h⟩;
      use ⟨v :: w :: l, hx₁.trans (List.suffix_cons _ _), .cons this hx₂⟩;
      exact ⟨rfl, by simp⟩;
  atomic := Iff.rfl

lemma forces_root_iff [IsTrans _ M.Rel] {A : Formula α} :
    M.unravelling.root ⊩ A ↔ M.root ⊩[M.toModel] A :=
  tipMap.forces_iff

end unravelling

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
