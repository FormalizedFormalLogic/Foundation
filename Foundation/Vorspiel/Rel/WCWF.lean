module

public import Foundation.Vorspiel.Rel.CWF

/-!
# Weakly converse well-founded relations
-/

@[expose]
public section

/-- The irreflexive part of a relation. -/
def Rel.IrreflGen {α} (r : Rel α α) : Rel α α := fun x y ↦ r x y ∧ x ≠ y

@[simp, grind =]
lemma Rel.irreflGen_iff {α} {r : Rel α α} {x y : α} : r.IrreflGen x y ↔ r x y ∧ x ≠ y := Iff.rfl

abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded rel.IrreflGen

class IsWeaklyConverseWellFounded (α) (rel : Rel α α) : Prop where
  wcwf : WeaklyConverseWellFounded rel

section

variable {α} {r : Rel α α}

lemma WeaklyConverseWellFounded.has_max [IsWeaklyConverseWellFounded α r] (s : Set α)
    (hs : s.Nonempty) : ∃ m ∈ s, ∀ x ∈ s, r m x → m = x := by
  obtain ⟨m, hm, h⟩ :=
    ConverseWellFounded.iff_has_max.mp (IsWeaklyConverseWellFounded.wcwf (rel := r)) s hs;
  exact ⟨m, hm, fun x hx hmx ↦ by grind⟩;

instance : Std.Irrefl r.IrreflGen := ⟨fun _ h ↦ h.2 rfl⟩

instance [IsTrans α r] [Std.Antisymm r] : IsTrans α r.IrreflGen where
  trans a b c hab hbc :=
    ⟨IsTrans.trans a b c hab.1 hbc.1,
      by rintro rfl; exact hab.2 (Std.Antisymm.antisymm a b hab.1 hbc.1)⟩

instance [Finite α] [IsTrans α r] [Std.Antisymm r] : IsWeaklyConverseWellFounded α r :=
  ⟨Finite.converseWellFounded_of_trans_of_irrefl⟩

end
