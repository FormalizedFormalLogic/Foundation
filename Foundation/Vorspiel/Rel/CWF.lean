module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Rel

/-!
# Converse well-founded relations

`ConverseWellFounded`, `IsConverseWellFounded` and the height function `cwfHeight` of a
point of a finite converse well-founded relation.
-/

@[expose]
public section

section

abbrev ConverseWellFounded {α} (rel : Rel α α) := WellFounded $ flip rel

class IsConverseWellFounded (α) (rel : Rel α α) : Prop where cwf : ConverseWellFounded rel

end



section

variable {α} {R : Rel α α}

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded R ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip];

theorem Finite.converseWellFounded_of_trans_of_irrefl [Finite α] [IsTrans α R] [Std.Irrefl R] : ConverseWellFounded R := by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, Std.Irrefl.irrefl]⟩;

instance [Finite α] [IsTrans α R] [Std.Irrefl R] : IsConverseWellFounded _ R :=
  ⟨Finite.converseWellFounded_of_trans_of_irrefl⟩

variable (R)

open Classical in
noncomputable def cwfHeight [IsConverseWellFounded α R] [Fintype α] : α → ℕ :=
  WellFounded.fix (r := flip R) (C := fun _ ↦ ℕ) IsConverseWellFounded.cwf fun x ih ↦
    Finset.univ.sup fun y : {y : α // R x y} ↦ ih y y.prop + 1

variable {R}

section cwfHeight

variable [Fintype α] [IsConverseWellFounded α R]

open Classical

lemma cwfHeight_eq (a : α) :
  cwfHeight R a = Finset.sup {x : α | R a x} (fun b ↦ cwfHeight R b + 1) := by
  have h : cwfHeight R a = Finset.univ.sup fun b : {y : α // R a y} ↦ cwfHeight R b + 1 :=
    WellFounded.fix_eq _ _ a;
  suffices
    Finset.univ.sup (fun b : {y : α // R a y} ↦ cwfHeight R b + 1) =
    Finset.sup {y : α | R a y} fun b ↦ cwfHeight R b + 1 from h.trans this;
  apply eq_of_le_of_ge;
  . apply Finset.sup_le;
    intro b _;
    exact Finset.le_sup (f := fun b ↦ cwfHeight R b + 1) (by simp [b.prop]);
  . apply Finset.sup_le;
    intro b hb;
    simpa using Finset.le_sup (f := fun b : {y : α // R a y} ↦ cwfHeight R b + 1)
      (b := ⟨b, by simpa using hb⟩) (s := Finset.univ) (by simp);

lemma cwfHeight_gt_of {a b} :
  R a b → cwfHeight R a > cwfHeight R b := fun h ↦ calc
  cwfHeight R a = Finset.sup {x : α | R a x} fun b ↦ cwfHeight R b + 1 := cwfHeight_eq a
  _               ≥ cwfHeight R b + 1 := Finset.le_sup (f := fun b ↦ cwfHeight R b + 1) (by simp [h])

lemma cwfHeight_le {a : α}
  (h : ∀ b, R a b → cwfHeight R b < n) : cwfHeight R a ≤ n := by
  rw [cwfHeight_eq];
  apply Finset.sup_le;
  intro b hab;
  exact h b (by simpa using hab);

lemma lt_cwfHeight {a : α} (hb : R a b) (h : n ≤ cwfHeight R b) : n < cwfHeight R a := by
  have : cwfHeight R b < cwfHeight R a := by
    apply Nat.lt_of_succ_le;
    rw [cwfHeight_eq a];
    exact Finset.le_sup (s := {x : α | R a x})
      (f := fun b ↦ cwfHeight R b + 1) (b := b) (by simp [hb]);
  exact lt_of_le_of_lt h this;

end cwfHeight

end


section

variable {α} {r : Rel α α}

instance [Std.Irrefl (flip r)] : Std.Irrefl r := by
  constructor;
  have := Std.Irrefl.irrefl (r := flip r);
  simpa;

lemma ConverseWellFounded.irrefl [IsConverseWellFounded α r] : Std.Irrefl r := by
  have := WellFounded.irrefl (r := flip r) IsConverseWellFounded.cwf;
  infer_instance;

end
