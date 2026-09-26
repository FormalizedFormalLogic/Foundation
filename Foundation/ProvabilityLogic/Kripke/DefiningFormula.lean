module

public import Foundation.ProvabilityLogic.Kripke.Bisimulation
public import Foundation.ProvabilityLogic.Kripke.Rank

/-!
# Defining formulas

## References

- [Bek90, §4, Lemma 7]
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

universe u

variable {κ κ' : Type*} {α : Type u} [Nonempty κ] [Nonempty κ'] [DecidableEq α]

namespace Model

noncomputable section

variable {M : Model κ α} {N : Model κ' α} {P : Finset α} {x : M.World} {w : N.World}

open Classical in
/-- The literals over `P` true at `x`. -/
def World.valuationConj (P : Finset α) (x : M.World) : Formula α :=
  (P.image fun a ↦ if M x a then #a else ∼#a).conj

@[grind .]
lemma World.atoms_valuationConj : (x.valuationConj P).atoms ⊆ P :=
  (FormulaFinset.atoms_conj_subset _).trans <| Finset.biUnion_subset.mpr <|
    Finset.forall_mem_image.mpr <| by grind

@[grind =]
lemma World.forces_valuationConj : w ⊩[_] x.valuationConj P ↔ ∀ a ∈ P, (M x a ↔ N w a) :=
  forces_conj.trans <| Finset.forall_mem_image.trans <| forall₂_congr fun _ _ ↦ by grind

open Classical in
/-- The characteristic formula of `x` over `P`.

- [Bek90, §4]
-/
def World.charFormulaUnder [Fintype M.World] [M.IsGL] (P : Finset α) (x : M.World) : Formula α :=
  x.valuationConj P ⋏
  (Finset.univ.image fun y : { y // x ≺ y } ↦ ◇y.1.charFormulaUnder P).conj ⋏
  □(Finset.univ.image fun y : { y // x ≺ y } ↦ y.1.charFormulaUnder P).disj
termination_by x.rank
decreasing_by all_goals exact rank_lt_of_rel y.2

variable [Fintype M.World] [M.IsGL]

open Classical in
lemma World.charFormulaUnder_def : x.charFormulaUnder P =
    x.valuationConj P ⋏
    (Finset.univ.image fun y : { y // x ≺ y } ↦ ◇y.1.charFormulaUnder P).conj ⋏
    □(Finset.univ.image fun y : { y // x ≺ y } ↦ y.1.charFormulaUnder P).disj := by
  rw [World.charFormulaUnder];

@[grind .]
lemma World.atoms_charFormulaUnder : (x.charFormulaUnder P).atoms ⊆ P := by
  induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
  | h x ih =>
    rw [charFormulaUnder_def];
    simp only [Formula.atoms_and, Formula.atoms_box, Finset.union_subset_iff];
    and_intros;
    · exact atoms_valuationConj;
    · exact (FormulaFinset.atoms_conj_subset _).trans <| Finset.biUnion_subset.mpr <|
        Finset.forall_mem_image.mpr fun y _ ↦ Formula.atoms_dia.trans_subset <| ih y y.2;
    · exact (FormulaFinset.atoms_disj_subset _).trans <| Finset.biUnion_subset.mpr <|
        Finset.forall_mem_image.mpr fun y _ ↦ ih y y.2;

lemma World.forces_charFormulaUnder_iff : w ⊩[_] x.charFormulaUnder P ↔
    (∀ a ∈ P, (M x a ↔ N w a)) ∧
    (∀ y, x ≺ y → ∃ v, w ≺ v ∧ v ⊩[_] y.charFormulaUnder P) ∧
    (∀ v, w ≺ v → ∃ y, x ≺ y ∧ v ⊩[_] y.charFormulaUnder P) := by
  rw [charFormulaUnder_def];
  simp [forces_and, forces_valuationConj, forces_conj, forces_box, forces_disj, forces_dia,
    Subtype.exists];

@[grind .]
lemma World.forces_charFormulaUnder_self : x ⊩[_] x.charFormulaUnder P := by
  induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
  | h x ih =>
    exact forces_charFormulaUnder_iff.mpr
      ⟨fun _ _ ↦ Iff.rfl, fun y R ↦ ⟨y, R, ih y R⟩, fun y R ↦ ⟨y, R, ih y R⟩⟩;

/-- Being forced at a point forcing the characteristic formula is a `P`-bisimulation. -/
def charBisimulationUnder (P : Finset α) (M : Model κ α) [Fintype M.World] [M.IsGL]
    (N : Model κ' α) : M ⇄[P] N where
  toRel x w := w ⊩[_] x.charFormulaUnder P
  atomic ha h := (forces_charFormulaUnder_iff.mp h).1 _ ha
  forth h R := (forces_charFormulaUnder_iff.mp h |>.2.1 _ R).imp fun _ ↦ And.symm
  back h R := (forces_charFormulaUnder_iff.mp h |>.2.2 _ R).imp fun _ ↦ And.symm

end

end Model

namespace RootedModel

/-- `A` defines `M` under `P`: it is over `P`, true at the root of `M`, and true at the root of a
finite GL-model only if its root is `P`-bisimilar to that of `M`.

- [Bek90, §4]
-/
structure IsDefiningFormula (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  root_forces : M.root ⊩[_] A
  unique : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α) [N.IsFiniteGL],
    N.root ⊩[_] A → ∃ Bi : M.toModel ⇄[P] N.toModel, Bi M.root N.root

/-- - [Bek90, Lemma 7] -/
theorem exists_isDefiningFormula {M : RootedModel κ α} [M.IsFiniteGL] (P : Finset α) :
    ∃ A, M.IsDefiningFormula P A := by
  have : Fintype M.World := Fintype.ofFinite _;
  use World.charFormulaUnder (M := M.toModel) P M.root;
  exact ⟨atoms_charFormulaUnder, forces_charFormulaUnder_self,
    fun N _ h ↦ ⟨charBisimulationUnder P M.toModel N.toModel, h⟩⟩;

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
