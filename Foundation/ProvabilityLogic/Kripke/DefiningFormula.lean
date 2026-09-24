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
  (P.image fun a ↦ if M.Val x a then #a else ∼#a).conj

@[grind .]
lemma World.atoms_valuationConj : (x.valuationConj P).atoms ⊆ P := fun a ha ↦ by
  have := FormulaFinset.atoms_conj_subset _ ha;
  simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at this;
  obtain ⟨_, ⟨b, hb, rfl⟩, ha⟩ := this;
  split at ha <;> simp_all;

@[grind =]
lemma World.forces_valuationConj : w ⊩[N] x.valuationConj P ↔ ∀ a ∈ P, (M.Val x a ↔ N.Val w a) := by
  simp only [World.valuationConj, forces_conj, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂];
  apply forall₂_congr;
  intro a _;
  split <;> simp_all [forces_neg];

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
    rw [World.charFormulaUnder_def];
    intro a ha;
    simp only [Formula.atoms_and, Formula.atoms_box, Finset.mem_union] at ha;
    rcases ha with ha | ha | ha;
    · exact World.atoms_valuationConj ha;
    · have := FormulaFinset.atoms_conj_subset _ ha;
      simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at this;
      obtain ⟨_, ⟨y, -, rfl⟩, ha⟩ := this;
      exact ih y y.2 (by simpa using ha);
    · have := FormulaFinset.atoms_disj_subset _ ha;
      simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at this;
      obtain ⟨_, ⟨y, -, rfl⟩, ha⟩ := this;
      exact ih y y.2 ha;

lemma World.forces_charFormulaUnder_iff : w ⊩[N] x.charFormulaUnder P ↔
    (∀ a ∈ P, (M.Val x a ↔ N.Val w a)) ∧
    (∀ y, x ≺ y → ∃ v, w ≺ v ∧ v ⊩[N] y.charFormulaUnder P) ∧
    (∀ v, w ≺ v → ∃ y, x ≺ y ∧ v ⊩[N] y.charFormulaUnder P) := by
  rw [World.charFormulaUnder_def];
  simp [forces_and, World.forces_valuationConj, forces_conj, forces_box, forces_disj, forces_dia,
    Subtype.exists];

@[grind .]
lemma World.forces_charFormulaUnder_self : x ⊩[M] x.charFormulaUnder P := by
  induction x using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
  | h x ih =>
    exact World.forces_charFormulaUnder_iff.mpr
      ⟨fun _ _ ↦ Iff.rfl, fun y R ↦ ⟨y, R, ih y R⟩, fun y R ↦ ⟨y, R, ih y R⟩⟩;

/-- Being forced at a point forcing the characteristic formula is a `P`-bisimulation. -/
def charBisimulationUnder (P : Finset α) (M : Model κ α) [Fintype M.World] [M.IsGL]
    (N : Model κ' α) : M ⇄[P] N where
  toRel x w := w ⊩[N] x.charFormulaUnder P
  atomic ha h := (World.forces_charFormulaUnder_iff.mp h).1 _ ha
  forth h R := by
    obtain ⟨v, R', hv⟩ := (World.forces_charFormulaUnder_iff.mp h).2.1 _ R;
    exact ⟨v, hv, R'⟩;
  back h R := by
    obtain ⟨y, R', hy⟩ := (World.forces_charFormulaUnder_iff.mp h).2.2 _ R;
    exact ⟨y, hy, R'⟩;

end

end Model

namespace RootedModel

/-- `A` defines `M` under `P`: it is over `P`, true at the root of `M`, and true at the root of a
finite GL-model only if its root is `P`-bisimilar to that of `M`.

- [Bek90, §4]
-/
structure IsDefiningFormula (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  root_forces : M.root ⊩[M.toModel] A
  unique : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α) [N.IsFiniteGL],
    N.root ⊩[N.toModel] A → ∃ Bi : M.toModel ⇄[P] N.toModel, Bi M.root N.root

/-- - [Bek90, Lemma 7] -/
theorem exists_isDefiningFormula {M : RootedModel κ α} [M.IsFiniteGL] (P : Finset α) :
    ∃ A, M.IsDefiningFormula P A := by
  have : Fintype M.World := Fintype.ofFinite _;
  exact ⟨World.charFormulaUnder (M := M.toModel) P M.root, World.atoms_charFormulaUnder,
    World.forces_charFormulaUnder_self,
    fun N _ h ↦ ⟨charBisimulationUnder P M.toModel N.toModel, h⟩⟩;

end RootedModel

end FFL.ProvabilityLogic.Kripke

end
