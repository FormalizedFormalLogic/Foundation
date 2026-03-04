module

public import Foundation.Modal.Logic.Basic
public import Foundation.Vorspiel.Rel.Basic
public import Foundation.Logic.ForcingRelation

@[expose] public section

namespace LO.Modal

variable {ν} [Nonempty ν] {α : Type*}
         {n : ℕ} {φ ψ χ : Formula α} {a : α}

structure NeighborhoodModel (ν : Type*) [Nonempty ν] (α : Type*) where
  filter : ν → Set (Set ν)
  val : α → Set ν

namespace NeighborhoodModel

variable {M : NeighborhoodModel ν α}

abbrev World (_ : NeighborhoodModel ν α) := ν

abbrev Neighborhood (M : NeighborhoodModel ν α) := Set M.World

def box (M : NeighborhoodModel ν α) (X : M.Neighborhood) : M.Neighborhood := { w | X ∈ M.filter w }
def dia (M : NeighborhoodModel ν α) := λ X => (M.box Xᶜ)ᶜ

def mkBox (ν : Type*) [Nonempty ν] (α : Type*) (box : Set ν → Set ν) (val : α → Set ν) : NeighborhoodModel ν α where
  filter w := { X | w ∈ box X }
  val := val

def truthset (M : NeighborhoodModel ν α) : Formula α → M.Neighborhood
| .atom a => M.val a
| ⊥       => ∅
| φ ➝ ψ  => (truthset M φ)ᶜ ∪ truthset M ψ
| □φ      => M.box (truthset M φ)

instance : CoeFun (NeighborhoodModel ν α) (λ M => Formula α → M.Neighborhood) := ⟨λ M => truthset M⟩

lemma def_truthset_atom   : M (.atom a) = M.val a := rfl
lemma def_truthset_verum  : M ⊤ = Set.univ := by simp [truthset];
lemma def_truthset_falsum : M ⊥ = ∅ := rfl
lemma def_truthset_and    : M (φ ⋏ ψ) = M φ ∩ M ψ := by simp [truthset];
lemma def_truthset_or     : M (φ ⋎ ψ) = M φ ∪ M ψ := by simp [truthset];
lemma def_truthset_imp    : M (φ ➝ ψ) = (M φ)ᶜ ∪ M ψ := rfl
lemma def_truthset_neg    : M (∼φ) = (M φ)ᶜ := by simp [truthset];

attribute [simp, grind =]
  def_truthset_atom
  def_truthset_verum
  def_truthset_falsum
  def_truthset_and
  def_truthset_or
  def_truthset_imp
  def_truthset_neg

@[simp, grind =]
lemma def_truthset_iff    : M (φ ⭤ ψ) = (M φ ∩ M ψ) ∪ ((M φ)ᶜ ∩ (M ψ)ᶜ)  := calc
  M (φ ⭤ ψ) = M (φ ➝ ψ) ∩ M (ψ ➝ φ)               := by simp [LogicalConnective.iff];
  _         = ((M φ)ᶜ ∪ (M ψ)) ∩ ((M ψ)ᶜ ∪ (M φ)) := by simp;
  _         = (M φ ∩ M ψ) ∪ ((M φ)ᶜ ∩ (M ψ)ᶜ)     := by tauto_set;


@[simp, grind =]
lemma def_boxItr {n : ℕ} : M (□^[n] φ) = M.box^[n] (M φ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ']; simp [ih, truthset]

@[simp, grind =]
lemma def_box : M (□φ) = M.box (M φ) := def_boxItr (n := 1)


@[simp, grind =]
lemma def_diaItr {n : ℕ} : M (◇^[n] φ) = M.dia^[n] (M φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ'];
    simp only [Dia.diaItr_succ, truthset, ih, Set.union_empty, Function.comp_apply, dia]

@[simp, grind =]
lemma def_dia : M (◇φ) = M.dia (M φ) := def_diaItr (n := 1)


def Forces (M : NeighborhoodModel ν α) (w : M.World) (φ : Formula α) : Prop := w ∈ M φ

instance {M : NeighborhoodModel ν α} : ForcingRelation M.World (Formula α) := ⟨Forces _⟩

variable {x : M.World}

@[simp, grind .]
lemma iff_forces_mem_truthset : x ⊩ φ ↔ x ∈ M φ := by rfl;

lemma forces_atom : x ⊩ (.atom a) ↔ x ∈ M.val a := by simp [ForcingRelation.Forces, Forces]
lemma forces_verum : x ⊩ ⊤ := by simp [ForcingRelation.Forces, Forces]
lemma forces_falsum : x ⊮ ⊥ := by simp [ForcingRelation.NotForces, ForcingRelation.Forces, Forces]
lemma forces_and : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by simp [ForcingRelation.Forces, Forces]
lemma forces_or : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by simp [ForcingRelation.Forces, Forces]
lemma forces_imp : x ⊩ φ ➝ ψ ↔ (x ⊩ φ → x ⊩ ψ) := by
  simp [ForcingRelation.Forces, Forces]
  tauto;
lemma forces_neg : x ⊩ ∼φ ↔ ¬ x ⊩ φ := by simp [ForcingRelation.Forces, Forces]
lemma forces_iff : x ⊩ φ ⭤ ψ ↔ (x ⊩ φ ↔ x ⊩ ψ) := by
  simp [ForcingRelation.Forces, Forces]
  tauto;

lemma forces_boxItr : x ⊩ □^[n] φ ↔ x ∈ M.box^[n] (M φ) := by simp [ForcingRelation.Forces, Forces, def_boxItr]
lemma forces_box : x ⊩ □φ ↔ x ∈ M.box (M φ) := forces_boxItr (n := 1)

lemma forces_diaItr : x ⊩ ◇^[n] φ ↔ x ∈ M.dia^[n] (M φ) := by simp [ForcingRelation.Forces, Forces, def_diaItr]
lemma forces_dia : x ⊩ ◇φ ↔ x ∈ M.dia (M φ) := forces_diaItr (n := 1)

attribute [simp, grind .]
  forces_verum
  forces_falsum

attribute [simp, grind =]
  forces_atom
  forces_and
  forces_or
  forces_imp
  forces_neg
  forces_iff
  forces_boxItr
  forces_box
  forces_diaItr
  forces_dia


instance : Semantics (NeighborhoodModel ν α) (Formula α) := ⟨λ M φ => M.World ∀⊩ φ⟩

lemma iff_validates_forall_forces : M ⊧ φ ↔ ∀ x : M.World, x ⊩ φ := by rfl;
alias ⟨validates_forall_forces_of_validates, validates_of_forall_forces⟩ := iff_validates_forall_forces

lemma iff_not_validates_exists_not_forces : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by
  contrapose!;
  exact iff_validates_forall_forces;
alias ⟨exists_not_forces_of_not_validates, not_validates_of_exists_not_forces⟩ := iff_not_validates_exists_not_forces

@[grind =]
lemma iff_validates_eq_truthset_univ : M ⊧ φ ↔ M φ = Set.univ := by
  apply Iff.trans $ iff_validates_forall_forces;
  simp [iff_forces_mem_truthset, Set.eq_univ_iff_forall];

@[grind =]
lemma iff_validates_iff_eq_truthset : M ⊧ φ ⭤ ψ ↔ M φ = M ψ := by
  constructor;
  . intro h;
    ext x;
    grind [h x];
  . rintro h;
    simp [iff_validates_eq_truthset_univ, h];

@[simp, grind .]
lemma validates_axiomImplyK : M ⊧ Axioms.ImplyK φ ψ := by
  simp only [iff_validates_eq_truthset_univ, def_truthset_imp];
  tauto_set;

@[simp, grind .]
lemma validates_axiomImplyS : M ⊧ Axioms.ImplyS φ ψ χ := by
  simp only [iff_validates_eq_truthset_univ, def_truthset_imp];
  tauto_set;

@[simp, grind .]
lemma validates_axiomElimContra : M ⊧ Axioms.ElimContra φ ψ := by
  simp only [iff_validates_eq_truthset_univ, def_truthset_imp, def_truthset_neg];
  tauto_set;

lemma validates_mdp (hφψ : M ⊧ φ ➝ ψ) (hφ : M ⊧ φ) : M ⊧ ψ := by
  simp_all [iff_validates_eq_truthset_univ, def_truthset_imp];

lemma validates_re (hφψ : M ⊧ φ ⭤ ψ) : M ⊧ □φ ⭤ □ψ := by
  simp_all [iff_validates_iff_eq_truthset];

end NeighborhoodModel

end LO.Modal

end
