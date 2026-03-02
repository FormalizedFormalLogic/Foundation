module

public import Foundation.Propositional.Logic.Basic
public import Foundation.Propositional.Entailment.Corsi.Basic
public import Foundation.Vorspiel.Rel.Basic
public import Foundation.Logic.ForcingRelation

@[expose] public section

variable {κ α : Type*} [Nonempty κ]

namespace LO.Propositional

open Entailment

structure KripkeModel (κ : Type*) [Nonempty κ] (α : Type*) where
  frame : Rel κ κ
  val : α → κ → Prop

namespace KripkeModel

abbrev world (_ : KripkeModel κ α) := κ

variable {M : KripkeModel κ α} {x y z : M.world} {a : α} {φ ψ χ : Formula α} {n m : ℕ}

abbrev rel : Rel M.world M.world := M.frame
infix:45 " ≺ " => rel

abbrev relInv (x y : M.world) := M.frame y x
infix:45 " ≻ " => relInv

abbrev relItr (n : ℕ) : Rel M.world M.world := M.frame.Iterate n
notation x:45 " ≺^[" n:0 "] " y:46 => relItr n x y

-- instance : CoeSort (KripkeModel κ α) (Type*) := ⟨λ M => M.world⟩
instance : CoeFun (KripkeModel κ α) (λ _ => α → κ → Prop) := ⟨fun M => M.val⟩

section Forces


@[grind]
def Forces (M : KripkeModel κ α) (x : M.world) : Formula α → Prop
  | .atom a  => M a x
  | ⊥      => False
  | φ ⋏ ψ  => Forces M x φ ∧ Forces M x ψ
  | φ ⋎ ψ  => Forces M x φ ∨ Forces M x ψ
  | φ ➝ ψ => ∀ y : M.world, x ≺ y → (Forces M y φ → Forces M y ψ)

instance : ForcingRelation M.world (Formula α) where
  Forces := Forces M

@[grind =] lemma forces_atom : x ⊩ (.atom a) ↔ M a x := by tauto
@[simp, grind .] lemma forces_falsum : x ⊮ ⊥ := by tauto;
@[simp, grind .] lemma forces_verum : x ⊩ ⊤ := by tauto;
@[grind =] lemma forces_and : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by rfl;
@[grind =] lemma forces_or : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by rfl;
@[grind =] lemma forces_imp : x ⊩ φ ➝ ψ ↔ ∀ y : M.world, x ≺ y → (y ⊩ φ → y ⊩ ψ) := by rfl;

@[grind =]
lemma forces_neg : x ⊩ ∼φ ↔ ∀ y, x ≺ y → (y ⊮ φ) := by
  simp [Formula.neg_def, forces_imp, ForcingRelation.NotForces];

instance : ForcingRelation.BasicSemantics M.world where
  verum {_} := forces_verum
  falsum {_} := forces_falsum
  and {_ _ _} := forces_and
  or {_ _ _} := forces_or


@[grind =]
lemma forces_lconj {l : List _} : x ⊩ l.conj ↔ ∀ φ ∈ l, x ⊩ φ := by
  induction l <;>
  grind [List.conj_cons, List.conj_nil];

@[grind =]
lemma forces_lconj₂ {l : List _} : x ⊩ ⋀l ↔ ∀ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton <;>
  grind [List.conj₂_nil, List.conj₂_cons_nonempty, List.conj₂_singleton]

@[grind =]
lemma forces_lconj' {l : List β} {ι : β → Formula α} : x ⊩ l.conj' ι ↔ ∀ i ∈ l, x ⊩ (ι i) := by
  grind [List.conj'];

@[grind =]
lemma forces_fconj {s : Finset _} : x ⊩ s.conj ↔ ∀ φ ∈ s, x ⊩ φ := by
  apply Iff.trans forces_lconj₂;
  simp;

@[grind =]
lemma forces_fconj' {s : Finset β} {ι : β → Formula α} : x ⊩ s.conj' ι ↔ ∀ i ∈ s, x ⊩ (ι i) := by
  apply Iff.trans forces_lconj';
  simp;


@[grind =]
lemma forces_ldisj {l : List _} : x ⊩ l.disj ↔ ∃ φ ∈ l, x ⊩ φ := by
  induction l <;>
  grind [List.disj_cons, List.disj_nil];

@[grind =]
lemma forces_ldisj₂ {l : List _} : x ⊩ ⋁l ↔ ∃ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton <;>
  grind [List.disj₂_nil, List.disj₂_cons_nonempty, List.disj₂_singleton]

@[grind =]
lemma forces_ldisj' {l : List β} {ι : β → Formula α} : x ⊩ l.disj' ι ↔ ∃ i ∈ l, x ⊩ (ι i) := by
  grind [List.disj']

@[grind =]
lemma forces_fdisj {s : Finset _} : x ⊩ s.disj ↔ ∃ φ ∈ s, x ⊩ φ := by
  apply Iff.trans forces_ldisj₂;
  simp;

@[grind =]
lemma forces_fdisj' {s : Finset β} {ι : β → Formula α} : x ⊩ s.disj' ι ↔ ∃ i ∈ s, x ⊩ (ι i) := by
  apply Iff.trans forces_ldisj';
  simp;

end Forces


section Models

variable {M : KripkeModel κ α} {φ ψ χ : Formula α}

instance : Semantics (KripkeModel κ α) (Formula α) := ⟨λ M φ => M.world ∀⊩ φ⟩

@[grind =]
lemma iff_validates_forall_forces : M ⊧ φ ↔ ∀ x : M.world, x ⊩ φ := by rfl
alias ⟨forallforces_of_validates, validates_of_forall_forces⟩ := iff_validates_forall_forces

@[grind =]
lemma iff_notValidates_exists_world_notForces : M ⊭ φ ↔ ∃ x : M.world, x ⊮ φ := by
  simp [Semantics.Models, Semantics.NotModels];
alias ⟨exists_world_notForces_of_notValidates, notValidates_of_exists_world_notForces⟩ := iff_notValidates_exists_world_notForces


lemma validates_verum : M ⊧ ⊤ := ForcingRelation.AllForces.verum
instance : Semantics.Top (KripkeModel κ α) := ⟨λ _ => validates_verum⟩

lemma validates_falsum : M ⊭ ⊥ := by
  have : Inhabited M.world := Inhabited.mk $ Nonempty.some inferInstance;
  apply ForcingRelation.AllForces.falsum
instance : Semantics.Bot (KripkeModel κ α) := ⟨λ _ => validates_falsum⟩

@[grind =]
lemma validates_and : M ⊧ (φ ⋏ ψ) ↔ M ⊧ φ ∧ M ⊧ ψ := ForcingRelation.AllForces.and
instance : Semantics.And (KripkeModel κ α) := ⟨validates_and⟩

lemma validates_andElim₁ : M ⊧ Axioms.AndElim₁ φ ψ := by intro x; grind;
lemma validates_andElim₂ : M ⊧ Axioms.AndElim₂ φ ψ := by intro x; grind;
lemma validates_orInst₁ : M ⊧ Axioms.OrInst₁ φ ψ := by intro x; grind;
lemma validates_orInst₂ : M ⊧ Axioms.OrInst₂ φ ψ := by intro x; grind;
lemma validates_efq : M ⊧ Axioms.EFQ φ := by intro x; grind;

lemma validates_distributeAndOr : M ⊧ Axioms.DistributeAndOr φ ψ χ := by
  rintro x y Rxy ⟨hφ, (hψ | hχ)⟩
  . left; constructor <;> assumption;
  . right; constructor <;> assumption;

lemma validates_axiomD : M ⊧ Axioms.D φ ψ χ := by
  rintro x y Rxy ⟨h₁, h₂⟩ z Ryz (hφ | hψ);
  . apply h₁ <;> assumption;
  . apply h₂ <;> assumption;

lemma validates_axiomI : M ⊧ Axioms.I φ ψ χ := by
  rintro x y Rxy ⟨h₁, h₂⟩ z Ryz h₃;
  exact h₂ z Ryz $ h₁ z Ryz h₃;

lemma validates_impId : M ⊧ Axioms.ImpId φ := by rintro x y Rxy hφ; assumption;

attribute [grind .]
  validates_verum
  validates_falsum
  validates_and
  validates_andElim₁
  validates_andElim₂
  validates_orInst₁
  validates_orInst₂
  validates_efq
  validates_distributeAndOr
  validates_axiomD
  validates_axiomI
  validates_impId

@[grind <=]
lemma validates_ruleC (hφ : M ⊧ φ) (hψ : M ⊧ ψ) : M ⊧ φ ⋏ ψ := fun x ↦ ⟨hφ x, hψ x⟩

@[grind <=]
lemma validates_afortiori (h : M ⊧ φ) : M ⊧ ψ ➝ φ := fun _ y _ _ ↦ h y

end Models


section

class Persistent (M : KripkeModel κ α) : Prop where
  atom_persistency : ∀ {x y : M.world} {a : α}, x ⊩ (.atom a) → x ≺ y → y ⊩ (.atom a)
export Persistent (atom_persistency)

lemma formula_persistency [Persistent M] [IsTrans _ M.rel] {x y : M.world} {φ : Formula α} (hxφ : x ⊩ φ) (Rxy : x ≺ y) : y ⊩ φ := by
  induction φ with
  | hatom => apply atom_persistency hxφ Rxy;
  | himp φ ψ ihφ ihψ =>
    intro z Ryz hzφ;
    apply hxφ z $ IsTrans.trans _ _ _ Rxy Ryz;
    apply hzφ;
  | _ => grind;

@[grind .]
lemma validates_implyK [Persistent M] [IsTrans _ M.rel] : M ⊧ φ ➝ ψ ➝ φ := by
  intro x y Rxy hφ z Ryz hψ;
  apply formula_persistency hφ Ryz;

@[grind .]
lemma validates_implyS [IsTrans _ M.rel] [Std.Refl M.rel] : M ⊧ Axioms.ImplyS φ ψ χ := by
  rintro x y Rxy hφψχ z Ryz hφψ w Rzw hφ;
  have Ryw : y ≺ w := IsTrans.trans _ _ _ Ryz Rzw;
  have Rww : w ≺ w := Std.Refl.refl _;
  exact hφψχ _ Ryw hφ _ Rww (hφψ _ Rzw hφ);

lemma validates_mdp_of_reflexive [Std.Refl M.rel] (hφψ : M ⊧ φ ➝ ψ) (hφ : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  apply hφψ x;
  . apply Std.Refl.refl;
  . apply hφ;

class Intuitionistic (M : KripkeModel κ α) extends Std.Refl M.rel, IsTrans _ M.rel, Persistent M

end


def logic (M : KripkeModel κ α) : Logic α := { φ | M ⊧ φ }

end KripkeModel


end LO.Propositional

end
