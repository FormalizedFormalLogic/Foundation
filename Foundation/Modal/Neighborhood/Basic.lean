import Foundation.Vorspiel.HRel.Basic
import Foundation.Modal.Axioms
import Foundation.Modal.Formula
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open Formula (atom)

namespace Neighborhood

structure Frame where
  World : Type
  [world_nonempty : Nonempty World]
  𝒩 : World → Set (Set World)
attribute [simp] Frame.world_nonempty

instance : CoeSort Frame Type := ⟨Frame.World⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty

@[reducible] def Frame.ℬ (F : Frame) : Set F.World → Set F.World := λ X => { w | X ∈ F.𝒩 w }

@[simp]
lemma Frame.eq_ℬ_𝒩 {F : Frame} {X Y : Set F.World} : (F.ℬ X) = Y ↔ (∀ x, X ∈ F.𝒩 x ↔ x ∈ Y) := by
  constructor;
  . rintro rfl;
    tauto;
  . rintro h;
    ext x;
    apply h;

def Frame.mk_B (World : Type) [Nonempty World] (B : Set World → Set World) : Frame where
  World := World
  𝒩 x := { X | x ∈ B X }

section

abbrev Frame.simple_blackhole : Frame := ⟨Unit, λ _ => { Set.univ }⟩

end


abbrev FrameClass := Set Frame


abbrev Valuation (F : Frame) := ℕ → Set F.World

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeSort Model Type := ⟨λ M => M.toFrame.World⟩
--instance : CoeFun Model (λ M => M.World → Set (Set M.World)) := ⟨λ M => Frame.ν M.toFrame⟩

@[simp]
lemma Model.nonempty_univ_world {M : Model} : Set.Nonempty (Set.univ (α := M.World)) := by
  use M.world_nonempty.some;
  tauto;

@[grind]
def Model.truthset (M : Model) : Formula ℕ → Set M.World
| .atom n => M.Val n
| ⊥       => ∅
| φ ➝ ψ  => (truthset M φ)ᶜ ∪ truthset M ψ
| □φ      => M.ℬ (truthset M φ)

namespace Model.truthset

variable {M : Model} {n : ℕ} {φ ψ : Formula ℕ}

instance : CoeFun Model (λ M => Formula ℕ → Set M.World) := ⟨λ M => truthset M⟩

@[simp, grind] lemma eq_atom : M (.atom n) = M.Val n := rfl
@[simp, grind] lemma eq_bot  : M ⊥ = ∅ := rfl
@[simp, grind] lemma eq_top  : M ⊤ = Set.univ := by simp [truthset]
@[simp, grind] lemma eq_imp  : M (φ ➝ ψ) = (M φ)ᶜ ∪ (M ψ) := rfl
@[simp, grind] lemma eq_or   : M (φ ⋎ ψ) = (M φ) ∪ (M ψ) := by simp [truthset];
@[simp, grind] lemma eq_and  : M (φ ⋏ ψ) = (M φ) ∩ (M ψ) := by simp [truthset];
@[simp, grind] lemma eq_neg  : M (∼φ) = (M φ)ᶜ := by simp [truthset]
@[simp, grind] lemma eq_iff  : M (φ ⭤ ψ) = (M φ ∩ M ψ) ∪ ((M φ)ᶜ ∩ (M ψ)ᶜ) := calc
  M (φ ⭤ ψ) = M (φ ➝ ψ) ∩ (M (ψ ➝ φ))             := by simp [LogicalConnective.iff];
  _         = ((M φ)ᶜ ∪ (M ψ)) ∩ ((M ψ)ᶜ ∪ (M φ)) := by simp;
  _         = (M φ ∩ M ψ) ∪ ((M φ)ᶜ ∩ (M ψ)ᶜ)     := by tauto_set;
@[simp, grind] lemma eq_box  : M (□φ) = M.ℬ (M φ) := rfl
@[simp, grind] lemma eq_dia  : M (◇φ) = (M.ℬ (M φ)ᶜ)ᶜ := by simp [truthset]

@[grind]
lemma eq_subst :
  letI U : Valuation M.toFrame := λ a => M ((atom a)⟦s⟧)
  M (φ⟦s⟧) = (⟨M.toFrame, U⟩ : Model) φ := by
  induction φ <;> simp_all;

end Model.truthset


end Neighborhood


namespace Formula.Neighborhood

open Modal.Neighborhood

def Satisfies (M : Model) (x : M.World) (φ : Formula ℕ) : Prop := x ∈ M φ

namespace Satisfies

protected instance semantics {M : Model} : Semantics (Formula ℕ) M.World := ⟨λ x => Formula.Neighborhood.Satisfies M x⟩

variable {M : Model} {x : M.World} {φ ψ ξ : Formula ℕ}

@[grind] lemma def_top : x ⊧ ⊤ := by simp [Semantics.Realize, Satisfies];
@[grind] lemma def_bot : ¬x ⊧ ⊥ := by simp [Semantics.Realize, Satisfies];
@[grind] lemma def_neg : x ⊧ ∼φ ↔ ¬x ⊧ φ := by simp [Semantics.Realize, Satisfies];
@[grind] lemma def_imp : x ⊧ φ ➝ ψ ↔ (x ⊧ φ → x ⊧ ψ) := by simp [Semantics.Realize, Satisfies]; tauto;
@[grind] lemma def_and : x ⊧ φ ⋏ ψ ↔ (x ⊧ φ ∧ x ⊧ ψ) := by simp [Semantics.Realize, Satisfies];
@[grind] lemma def_or  : x ⊧ φ ⋎ ψ ↔ (x ⊧ φ ∨ x ⊧ ψ) := by simp [Semantics.Realize, Satisfies];

@[grind] lemma def_box : x ⊧ □φ ↔ M φ ∈ (M.𝒩 x) := by simp [Semantics.Realize, Satisfies];
@[grind] lemma def_dia : x ⊧ ◇φ ↔ (M φ)ᶜ ∈ (M.𝒩 x)ᶜ := by simp [Semantics.Realize, Satisfies];

protected instance : Semantics.Tarski (M.World) where
  realize_top := by grind
  realize_bot := by grind
  realize_imp := by grind
  realize_not := by grind
  realize_or  := by grind
  realize_and := by grind

@[simp] protected lemma imply₁ : x ⊧ Axioms.Imply₁ φ ψ := by grind
@[simp] protected lemma imply₂ : x ⊧ Axioms.Imply₂ φ ψ ξ := by grind
@[simp] protected lemma elimContra : x ⊧ Axioms.ElimContra φ ψ := by grind
protected lemma mdp (hφψ : x ⊧ φ ➝ ψ) (hψ : x ⊧ φ) : x ⊧ ψ := by grind

lemma dia_dual : x ⊧ ◇φ ↔ x ⊧ ∼□(∼φ) := by simp [Semantics.Realize, Satisfies];
lemma box_dual : x ⊧ □φ ↔ x ⊧ ∼◇(∼φ) := by simp [Semantics.Realize, Satisfies];

lemma iff_subst_self {M : Model} {x : M.World} (s) :
  letI U : Valuation M.toFrame := λ a => M ((atom a)⟦s⟧)
  Satisfies ⟨M.toFrame, U⟩ x φ ↔ Satisfies M x (φ⟦s⟧) := by
  simp [Satisfies, Model.truthset.eq_subst];

end Satisfies


def ValidOnModel (M : Model) (φ : Formula ℕ) : Prop := ∀ x, Satisfies M x φ

namespace ValidOnModel

variable {M : Model} {φ ψ ξ : Formula ℕ}

protected instance semantics : Semantics (Formula ℕ) Model := ⟨fun M ↦ ValidOnModel M⟩

@[simp]
lemma iff_eq_truthset_univ : M ⊧ φ ↔ (M φ = Set.univ) := by
  constructor;
  . intro hφ;
    ext x;
    simp only [Set.mem_univ, iff_true];
    apply hφ;
  . intro h x;
    simp [Satisfies, h]

instance : Semantics.Bot Model where
  realize_bot M := by
    simp only [iff_eq_truthset_univ, Neighborhood.Model.truthset.eq_bot];
    apply Set.nonempty_iff_ne_empty.mp ?_ |>.symm;
    simp;

instance : Semantics.Top Model where
  realize_top M := by simp;

lemma valid_iff : M ⊧ φ ⭤ ψ ↔ (M φ = M ψ) := by
  constructor;
  . intro h;
    ext x;
    have := @h x;
    simp [Satisfies] at this;
    tauto;
  . intro h x;
    simp [Satisfies, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, h];

@[simp] protected lemma imply₁ : M ⊧ Axioms.Imply₁ φ ψ := λ _ ↦ Satisfies.imply₁

@[simp] protected lemma imply₂ : M ⊧ Axioms.Imply₂ φ ψ ξ := λ _ ↦ Satisfies.imply₂

@[simp] protected lemma elimContra : M ⊧ Axioms.ElimContra φ ψ := λ _ ↦ Satisfies.elimContra

protected lemma mdp (hφψ : M ⊧ φ ➝ ψ) (hψ : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  apply Satisfies.mdp;
  . exact hφψ x;
  . exact hψ x;

protected lemma re (hφ : M ⊧ φ ⭤ ψ) : M ⊧ □φ ⭤ □ψ := by
  rw [valid_iff] at ⊢ hφ;
  ext x;
  simp [Satisfies, hφ];

end ValidOnModel



def ValidOnFrame (F : Neighborhood.Frame) (φ : Formula ℕ) : Prop := ∀ V, (⟨F, V⟩ : Model) ⊧ φ

namespace ValidOnFrame

variable {F : Frame} {φ ψ ξ : Formula ℕ}

protected instance semantics : Semantics (Formula ℕ) Frame := ⟨fun F ↦ ValidOnFrame F⟩

instance : Semantics.Bot Frame where
  realize_bot F := by
    by_contra! hC;
    simpa using hC (λ _ => {});

instance : Semantics.Top Frame where
  realize_top F := by intro; simp;

protected lemma mdp (hφψ : F ⊧ φ ➝ ψ) (hφ : F ⊧ φ) : F ⊧ ψ := by
  intro V;
  apply ValidOnModel.mdp;
  . exact hφψ V;
  . exact hφ V;

protected lemma re (hφ : F ⊧ φ ⭤ ψ) : F ⊧ □φ ⭤ □ψ := by
  intro V;
  apply ValidOnModel.re;
  exact hφ V;

@[simp] protected lemma imply₁ : F ⊧ Axioms.Imply₁ φ ψ := λ _ ↦ ValidOnModel.imply₁

@[simp] protected lemma imply₂ : F ⊧ Axioms.Imply₂ φ ψ ξ := λ _ ↦ ValidOnModel.imply₂

@[simp] protected lemma elimContra : F ⊧ Axioms.ElimContra φ ψ := λ _ ↦ ValidOnModel.elimContra


lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Valuation F, ∃ x : (⟨F, V⟩ : Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, Satisfies, ValidOnModel, Semantics.Realize];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

protected lemma subst (s) (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, x, hx⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (λ a => Model.truthset ⟨F, V⟩ (atom a⟦s⟧)) x;

end ValidOnFrame

section

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_model_world : (¬C ⊧ φ) ↔ (∃ M : Model, ∃ x : M.World, M.toFrame ∈ C ∧ ¬(x ⊧ φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end

end Formula.Neighborhood


namespace Neighborhood

abbrev Frame.logic (F : Frame) : Logic ℕ := { φ | F ⊧ φ }
abbrev FrameClass.logic (C : FrameClass) : Logic ℕ := { φ | C ⊧ φ }

end Neighborhood



end LO.Modal
