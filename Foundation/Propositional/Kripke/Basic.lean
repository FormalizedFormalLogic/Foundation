import Foundation.Propositional.Logic.Basic
import Foundation.Vorspiel.Rel.Basic

namespace LO.Propositional

open Entailment

namespace Kripke

structure Frame where
  World : Type
  Rel : Rel World World
  [world_nonempty : Nonempty World]
  [rel_partial_order : IsPartialOrder _ Rel]

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => _root_.Rel F.World F.World) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty
instance {F : Frame} : IsPartialOrder F.World F.Rel := F.rel_partial_order

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

namespace Frame

variable {F : Frame} {x y z : F.World}

@[mk_iff]
class IsFinite (F : Frame) : Prop where [world_finite : Finite F.World]
attribute [instance] Frame.IsFinite.world_finite

instance [Finite F.World] : F.IsFinite := ⟨⟩

@[simp, refl] lemma refl {x : F.World} : x ≺ x := F.rel_partial_order.refl x
@[trans] lemma trans {x y z : F.World} : x ≺ y → y ≺ z → x ≺ z := F.rel_partial_order.trans x y z
lemma antisymm {x y : F.World} : x ≺ y → y ≺ x → x = y := F.rel_partial_order.antisymm x y

end Frame

section

abbrev whitepoint : Frame where
  World := Unit
  Rel := fun _ _ => True
  rel_partial_order := ⟨⟩
instance : whitepoint.IsFinite := inferInstance

end


abbrev FrameClass := Set (Frame)


structure Valuation (F : Frame) where
  Val : F.World → ℕ → Prop
  hereditary : ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (Val w₁ a) → (Val w₂ a)
instance {F : Frame} : CoeFun (Valuation F) (λ _ => F.World → ℕ → Prop) := ⟨Valuation.Val⟩

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeSort (Model) (Type) := ⟨λ M => M.World⟩
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke


open Kripke


open Formula

namespace Formula.Kripke

@[grind]
def Forces (M : outParam Kripke.Model) (w : M.World) : Formula ℕ → Prop
  | atom a => M w a
  | ⊥      => False
  | φ ⋏ ψ  => Forces M w φ ∧ Forces M w ψ
  | φ ⋎ ψ  => Forces M w φ ∨ Forces M w ψ
  | φ ➝ ψ => ∀ {v : M.World}, (w ≺ v) → (Forces M v φ → Forces M v ψ)
notation:75 x " ⊩[" M "] " φ:50 => Forces M x φ

abbrev NotForces (M : outParam Kripke.Model) (w : M.World) (φ : Formula ℕ) : Prop := ¬(w ⊩[M] φ)
notation:50 x " ⊮[" M "] " φ:50 => NotForces M x φ

namespace Forces

variable {M : Kripke.Model} {x y : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[grind =] lemma def_atom : x ⊩[M] #a ↔ M x a := by tauto;
@[simp, grind .] lemma def_bot : x ⊮[M] ⊥ := by tauto;
@[simp, grind .] lemma def_top : x ⊩[M] ⊤ := by tauto;
@[grind =] lemma def_and : x ⊩[M] φ ⋏ ψ ↔ x ⊩[M] φ ∧ x ⊩[M] ψ := by rfl;
@[grind =] lemma def_or  : x ⊩[M] φ ⋎ ψ ↔ x ⊩[M] φ ∨ x ⊩[M] ψ := by rfl;
@[grind =] lemma def_imp : x ⊩[M] φ ➝ ψ ↔ ∀ {v}, x ≺ v → v ⊩[M] φ → v ⊩[M] ψ := by rfl;
@[grind =] lemma def_neg : x ⊩[M] ∼φ ↔ ∀ {v}, x ≺ v → v ⊮[M] φ := by rfl;

@[grind <=]
lemma formula_hereditary (Rxy : x ≺ y) : x ⊩[_] φ → y ⊩[_] φ := by
  induction φ with
  | hatom => apply M.Val.hereditary Rxy;
  | himp φ ψ ihφ ihψ =>
    intro h z Ryz hzφ;
    exact h (M.trans Rxy Ryz) hzφ
  | _ => grind;

@[grind →] lemma not_of_neg : x ⊩[_] (∼φ) → ¬x ⊩[_] φ := fun h hC ↦ h (refl x) hC

-- lemma negEquiv : x ⊩ ∼φ ↔ x ⊩ φ ➝ ⊥ := by simp_all [Forces];

lemma iff_subst_self {F : Frame} {V : Valuation F} {x : F.World} (s) :
  letI U : Kripke.Valuation F := ⟨
    λ w a => Forces (M := ⟨F, V⟩) w ((.atom a)⟦s⟧),
    fun {_ _} Rwv {_} => formula_hereditary Rwv
  ⟩;
  x ⊩[⟨F, U⟩] φ ↔ x ⊩[⟨F, V⟩] (φ⟦s⟧) := by
  induction φ generalizing x with
  | hatom a => simp [Forces];
  | hfalsum => simp [Forces];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ y Rxy hφs;
      apply ihψ.mp;
      apply hφψ Rxy;
      apply ihφ.mpr hφs;
    . intro hφψs y Rxy hφ;
      apply ihψ.mpr;
      apply hφψs Rxy;
      apply ihφ.mp hφ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . rintro ⟨hφ, hψ⟩;
      apply def_and.mpr;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; apply ihφ.mp hφ;
      . right; apply ihψ.mp hψ;
    . rintro (hφ | hψ);
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;

end Forces


open Forces

namespace ValidOnModel

instance : Semantics (Kripke.Model) (Formula ℕ) := ⟨fun M φ => ∀ x : M.World, x ⊩[M] φ⟩

variable {M : Model} {φ ψ χ : Formula ℕ}

@[simp, grind =] lemma iff_models : M ⊧ φ ↔ ∀ x : M.World, x ⊩[M] φ := iff_of_eq rfl
@[simp, grind =] lemma iff_not_models : M ⊭ φ ↔ ∃ x : M.World, x ⊮[M] φ := by simp [Semantics.NotModels, Semantics.Models];

instance : Semantics.Top Model := ⟨by simp⟩
instance : Semantics.Bot Model := ⟨by simp⟩

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_models

protected lemma andElim₁ : M ⊧ φ ⋏ ψ ➝ φ := by grind;
protected lemma andElim₂ : M ⊧ φ ⋏ ψ ➝ ψ := by grind;
protected lemma andInst₃ : M ⊧ φ ➝ ψ ➝ φ ⋏ ψ := by grind;
protected lemma orInst₁ : M ⊧ φ ➝ φ ⋎ ψ := by grind;
protected lemma orInst₂ : M ⊧ ψ ➝ φ ⋎ ψ := by grind;

protected lemma orElim : M ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma implyK : M ⊧ φ ➝ ψ ➝ φ := by grind;

protected lemma implyS : M ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw : y ≺ w := M.trans Ryz Rzw;
  have Rww : w ≺ w := M.refl;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w M.refl $ hp w;

protected lemma efq : M ⊧ Axioms.EFQ φ := by grind;

end ValidOnModel



namespace ValidOnFrame

instance : Semantics Frame (Formula ℕ) := ⟨fun F φ => ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ⟩

variable {F : Frame} {φ ψ χ : Formula ℕ}

@[simp, grind .] lemma iff_valid : F ⊧ φ ↔ ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ := by rfl
@[simp, grind .] lemma iff_not_valid : F ⊭ φ ↔ ∃ V, (⟨F, V⟩ : Kripke.Model) ⊭ φ := by simp [Semantics.NotModels, Semantics.Models];
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_valid

lemma iff_not_exists_valuation_world : (F ⊭ φ) ↔ (∃ V x, x ⊮[⟨F, V⟩] φ) := by grind;
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

protected lemma top : F ⊧ ⊤ := by tauto;
instance : Semantics.Top (Frame) := ⟨λ _ => ValidOnFrame.top⟩

protected lemma bot : F ⊭ ⊥ := by
  apply not_of_exists_valuation_world;
  use ⟨λ _ _ => True, by tauto⟩, F.world_nonempty.some;
  grind;
instance : Semantics.Bot (Frame) := ⟨λ _ => ValidOnFrame.bot⟩

protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Forces.iff_subst_self s |>.not.mpr hx;
  apply h;

protected lemma andElim₁ : F ⊧ φ ⋏ ψ ➝ φ := fun _ => ValidOnModel.andElim₁

protected lemma andElim₂ : F ⊧ φ ⋏ ψ ➝ ψ := fun _ => ValidOnModel.andElim₂

protected lemma andInst₃ : F ⊧ φ ➝ ψ ➝ φ ⋏ ψ := fun _ => ValidOnModel.andInst₃

protected lemma orInst₁ : F ⊧ φ ➝ φ ⋎ ψ := fun _ => ValidOnModel.orInst₁

protected lemma orInst₂ : F ⊧ ψ ➝ φ ⋎ ψ := fun _ => ValidOnModel.orInst₂

protected lemma orElim : F ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := fun _ => ValidOnModel.orElim

protected lemma implyK : F ⊧ φ ➝ ψ ➝ φ := fun _ => ValidOnModel.implyK

protected lemma implyS : F ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := fun _ => ValidOnModel.implyS

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := fun V x => ValidOnModel.mdp (hpq V) (hp V) x

protected lemma efq : F ⊧ Axioms.EFQ φ := fun _ => ValidOnModel.efq

end ValidOnFrame

end Formula.Kripke



namespace Kripke

section

variable {C : Kripke.FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : C ⊭ φ ↔ (∃ F ∈ C, F ⊭ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : C ⊭ φ ↔ (∃ M : Kripke.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

end



/-
section

open Formula (atom)

namespace FrameClass

def Validates (C : FrameClass) (Γ : FormulaSet ℕ) := ∀ F ∈ C, ∀ φ ∈ Γ, F ⊧ φ

abbrev ValidatesFormula (C : FrameClass) (φ : Formula ℕ) := Validates C {φ}

variable {C C₁ C₂ : FrameClass} {Γ Γ₁ Γ₂ : FormulaSet ℕ} {φ φ₁ φ₂ : Formula ℕ}

lemma Validates.inter_of (h₁ : C₁.Validates Γ₁) (h₂ : C₂.Validates Γ₂) : (C₁ ∩ C₂).Validates (Γ₁ ∪ Γ₂) := by
  rintro F;
  rintro ⟨hF₁, hF₂⟩ φ (hφ₁ | hφ₂);
  . exact h₁ F hF₁ _ hφ₁;
  . exact h₂ F hF₂ _ hφ₂;

lemma ValidatesFormula.inter_of (h₁ : C₁.ValidatesFormula φ₁) (h₂ : C₂.ValidatesFormula φ₂) : (C₁ ∩ C₂).Validates {φ₁, φ₂}
  := Validates.inter_of h₁ h₂

protected abbrev all : FrameClass := Set.univ

@[simp]
lemma all.IsNonempty : FrameClass.all.Nonempty := by use whitepoint; tauto;

lemma all.validates_AxiomEFQ : FrameClass.all.ValidatesFormula (Axioms.EFQ (.atom 0)) := by

  suffices ∀ F : Frame, F ⊨ (Axioms.EFQ (.atom 0)) by simpa [Validates];
  intro F;
  exact Formula.Kripke.ValidOnFrame.efq;

lemma Validates.withAxiomEFQ (hV : C.Validates Γ) : C.Validates (insert (Axioms.EFQ (.atom 0)) Γ) := by
  convert Validates.inter_of all.validates_AxiomEFQ hV;
  tauto_set;

protected abbrev finite_all : FrameClass := { F | F.IsFinite }

@[simp]
lemma finite_all.nonempty : FrameClass.finite_all.Nonempty := by use whitepoint; tauto;

lemma finite_all.validates_AxiomEFQ : FrameClass.finite_all.ValidatesFormula (Axioms.EFQ (.atom 0)) := by
  suffices ∀ (F : Frame), F.IsFinite → F ⊨ (Axioms.EFQ (.atom 0)) by simpa [Validates];
  intro F _;
  exact Formula.Kripke.ValidOnFrame.efq;

end FrameClass

end
-/

section

abbrev FrameClass.logic (C : FrameClass) : Logic ℕ := { φ | C ⊧ φ }

end

end Kripke

end LO.Propositional
