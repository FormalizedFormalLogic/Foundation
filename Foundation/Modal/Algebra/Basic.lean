module
import Foundation.Modal.LogicSymbol
import Foundation.Modal.Formula
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Vorspiel.Order
import Foundation.Logic.LindenbaumAlgebra
import Foundation.Modal.Kripke.Logic.K


namespace LO

/-- Algebra corresponding to `Modal.K` -/
class ModalAlgebra (α : Type*) extends BooleanAlgebra α, Box α, Dia α where
  box_top : □(⊤ : α) = ⊤
  box_meet (a b : α) : □(a ⊓ b) = □a ⊓ □b
  dual_dia {a : α} : (◇a) = (□aᶜ)ᶜ

namespace ModalAlgebra

variable {α : Type*} [ModalAlgebra α]
variable {a b : α}

attribute [grind =] dual_dia

@[grind =] lemma dual_box {a : α} : □a = (◇aᶜ)ᶜ := by simp [dual_dia]

@[grind =] lemma compl_box : (□a)ᶜ = ◇aᶜ := by simp [dual_box];
@[grind =] lemma compl_dia : (◇a)ᶜ = □aᶜ := by simp [dual_dia];

attribute [simp, grind .] box_top
@[simp, grind .] lemma dia_bot : ◇(⊥ : α) = ⊥ := by simp [dual_dia];

lemma box_imp_le_box_imp_box : □(a ⇨ b) ≤ (□a ⇨ □b) := by
  suffices □(a ⇨ b) ⊓ □a ≤ □b by simpa;
  calc
    □(a ⇨ b) ⊓ □a ≤ □(a ⇨ b) ⊓ □a ⊓ □b := by simp [←box_meet];
    _             ≤ □b                 := by simp;

lemma box_axiomK : □(a ⇨ b) ⇨ (□a ⇨ □b) = ⊤ := by
  rw [himp_eq_top_iff];
  exact box_imp_le_box_imp_box;

end ModalAlgebra


namespace ModalAlgebra

class Transitive (α : Type*) extends ModalAlgebra α where
  box_trans {a : α} : □a ≤ □□a
export Transitive (box_trans)
attribute [simp, grind .] box_trans

class Reflexive (α : Type*) extends ModalAlgebra α where
  box_refl {a : α} : □a ≤ a
export Reflexive (box_refl)
attribute [simp, grind .] box_refl

end ModalAlgebra


class InteriorAlgebra (α : Type*) extends ModalAlgebra.Transitive α, ModalAlgebra.Reflexive α where


namespace Entailment.LindenbaumAlgebra

open LO.Entailment
open LO.Modal.Entailment

variable {F S : Type*} [BasicModalLogicalConnective F] [Entailment S F]
         (𝓢 : S) [Modal.Entailment.K 𝓢]

instance [DecidableEq F] : Box (LindenbaumAlgebra 𝓢) where
  box := Quotient.lift (fun φ ↦ ⟦□φ⟧) $ by
    intro φ ψ h;
    simp only [ProvablyEquivalent.setoid, ProvablyEquivalent, Quotient.eq];
    apply box_congruence!;
    assumption;

instance [DecidableEq F] : Dia (LindenbaumAlgebra 𝓢) where
  dia := Quotient.lift (fun φ ↦ ⟦◇φ⟧) $ by
    intro φ ψ h;
    simp only [ProvablyEquivalent.setoid, ProvablyEquivalent, Quotient.eq];
    apply dia_iff!;
    assumption;

@[simp] lemma box_def [DecidableEq F] (φ : F) : □(⟦φ⟧ : LindenbaumAlgebra 𝓢) = ⟦□φ⟧ := rfl
@[simp] lemma dia_def [DecidableEq F] (φ : F) : ◇(⟦φ⟧ : LindenbaumAlgebra 𝓢) = ⟦◇φ⟧ := rfl

instance [DecidableEq F] : ModalAlgebra (LindenbaumAlgebra 𝓢) where
  box_top := by
    suffices 𝓢 ⊢ □⊤ ⭤ ⊤ by
      apply Quotient.eq.mpr;
      simpa;
    apply E!_intro;
    . simp;
    . apply C!_of_conseq!;
      exact axiomN!;
  box_meet φ ψ := by
    induction' φ using Quotient.ind with φ
    induction' ψ using Quotient.ind with ψ
    suffices 𝓢 ⊢ □(φ ⋏ ψ) ⭤ □φ ⋏ □ψ by
      apply Quotient.eq.mpr;
      simpa;
    apply E!_intro;
    . simp;
    . simp;
  dual_dia := by
    intro φ;
    induction' φ using Quotient.ind with φ;
    suffices 𝓢 ⊢ ◇φ ⭤ ∼□(∼φ) by
      apply Quotient.eq.mpr;
      simpa only
    exact dia_duality!;

end Entailment.LindenbaumAlgebra



namespace Modal

variable {α : Type u}

namespace Formula

@[grind]
def value [Bot H] [HImp H] [Box H] (V : α → H) : Formula α → H
  | atom a => V a
  | ⊥      => ⊥
  | φ ➝ ψ  => φ.value V ⇨ ψ.value V
  | □φ     => □(φ.value V)

infix:45 " ⊩ " => value

variable [ModalAlgebra H] {V : α → H} {φ ψ : Formula α}

@[simp, grind .] lemma eq_value_verum : (V ⊩ ⊤) = ⊤ := by simp [value];
@[simp, grind .] lemma eq_value_falsum : (V ⊩ ⊥) = ⊥ := by simp [value];
@[simp, grind =] lemma eq_value_imp : (V ⊩ φ ➝ ψ) = (V ⊩ φ) ⇨ (V ⊩ ψ) := by simp [value];
@[simp, grind =] lemma eq_value_and : (V ⊩ φ ⋏ ψ) = (V ⊩ φ) ⊓ (V ⊩ ψ) := by simp [value];
@[simp, grind =] lemma eq_value_or  : (V ⊩ φ ⋎ ψ) = (V ⊩ φ) ⊔ (V ⊩ ψ) := by simp [value, himp_eq, sup_comm];
@[simp, grind =] lemma eq_value_neg : (V ⊩ ∼φ) = (V ⊩ φ)ᶜ := by simp [value];
@[simp, grind =] lemma eq_value_box : (V ⊩ □φ) = □(V ⊩ φ) := by simp [value];
@[simp, grind =] lemma eq_value_dia : (V ⊩ ◇φ) = ◇(V ⊩ φ) := by simp [ModalAlgebra.dual_dia, value];

end Formula


structure AlgebraicSemantics (α : Type*) where
  Carrier : Type*
  Valuation : α → Carrier
  [modalAlgebra : ModalAlgebra Carrier]
  [nontrivial : Nontrivial Carrier]

namespace AlgebraicSemantics

variable {A : AlgebraicSemantics α} {φ ψ : Formula α}

instance : CoeSort (AlgebraicSemantics α) (Type*) := ⟨Carrier⟩
instance : CoeFun (AlgebraicSemantics α) (λ A => α → A) := ⟨Valuation⟩
instance : ModalAlgebra A := A.modalAlgebra
instance : Nontrivial A := A.nontrivial

instance : Semantics (AlgebraicSemantics α) (Formula α) := ⟨fun A φ ↦ (A ⊩ φ) = ⊤⟩
@[simp, grind =] lemma def_val : A ⊧ φ ↔ (A ⊩ φ) = ⊤ := by rfl

instance : Semantics.Top (AlgebraicSemantics α) := ⟨by grind⟩
instance : Semantics.Bot (AlgebraicSemantics α) := ⟨by simp⟩
instance : Semantics.And (AlgebraicSemantics α) := ⟨by simp⟩

@[grind =]
lemma val_imp : A ⊧ φ ➝ ψ ↔ (A ⊩ φ) ≤ (A ⊩ ψ) := by simp;

@[grind <-]
lemma nec (h : A ⊧ φ) : A ⊧ □φ := by
  replace h : (A ⊩ φ) = ⊤ := h;
  simp [h, ModalAlgebra.box_top];

@[grind →]
lemma mdp (hφψ : A ⊧ φ ➝ ψ) (hφ : A ⊧ φ) : A ⊧ ψ := by
  simp only [def_val, Formula.eq_value_imp, himp_eq_top_iff] at hφψ hφ ⊢;
  rw [eq_top_iff] at hφ ⊢;
  trans (A ⊩ φ);
  . exact hφ;
  . exact hφψ;

variable {Ax : Axiom α}

def mod (Ax : Axiom α) : Set (AlgebraicSemantics α) := Semantics.models (AlgebraicSemantics α) Ax.instances

lemma mod_models_iff : mod.{_,w} Ax ⊧ φ ↔ ∀ ℍ : AlgebraicSemantics.{_,w} α, ℍ ⊧* Ax.instances → ℍ ⊧ φ := by
  simp only [mod, Semantics.models, Semantics.ModelsSet.setOf_iff, def_val, forall_exists_index, and_imp, Semantics.set_models_iff, Set.mem_setOf_eq]

lemma sound (h : Hilbert.Normal Ax ⊢ φ) : mod.{_,w} Ax ⊧ φ := by
  intro A hA;
  induction h using Hilbert.Normal.rec! with
  | axm s hφ =>
    apply hA.models_set;
    exact Axiom.of_mem hφ;
  | implyK | implyS | ec => simp;
  | _ => grind;

instance : Sound (Hilbert.Normal Ax) (mod Ax) := ⟨sound⟩

variable [DecidableEq α] {Ax : Axiom α} [Entailment.Consistent (Hilbert.Normal Ax)] [Entailment.K (Hilbert.Normal Ax)]

def lindenbaum (Ax : Axiom α)
  [Entailment.K (Hilbert.Normal Ax)]
  [Entailment.Consistent (Hilbert.Normal Ax)] : AlgebraicSemantics α where
  Carrier := Entailment.LindenbaumAlgebra (Hilbert.Normal Ax)
  Valuation a := ⟦.atom a⟧

lemma lindenbaum_val_eq {φ} : (lindenbaum Ax ⊩ φ) = ⟦φ⟧ := by
  induction φ with
  | hatom a => rfl
  | hfalsum =>
    simp only [Formula.eq_value_falsum];
    rw [Entailment.LindenbaumAlgebra.bot_def];
  | himp φ ψ ihφ ihψ =>
    simp only [Formula.eq_value_imp, ihφ, ihψ];
    rw [Entailment.LindenbaumAlgebra.himp_def];
  | hbox φ ihφ =>
    simp only [Formula.eq_value_box, ihφ];
    rw [Entailment.LindenbaumAlgebra.box_def];

lemma lindenbaum_complete_iff {φ : Formula α} : lindenbaum Ax ⊧ φ ↔ (Hilbert.Normal Ax) ⊢ φ := by
  simp [AlgebraicSemantics.def_val, lindenbaum_val_eq, Entailment.LindenbaumAlgebra.provable_iff_eq_top]

instance : Sound (Hilbert.Normal Ax) (lindenbaum Ax) := ⟨lindenbaum_complete_iff.mpr⟩
instance : Complete (Hilbert.Normal Ax) (lindenbaum Ax) := ⟨lindenbaum_complete_iff.mp⟩

lemma complete {φ : Formula α} (h : mod.{_,u} Ax ⊧ φ) : (Hilbert.Normal Ax) ⊢ φ := by
  wlog Con : Entailment.Consistent (Hilbert.Normal Ax)
  . exact Entailment.not_consistent_iff_inconsistent.mp Con φ
  apply lindenbaum_complete_iff.mp;
  apply mod_models_iff.mp;
  . exact h;
  . constructor;
    intro ψ hψ;
    apply lindenbaum_complete_iff.mpr;
    grind;

instance instCompleteMod : Complete (Hilbert.Normal Ax) (mod.{_,u} Ax) := ⟨complete⟩

instance : Complete (Modal.K) (mod.{0, 0} Modal.K.axioms) := instCompleteMod

end AlgebraicSemantics

end Modal

end LO
