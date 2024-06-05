import Logic.Vorspiel.BinaryRelations
import Logic.Logic.Semantics
import Logic.Propositional.Superintuitionistic.Formula

namespace LO.Propositional.Superintuitionistic

namespace Kripke

attribute [simp] Reflexive Transitive Antisymmetric in
structure Frame where
  World : Type u
  World_nonempty : Nonempty World := by infer_instance
  Rel : World → World → Prop
  Rel_refl : Reflexive Rel := by aesop
  Rel_trans : Transitive Rel := by aesop
  Rel_antisymm : Antisymmetric Rel := by aesop

structure FiniteFrame extends Frame where
  World_finite : Finite World := by infer_instance

instance : CoeSort Frame Type* where coe := Frame.World

instance (F : Frame) : Nonempty F.World := F.World_nonempty

set_option linter.unusedVariables false in
abbrev Frame' (α : Type*) := Frame

set_option linter.unusedVariables false in
abbrev FiniteFrame' (α : Type*) := FiniteFrame

def FiniteFrame.toFrame' {α : Type*} (F : FiniteFrame) : Frame' α := F.toFrame

abbrev Frame.Rel' {F : Frame} (w w' : F.World) := F.Rel w w'
scoped infix:45 " ≺ " => Frame.Rel'


abbrev Valuation (W α : Type u) := W → α → Prop

structure Model (α) where
  Frame : Frame' α
  Valuation : Valuation Frame.World α
  hereditary : ∀ {w₁ w₂}, (w₁ ≺ w₂) → ∀ {a}, (Valuation w₁ a) → (Valuation w₂ a)

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type u) where coe := Model.World

abbrev Model.Rel (M : Model α) := M.Frame.Rel


abbrev FrameClass := Set Frame

set_option linter.unusedVariables false in
abbrev FrameClass' (α : Type*) := FrameClass

class FrameClass.IsNonempty (𝔽 : FrameClass) where
  nonempty : ∃ F, 𝔽 F



abbrev FiniteFrameClass := Set FiniteFrame

set_option linter.unusedVariables false in
abbrev FiniteFrameClass' (α : Type*) := FiniteFrameClass

class FiniteFrameClass.IsNonempty (𝔽 : FiniteFrameClass) where
  nonempty : ∃ F, 𝔽 F


abbrev FrameProperty := Frame → Prop

abbrev FiniteFrameProperty := FiniteFrame → Prop

section

end

end Kripke

open System
open Kripke

variable [Inhabited α]

def Formula.Kripke.Satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a => M.Valuation w a
  | ⊤      => True
  | ⊥      => False
  | p ⋏ q  => Satisfies M w p ∧ Satisfies M w q
  | p ⋎ q  => Satisfies M w p ∨ Satisfies M w q
  | p ⟶ q => ∀ {w'}, (w ≺ w') → (¬Satisfies M w' p ∨ Satisfies M w' q)

instance instKripkeSemanticsFormulaWorld (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

open Formula.Kripke

namespace Formula.Kripke.Satisfies

variable {M : Model α}

@[simp] protected lemma iff_models : w ⊧ p ↔ Formula.Kripke.Satisfies M w p := iff_of_eq rfl

local infix:45 " ⊩ " => Formula.Kripke.Satisfies M

@[simp] lemma atom_def : w ⊩ atom a ↔ M.Valuation w a := by simp [Satisfies];
@[simp] lemma top_def  : w ⊩ ⊤ ↔ True := by simp [Satisfies];
@[simp] lemma bot_def  : w ⊩ ⊥ ↔ False := by simp [Satisfies];
@[simp] lemma and_def  : w ⊩ p ⋏ q ↔ w ⊩ p ∧ w ⊩ q := by simp [Satisfies];
@[simp] lemma or_def   : w ⊩ p ⋎ q ↔ w ⊩ p ∨ w ⊩ q := by simp [Satisfies];
@[simp] lemma imp_def  : w ⊩ p ⟶ q ↔ ∀ {w'}, (w ≺ w') → (w' ⊩ p → w' ⊩ q) := by simp [Satisfies, imp_iff_not_or];
@[simp] lemma neg_def  : w ⊩ ~p ↔ ∀ {w'}, (w ≺ w') → ¬(w' ⊩ p) := by simp [NegDefinition.neg];

instance : Semantics.Top M.World where
  realize_top := by simp [Satisfies];

instance : Semantics.Bot M.World where
  realize_bot := by simp [Satisfies];

instance : Semantics.And M.World where
  realize_and := by simp [Satisfies];

instance : Semantics.Or M.World where
  realize_or := by simp [Satisfies];

lemma formula_hereditary (hw : w ≺ w') : w ⊩ p → w' ⊩ p := by
  induction p using Formula.rec' with
  | hatom => apply M.hereditary hw;
  | himp =>
    simp_all [Satisfies];
    intro hpq v hv;
    exact hpq $ M.Frame.Rel_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

/-
lemma hereditary_int {M : Model (𝐈𝐧𝐭 W α)} {w w' : W} {p : Formula α} (hw : M.frame w w') : (M, w) ⊧ p → (M, w') ⊧ p := by
  apply hereditary (by simp [FrameClass.Intuitionistic]; tauto) hw;
-/

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel (M : Model α) (p : Formula α) := ∀ w : M.World, w ⊧ p

instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace Formula.Kripke.ValidOnModel

@[simp] protected lemma iff_models : M ⊧ p ↔ Formula.Kripke.ValidOnModel M p := iff_of_eq rfl

-- variable {𝔽 : FrameClass W α} (hTrans : 𝔽 ⊆ { F | Transitive F }) (hRefl : 𝔽 ⊆ { F | Reflexive F })
variable {M : Model α} {p q r : Formula α}

@[simp] protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

@[simp] protected lemma conj₁ : M ⊧ p ⋏ q ⟶ p := by simp_all [ValidOnModel];

@[simp] protected lemma conj₂ : M ⊧ p ⋏ q ⟶ q := by simp_all [ValidOnModel];

@[simp] protected lemma conj₃ : M ⊧ p ⟶ q ⟶ p ⋏ q := by
  simp_all [ValidOnModel];
  intro w₁ w₂ _ hp w₃ hw₂₃ _;
  exact Satisfies.formula_hereditary hw₂₃ hp;

@[simp] protected lemma disj₁ : M ⊧ p ⟶ p ⋎ q := by simp_all [ValidOnModel];

@[simp] protected lemma disj₂ : M ⊧ q ⟶ p ⋎ q := by simp_all [ValidOnModel];

@[simp] protected lemma disj₃ : M ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.Frame.Rel_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

@[simp] protected lemma imply₁ : M ⊧ p ⟶ q ⟶ p := by
  simp_all [ValidOnModel];
  intro w₁ w₂ _ hp w₃ hw₂₃ _;
  exact Satisfies.formula_hereditary hw₂₃ hp;

@[simp] protected lemma imply₂ : M ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def];
  intro w₁ w₂ _ hpqr w₃ hw₂₃ hpq w₄ hw₃₄ hp;
  exact hpqr (M.Frame.Rel_trans hw₂₃ hw₃₄) hp (M.Frame.Rel_refl w₄) (hpq hw₃₄ hp);

@[simp] protected lemma mdp (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  simp_all [ValidOnModel];
  intro w;
  exact hpq _ (M.Frame.Rel_refl w);

@[simp] protected lemma efq : M ⊧ Axioms.EFQ p := by simp_all [ValidOnModel];

@[simp] protected lemma lem (hExt : Extensive M.Rel) : M ⊧ Axioms.LEM p := by
  simp_all [ValidOnModel];
  intro w;
  by_cases h : w ⊧ p
  . left; assumption;
  . right;
    intro w' hww';
    rw [←(hExt hww')];
    assumption;

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame) (p : Formula α) := ∀ (V : Valuation F.World α), (h : _) → (Model.mk F V h) ⊧ p

instance : Semantics (Formula α) (Frame' α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

namespace Formula.Kripke.ValidOnFrame

@[simp] protected lemma models_iff {F : Frame' α} : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl


variable {F : Frame' α} {p q r : Formula α}

@[simp] protected lemma verum : F ⊧ ⊤ := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.verum;

@[simp] protected lemma conj₁ : F ⊧ p ⋏ q ⟶ p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.conj₁;

@[simp] protected lemma conj₂ : F ⊧ p ⋏ q ⟶ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.conj₂;

@[simp] protected lemma conj₃ : F ⊧ p ⟶ q ⟶ p ⋏ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.conj₃;

@[simp] protected lemma disj₁ : F ⊧ p ⟶ p ⋎ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.disj₁;

@[simp] protected lemma disj₂ : F ⊧ q ⟶ p ⋎ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.disj₂;

@[simp] protected lemma disj₃ : F ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.disj₃;

@[simp] protected lemma imply₁ : F ⊧ p ⟶ q ⟶ p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.imply₁;

@[simp] protected lemma imply₂ : F ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.imply₂;

@[simp] protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros V hV;
  exact ValidOnModel.mdp (hpq V hV) (hp V hV);

@[simp] protected lemma efq : F ⊧ Axioms.EFQ p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.efq;

@[simp] protected lemma lem (hExt : Extensive F.Rel) : F ⊧ Axioms.LEM p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; exact ValidOnModel.lem hExt;

instance : Semantics.Bot (Frame' α) where
  realize_bot _ := by
    simp [ValidOnModel, ValidOnFrame];
    existsi (λ _ _ => True);
    simp_all;

end Formula.Kripke.ValidOnFrame


@[simp] def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {F : Frame' α}, F ∈ 𝔽 → F ⊧ p

instance : Semantics (Formula α) (FrameClass' α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFrameClass

@[simp] protected lemma iff_models {𝔽 : FrameClass' α} : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl

end Formula.Kripke.ValidOnFrameClass

@[simp] def Formula.Kripke.ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass) (f : Formula α) := ∀ (F : FiniteFrame' α), F ∈ 𝔽 → F.toFrame' ⊧ f

instance : Semantics (Formula α) (FiniteFrameClass' α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFiniteFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFiniteFrameClass

@[simp] protected lemma models_iff {𝔽 : FiniteFrameClass' α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFiniteFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFiniteFrameClass


namespace Kripke

def AxiomSetFrameClass (Ax : AxiomSet α) : FrameClass' α := { (F : Frame' α) | F ⊧* Ax }
notation "𝔽(" Ax ")" => Kripke.AxiomSetFrameClass Ax

def AxiomSetFiniteFrameClass (Ax : AxiomSet α) : FiniteFrameClass' α := { (F : FiniteFrame' α) | F.toFrame' ⊧* Ax }
notation "𝔽ꟳ(" Ax ")" => Kripke.AxiomSetFiniteFrameClass Ax

variable {Ax : AxiomSet α}

lemma validOnAxiomSetFrameClass_axiom (h : p ∈ Ax) : 𝔽(Ax) ⊧ p := by intro F hF; exact hF.realize h;

class Definability (Ax : AxiomSet α) (P : FrameProperty) where
  defines : ∀ (F : Frame' α), F ⊧* Ax ↔ P F

lemma iff_definability_memAxiomSetFrameClass (definability : Definability Ax P) : ∀ {F : Frame' α}, F ∈ 𝔽(Ax) ↔ P F := by
  apply Definability.defines;

class FiniteDefinability (Ax : AxiomSet α) (P : FiniteFrameProperty) where
  defines : ∀ (F : FiniteFrame' α), F.toFrame' ⊧* Ax ↔ P F

lemma iff_definability_memAxiomSetFiniteFrameClass (definability : FiniteDefinability Ax P) : ∀ {F : FiniteFrame' α}, F ∈ 𝔽ꟳ(Ax) ↔ P F := by
  apply definability.defines;

end Kripke

instance AxiomSet.EFQ.definability : Definability (α := α) 𝗘𝗙𝗤 (λ _ => True) where
  defines F := by simp; intros; apply ValidOnFrame.efq

instance AxiomSet.EFQ.nonempty : FrameClass.IsNonempty (𝔽(𝗘𝗙𝗤) : FrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ x y => x ≤ y };
    apply iff_definability_memAxiomSetFrameClass AxiomSet.EFQ.definability |>.mpr;
    trivial;

instance AxiomSet.LEM.definability : Definability (α := α) 𝗟𝗘𝗠 (λ F => Euclidean F.Rel) where
  defines F := by
    simp;
    constructor;
    . intro h x y z hxy hyz;
      let V : Valuation F.World α := (λ v _ => z ≺ v);
      let M := Model.mk F V (by
        simp [V];
        intros _ _ hvu hzv;
        exact F.Rel_trans hzv hvu;
      );
      let p : Formula α := Formula.atom default;

      have : Satisfies M z p := by simp [p, V]; exact F.Rel_refl _;
      have : ¬(Satisfies M x (~p)) := by simp; existsi z; simp_all;
      have : Satisfies M x p := by
        have := Formula.Kripke.Satisfies.or_def.mp $ h p V M.hereditary x;
        aesop;
      have : Satisfies M y p := Formula.Kripke.Satisfies.formula_hereditary hxy this;
      simpa [Satisfies, V] using this;
    . intros hEucl _;
      apply ValidOnFrame.lem;
      intro x y hxy;
      exact F.Rel_antisymm hxy $ hEucl (F.Rel_refl x) hxy;

instance : FrameClass.IsNonempty (𝔽(𝗟𝗘𝗠) : FrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ x y => x ≤ y };
    apply iff_definability_memAxiomSetFrameClass AxiomSet.LEM.definability |>.mpr;
    simp [Euclidean];

end LO.Propositional.Superintuitionistic
