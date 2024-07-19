import Logic.Vorspiel.BinaryRelations
import Logic.Logic.Semantics
import Logic.Propositional.Superintuitionistic.Formula

namespace LO.Propositional.Superintuitionistic

namespace Kripke

attribute [simp] Reflexive Transitive Antisymmetric in
structure Frame where
  World : Type u
  World_nonempty : Inhabited World := by infer_instance
  [World_decEq : DecidableEq World]
  Rel : World → World → Prop
  Rel_refl : Reflexive Rel := by aesop
  Rel_trans : Transitive Rel := by aesop
  Rel_antisymm : Antisymmetric Rel := by aesop

instance {F : Frame} : DecidableEq F.World := F.World_decEq

structure FiniteFrame extends Frame where
  World_finite : Finite World := by infer_instance

instance : CoeSort Frame Type* where coe := Frame.World

instance (F : Frame) : Inhabited F.World := F.World_nonempty

set_option linter.unusedVariables false in
abbrev Frame' (α : Type*) := Frame

set_option linter.unusedVariables false in
abbrev FiniteFrame' (α : Type*) := FiniteFrame

def FiniteFrame.toFrame' {α : Type*} (F : FiniteFrame) : Frame' α := F.toFrame

abbrev Frame.Rel' {F : Frame} (w w' : F.World) := F.Rel w w'
scoped infix:45 " ≺ " => Frame.Rel'

abbrev Frame.defaultWorld {F : Frame} : F.World := F.World_nonempty.default
-- NOTE: not `@`, `﹫` (U+FE6B)
scoped notation "﹫" => Frame.defaultWorld

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
  nonempty : ∃ F, F ∈ 𝔽



abbrev FiniteFrameClass := Set FiniteFrame

set_option linter.unusedVariables false in
abbrev FiniteFrameClass' (α : Type*) := FiniteFrameClass

class FiniteFrameClass.IsNonempty (𝔽 : FiniteFrameClass) where
  nonempty : ∃ F, F ∈ 𝔽


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
  | ~p     => ∀ {w'}, (w ≺ w') → ¬Satisfies M w' p
  | p ⟶ q => ∀ {w'}, (w ≺ w') → (Satisfies M w' p → Satisfies M w' q)

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
@[simp] lemma neg_def  : w ⊩ ~p ↔ ∀ {w'}, (w ≺ w') → ¬(w' ⊩ p) := by simp [Satisfies];

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
  | hneg =>
    simp_all [Satisfies];
    intro hp v hv;
    exact hp $ M.Frame.Rel_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

/-
lemma hereditary_int {M : Model (𝐈𝐧𝐭 W α)} {w w' : W} {p : Formula α} (hw : M.frame w w') : (M, w) ⊧ p → (M, w') ⊧ p := by
  apply hereditary (by simp [FrameClass.Intuitionistic]; tauto) hw;
-/

lemma neg_equiv : w ⊩ ~p ↔ w ⊩ p ⟶ ⊥ := by simp_all [Satisfies];

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel (M : Model α) (p : Formula α) := ∀ w : M.World, w ⊧ p

instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace Formula.Kripke.ValidOnModel

@[simp] protected lemma iff_models : M ⊧ p ↔ Formula.Kripke.ValidOnModel M p := iff_of_eq rfl

-- variable {𝔽 : FrameClass W α} (hTrans : 𝔽 ⊆ { F | Transitive F }) (hRefl : 𝔽 ⊆ { F | Reflexive F })
variable {M : Model α} {p q r : Formula α}

@[simp] protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

@[simp] protected lemma and₁ : M ⊧ p ⋏ q ⟶ p := by simp_all [ValidOnModel];

@[simp] protected lemma and₂ : M ⊧ p ⋏ q ⟶ q := by simp_all [ValidOnModel];

@[simp] protected lemma and₃ : M ⊧ p ⟶ q ⟶ p ⋏ q := by
  simp_all [ValidOnModel];
  intro w₁ w₂ _ hp w₃ hw₂₃ _;
  exact Satisfies.formula_hereditary hw₂₃ hp;

@[simp] protected lemma or₁ : M ⊧ p ⟶ p ⋎ q := by simp_all [ValidOnModel];

@[simp] protected lemma or₂ : M ⊧ q ⟶ p ⋎ q := by simp_all [ValidOnModel];

@[simp] protected lemma or₃ : M ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
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

@[simp] protected lemma neg_equiv : M ⊧ Axioms.NegEquiv p := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

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

@[simp] protected lemma and₁ : F ⊧ p ⋏ q ⟶ p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.and₁;

@[simp] protected lemma and₂ : F ⊧ p ⋏ q ⟶ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.and₂;

@[simp] protected lemma and₃ : F ⊧ p ⟶ q ⟶ p ⋏ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.and₃;

@[simp] protected lemma or₁ : F ⊧ p ⟶ p ⋎ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.or₁;

@[simp] protected lemma or₂ : F ⊧ q ⟶ p ⋎ q := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.or₂;

@[simp] protected lemma or₃ : F ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.or₃;

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

@[simp] protected lemma neg_equiv : F ⊧ Axioms.NegEquiv p := by
  simp_all only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models];
  intros; apply ValidOnModel.neg_equiv;

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

instance Definability.instUnion (definability₁ : Definability Ax₁ P₁) (definability₂ : Definability Ax₂ P₂) : Definability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact Definability.defines F |>.mp h.1;
      . exact Definability.defines F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Definability.defines F |>.mpr h.1;
      . apply Definability.defines F |>.mpr h.2;

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

instance AxiomSet.EFQ.instDefinabilityUnion (definability : Definability Ax P) : Definability (𝗘𝗙𝗤 ∪ Ax) P := by simpa using Definability.instUnion AxiomSet.EFQ.definability definability;

instance AxiomSet.EFQ.instUnionNonempty [FrameClass.IsNonempty 𝔽(Ax)] (definability : Definability Ax P) : FrameClass.IsNonempty (𝔽(𝗘𝗙𝗤 ∪ Ax) : FrameClass' α) where
  nonempty := by
    obtain ⟨F, hF⟩ := FrameClass.IsNonempty.nonempty (𝔽 := 𝔽(Ax));
    existsi F;
    apply iff_definability_memAxiomSetFrameClass (AxiomSet.EFQ.instDefinabilityUnion definability) |>.mpr;
    apply iff_definability_memAxiomSetFrameClass definability |>.mp hF;

end LO.Propositional.Superintuitionistic
