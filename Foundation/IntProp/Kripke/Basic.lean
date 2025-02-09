import Foundation.Vorspiel.BinaryRelations
import Foundation.IntProp.Hilbert.Basic

namespace LO.IntProp

open System


namespace Kripke

structure Frame where
  World : Type
  [world_nonempty : Nonempty World]
  Rel : Rel World World
  rel_refl : Reflexive Rel
  rel_trans : Transitive Rel

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty
-- instance {F : Frame} : IsPartialOrder _ F.Rel := F.rel_po

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

namespace Frame

variable {F : Frame} {x y z : F.World}

@[refl, simp] lemma rel_refl' : x ≺ x := F.rel_refl x

@[trans] lemma rel_trans' : x ≺ y → y ≺ z → x ≺ z := by apply F.rel_trans

end Frame


abbrev pointFrame : Frame where
  World := Unit
  Rel := fun _ _ => True
  rel_refl := by simp [Reflexive]
  rel_trans := by simp [Transitive]


abbrev FrameClass := Set (Frame)


structure Valuation (F : Frame) where
  Val : F.World → ℕ → Prop
  hereditary : ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (Val w₁ a) → (Val w₂ a)
instance {F : Frame} : CoeFun (Valuation F) (λ _ => F.World → ℕ → Prop) := ⟨Valuation.Val⟩

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke


open Kripke


open Formula

namespace Formula.Kripke

def Satisfies (M : Kripke.Model) (w : M.World) : Formula ℕ → Prop
  | atom a => M w a
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M w φ ∧ Satisfies M w ψ
  | φ ⋎ ψ  => Satisfies M w φ ∨ Satisfies M w ψ
  | φ ➝ ψ => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' φ → Satisfies M w' ψ)

namespace Satisfies

instance semantics (M : Kripke.Model) : Semantics (Formula ℕ) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

variable {M : Kripke.Model} {w w' : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[simp] protected lemma iff_models : w ⊧ φ ↔ Formula.Kripke.Satisfies M w φ := iff_of_eq rfl

@[simp] lemma atom_def : w ⊧ atom a ↔ M w a := by simp [Satisfies];

@[simp] lemma top_def  : w ⊧ ⊤ ↔ True := by simp [Satisfies];

@[simp] lemma bot_def  : w ⊧ ⊥ ↔ False := by simp [Satisfies];

@[simp] lemma and_def  : w ⊧ φ ⋏ ψ ↔ w ⊧ φ ∧ w ⊧ ψ := by simp [Satisfies];

@[simp] lemma or_def   : w ⊧ φ ⋎ ψ ↔ w ⊧ φ ∨ w ⊧ ψ := by simp [Satisfies];

@[simp] lemma imp_def  : w ⊧ φ ➝ ψ ↔ ∀ {w' : M.World}, (w ≺ w') → (w' ⊧ φ → w' ⊧ ψ) := by simp [Satisfies, imp_iff_not_or];

@[simp] lemma neg_def  : w ⊧ ∼φ ↔ ∀ {w' : M.World}, (w ≺ w') → ¬(w' ⊧ φ) := by simp [Satisfies];

instance : Semantics.Top M.World where
  realize_top := by simp [Satisfies];

instance : Semantics.Bot M.World where
  realize_bot := by simp [Satisfies];

instance : Semantics.And M.World where
  realize_and := by simp [Satisfies];

instance : Semantics.Or M.World where
  realize_or := by simp [Satisfies];

lemma formula_hereditary
  (hw : w ≺ w') : w ⊧ φ → w' ⊧ φ := by
  induction φ using Formula.rec' with
  | hatom => apply M.Val.hereditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq $ M.rel_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

lemma neg_equiv : w ⊧ ∼φ ↔ w ⊧ φ ➝ ⊥ := by simp_all [Satisfies];

lemma iff_subst_self {F : Frame} {V : Valuation F} {x : F.World} (s) :
  letI U : Kripke.Valuation F := ⟨
    λ w a => Satisfies ⟨F, V⟩ w ((.atom a)⟦s⟧),
    fun {_ _} Rwv {_} => formula_hereditary Rwv
  ⟩;
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ using Formula.rec' generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
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
      apply Satisfies.and_def.mpr;
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

end Satisfies


open Satisfies

def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

variable {M : Model} {φ ψ χ : Formula ℕ}

@[simp] protected lemma iff_models : M ⊧ φ ↔ Formula.Kripke.ValidOnModel M φ := iff_of_eq rfl


protected lemma verum : M ⊧ ⊤ := by simp [ValidOnModel, Satisfies];

instance : Semantics.Top (Model) := ⟨λ _ => ValidOnModel.verum⟩


protected lemma bot : ¬M ⊧ ⊥ := by simp [ValidOnModel, Satisfies];

instance : Semantics.Bot (Model) := ⟨λ _ => ValidOnModel.bot⟩


lemma iff_not_exists_world {M : Kripke.Model} : (¬M ⊧ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world

protected lemma andElim₁ : M ⊧ φ ⋏ ψ ➝ φ := by simp_all [ValidOnModel, Satisfies];

protected lemma andElim₂ : M ⊧ φ ⋏ ψ ➝ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma andInst₃ : M ⊧ φ ➝ ψ ➝ φ ⋏ ψ := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z φ := formula_hereditary Ryz hp;
  exact ⟨hp, hq⟩;

protected lemma orInst₁ : M ⊧ φ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma orInst₂ : M ⊧ ψ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma orElim : M ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.rel_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma imply₁ : M ⊧ φ ➝ ψ ➝ φ := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary Ryz hp;

protected lemma imply₂ : M ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw : y ≺ w := Frame.rel_trans' Ryz Rzw;
  have Rww : w ≺ w := Frame.rel_refl';
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w Frame.rel_refl' $ hp w;

protected lemma efq : M ⊧ Axioms.EFQ φ := by simp [ValidOnModel, Satisfies];

protected lemma lem : Symmetric M.Rel → M ⊧ Axioms.LEM φ := by
  unfold Symmetric Axioms.LEM;
  contrapose;
  push_neg;
  intro h;
  obtain ⟨x, ⟨hnxφ, ⟨y, Rxy, hyφ⟩⟩⟩ := by simpa [Satisfies] using exists_world_of_not h;
  use x, y;
  constructor;
  . assumption;
  . by_contra Ryx;
    have : x ⊧ φ := formula_hereditary Ryx hyφ;
    contradiction;

protected lemma dum : Connected M.Rel → M ⊧ Axioms.Dummett φ ψ := by
  unfold Connected Axioms.Dummett;
  contrapose;
  push_neg;
  intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ, nhyψ⟩, ⟨z, Ryz, hzψ, nhyφ⟩⟩ := by
    simpa [Satisfies] using exists_world_of_not h;
  use x, y, z;
  refine ⟨⟨Rxy, Ryz⟩, ?_, ?_⟩;
  . by_contra Ryz;
    have : z ⊧ φ := formula_hereditary Ryz hyφ;
    contradiction;
  . by_contra Rzy;
    have : y ⊧ ψ := formula_hereditary Rzy hzψ;
    contradiction;

protected lemma wlem : Confluent M.Rel → M ⊧ Axioms.WeakLEM φ := by
  unfold Confluent Axioms.WeakLEM;
  contrapose;
  push_neg;
  intro h;
  obtain ⟨x, ⟨y, Rxy, hyφ⟩, ⟨z, Rxz, hz⟩⟩ := by
    simpa [Satisfies] using exists_world_of_not h;
  use x, y, z;
  refine ⟨⟨Rxy, Rxz⟩, ?_⟩;
  . rintro w Ryw;
    by_contra Rzw;
    have : w ⊧ φ := formula_hereditary Ryw hyφ;
    have : ¬w ⊧ φ := hz w Rzw;
    contradiction;

end ValidOnModel


def ValidOnFrame (F : Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ


namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame} {φ ψ χ : Formula ℕ}

@[simp] protected lemma models_iff : F ⊧ φ ↔ ValidOnFrame F φ := iff_of_eq rfl

protected lemma top : F ⊧ ⊤ := by tauto;
instance : Semantics.Top (Frame) := ⟨λ _ => ValidOnFrame.top⟩

protected lemma bot : ¬F ⊧ ⊥ := by
  simp [ValidOnFrame.models_iff, ValidOnFrame];
  use ⟨(λ _ _ => True), by tauto⟩;
instance : Semantics.Bot (Frame) := ⟨λ _ => ValidOnFrame.bot⟩


lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ¬(⟨F, V⟩ : Kripke.Model) ⊧ φ) := by
  simp [ValidOnFrame];

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation


lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F, ∃ x : (⟨F, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, Satisfies, ValidOnModel, Semantics.Realize];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world


lemma iff_not_exists_model_world :  (¬F ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame = F ∧ ¬(x ⊧ φ)) := by
  constructor;
  . intro h;
    obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h;
    use ⟨F, V⟩, x;
    tauto;
  . rintro ⟨M, x, rfl, h⟩;
    exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world


protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  apply h;

protected lemma andElim₁ : F ⊧ φ ⋏ ψ ➝ φ := fun _ => ValidOnModel.andElim₁

protected lemma andElim₂ : F ⊧ φ ⋏ ψ ➝ ψ := fun _ => ValidOnModel.andElim₂

protected lemma andInst₃ : F ⊧ φ ➝ ψ ➝ φ ⋏ ψ := fun _ => ValidOnModel.andInst₃

protected lemma orInst₁ : F ⊧ φ ➝ φ ⋎ ψ := fun _ => ValidOnModel.orInst₁

protected lemma orInst₂ : F ⊧ ψ ➝ φ ⋎ ψ := fun _ => ValidOnModel.orInst₂

protected lemma orElim : F ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := fun _ => ValidOnModel.orElim

protected lemma imply₁ : F ⊧ φ ➝ ψ ➝ φ := fun _ => ValidOnModel.imply₁

protected lemma imply₂ : F ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := fun _ => ValidOnModel.imply₂

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := fun V x => ValidOnModel.mdp (hpq V) (hp V) x

protected lemma efq : F ⊧ Axioms.EFQ φ := fun _ => ValidOnModel.efq

protected lemma lem (F_symm : Symmetric F.Rel) : F ⊧ Axioms.LEM φ := fun _ => ValidOnModel.lem F_symm

protected lemma dum (F_conn : Connected F.Rel) : F ⊧ Axioms.Dummett φ ψ := fun _ => ValidOnModel.dum F_conn

protected lemma wlem (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM φ := fun _ => ValidOnModel.wlem F_conf

end ValidOnFrame


@[simp] def ValidOnFrameClass (C : FrameClass) (φ : Formula ℕ) := ∀ F, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

instance semantics : Semantics (Formula ℕ) (FrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

protected lemma bot (h_nonempty : C.Nonempty) : ¬C ⊧ ⊥ := by
  simp [ValidOnFrameClass.models_iff, ValidOnFrameClass];
  exact h_nonempty;

lemma iff_not_exists_frame {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame

lemma iff_not_exists_model {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ M : Kripke.Model, M.toFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_model_of_not, not_of_exists_model⟩ := iff_not_exists_model


lemma iff_not_exists_model_world {C : Kripke.FrameClass} : (¬C ⊧ φ) ↔ (∃ M : Kripke.Model, ∃ x : M.World, M.toFrame ∈ C ∧ ¬(x ⊧ φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world

end ValidOnFrameClass

end Formula.Kripke



namespace Kripke

namespace FrameClass

variable {C : FrameClass} {φ ψ χ : Formula ℕ}

class DefinedBy (C : Kripke.FrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

class FiniteDefinedBy (C Γ) extends FrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ

abbrev DefinedByFormula (C : Kripke.FrameClass) (φ : Formula ℕ) := FrameClass.DefinedBy C {φ}

lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ F ⊧ φ) : DefinedByFormula C φ := by
  constructor;
  simpa;

instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  . rintro ⟨hF₁, hF₂⟩;
    rintro φ (hφ₁ | hφ₂);
    . exact h₁.defines F |>.mp hF₁ _ hφ₁;
    . exact h₂.defines F |>.mp hF₂ _ hφ₂;
  . intro h;
    constructor;
    . apply h₁.defines F |>.mpr;
      intro φ hφ;
      apply h;
      left;
      assumption;
    . apply h₂.defines F |>.mpr;
      intro φ hφ;
      apply h;
      right;
      assumption;
⟩

instance definedByFormula_inter
  (C₁ φ₁) [DefinedByFormula C₁ φ₁]
  (C₂ φ₂) [DefinedByFormula C₂ φ₂]
  : DefinedBy (C₁ ∩ C₂) {φ₁, φ₂} := definedBy_inter C₁ {φ₁} C₂ {φ₂}


class IsNonempty (C : Kripke.FrameClass) : Prop where
  nonempty : Nonempty C

end FrameClass


abbrev AllFrameClass : FrameClass := Set.univ

instance AllFrameClass.DefinedBy : AllFrameClass.DefinedByFormula (Axioms.EFQ (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate $ by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.efq;

instance AllFrameClass.IsNonempty : AllFrameClass.IsNonempty := by
  use pointFrame;
  trivial;


namespace FrameClass

variable {C : Kripke.FrameClass} {Γ : Set (Formula ℕ)}

instance definedBy_with_axiomEFQ (defines : C.DefinedBy Γ) : DefinedBy C (insert (Axioms.EFQ (.atom 0)) Γ) := by
  convert definedBy_inter AllFrameClass {Axioms.EFQ (.atom 0)} C Γ
  tauto_set;

end FrameClass

end Kripke

end LO.IntProp
