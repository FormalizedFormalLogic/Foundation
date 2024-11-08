import Foundation.Vorspiel.BinaryRelations
import Foundation.IntProp.Deduction

universe u v

namespace LO.IntProp

open System


namespace Kripke

structure Frame where
  World : Type u
  [World_nonempty : Nonempty World]
  Rel : Rel World World
  trans_Rel : Transitive Rel
  refl_Rel : Reflexive Rel

instance : CoeSort Frame (Type u) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.World_nonempty

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'


set_option linter.unusedVariables false in
abbrev Frame.Dep (α : Type v) := Frame.{u}

abbrev Frame.alt (F : Frame.{u}) (α : Type v) : Frame.Dep α := F
notation F:max "#" α:max => Frame.alt F α

abbrev pointframe : Frame where
  World := Unit
  Rel := fun _ _ => True
  refl_Rel := by simp [Reflexive];
  trans_Rel := by simp [Transitive];

namespace pointframe

lemma is_reflexive : Reflexive pointframe.Rel := pointframe.refl_Rel

lemma is_transitive : Transitive pointframe.Rel := pointframe.trans_Rel

lemma is_connected : Connected pointframe.Rel := by simp [Connected];

lemma is_confluent : Confluent pointframe.Rel := by simp [Confluent];

end pointframe


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
abbrev FrameClass.Dep (α : Type v) := FrameClass.{u}

abbrev FrameClass.alt (C : FrameClass) (α : Type v) : FrameClass.Dep.{u} α := C
notation:max C:max "#" α:max => FrameClass.alt C α

section

abbrev SymmetricFrameClass := { F : Kripke.Frame | Symmetric F }

abbrev ConfluentFrameClass := { F : Kripke.Frame | Confluent F }

abbrev ConnectedFrameClass := { F : Kripke.Frame | Connected F }

end


abbrev Valuation (F : Frame) (α : Type*) := F.World → α → Prop

structure Model (α) extends Frame where
  Valuation : Valuation _ α
  hereditary : ∀ {w₁ w₂ : World}, (w₁ ≺ w₂) → ∀ {a}, (Valuation w₁ a) → (Valuation w₂ a)

end Kripke


open Kripke


open Formula

variable {α : Type u}

namespace Formula.Kripke

def Satisfies (M : Kripke.Model.{u, v} α) (w : M.World) : Formula α → Prop
  | atom a => M.Valuation w a
  | ⊤      => True
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M w φ ∧ Satisfies M w ψ
  | φ ⋎ ψ  => Satisfies M w φ ∨ Satisfies M w ψ
  | ∼φ     => ∀ {w' : M.World}, (w ≺ w') → ¬Satisfies M w' φ
  | φ ➝ ψ => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' φ → Satisfies M w' ψ)

namespace Satisfies

instance semantics (M : Kripke.Model.{u, v} α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

variable {M : Kripke.Model α} {w : M.World} {φ ψ χ : Formula α}

@[simp] protected lemma iff_models : w ⊧ φ ↔ Formula.Kripke.Satisfies M w φ := iff_of_eq rfl

@[simp] lemma atom_def : w ⊧ atom a ↔ M.Valuation w a := by simp [Satisfies];
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
  | hatom => apply M.hereditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq $ M.trans_Rel hw hv;
  | hneg =>
    intro hp v hv;
    exact hp $ M.trans_Rel hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];


lemma neg_equiv : w ⊧ ∼φ ↔ w ⊧ φ ➝ ⊥ := by simp_all [Satisfies];

end Satisfies


open Satisfies


def ValidOnModel (M : Kripke.Model α) (φ : Formula α) := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

variable {M : Model α} {φ ψ χ : Formula α}

@[simp] protected lemma iff_models : M ⊧ φ ↔ Formula.Kripke.ValidOnModel M φ := iff_of_eq rfl

protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

protected lemma and₁ : M ⊧ φ ⋏ ψ ➝ φ := by simp_all [ValidOnModel, Satisfies];

protected lemma and₂ : M ⊧ φ ⋏ ψ ➝ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma and₃ : M ⊧ φ ➝ ψ ➝ φ ⋏ ψ := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z φ := formula_hereditary Ryz hp;
  exact ⟨hp, hq⟩;

protected lemma or₁ : M ⊧ φ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma or₂ : M ⊧ ψ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma or₃ : M ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (M.trans_Rel hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma imply₁ : M ⊧ φ ➝ ψ ➝ φ := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary Ryz hp;

protected lemma imply₂ : M ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw := M.trans_Rel Ryz Rzw;
  have Rww := M.refl_Rel w;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w (M.refl_Rel w) $ hp w;

protected lemma bot : ¬M ⊧ ⊥ := by simp [ValidOnModel, Satisfies];

instance : Semantics.Bot (Kripke.Model α) := ⟨λ _ => ValidOnModel.bot⟩

protected lemma efq : M ⊧ Axioms.EFQ φ := by simp [ValidOnModel, Satisfies];

protected lemma neg_equiv : M ⊧ Axioms.NegEquiv φ := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

protected lemma lem : Symmetric M.Rel → M ⊧ Axioms.LEM φ := by
  simp_all [ValidOnModel, Satisfies, Symmetric];
  contrapose; push_neg;
  rintro ⟨x, nhxp, ⟨y, Rxy, hyp⟩⟩;
  use x, y;
  constructor;
  . exact Rxy;
  . by_contra Ryx;
    have := formula_hereditary Ryx hyp;
    contradiction;

protected lemma dum : Connected M.Rel → M ⊧ Axioms.GD φ ψ := by
  simp [ValidOnModel, Satisfies, Connected];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp, nhyq⟩, ⟨z, Ryz, hzq, nhyp⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Ryz, ?_, ?_⟩;
  . by_contra Ryz;
    have := formula_hereditary Ryz hyp;
    contradiction;
  . by_contra Rzy;
    have := formula_hereditary Rzy hzq;
    contradiction;

protected lemma wlem : Confluent M.Rel → M ⊧ Axioms.WeakLEM φ := by
  simp [ValidOnModel, Satisfies, Confluent];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp⟩, ⟨z, Rxz, hz⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  rintro w Ryw;
  by_contra Rzw;
  have := formula_hereditary Ryw hyp;
  have := hz w Rzw;
  contradiction;

end ValidOnModel


def ValidOnFrame (F : Frame) (φ : Formula α) := ∀ {V : Valuation F α}, {V_hereditary : _} → (⟨F, V, V_hereditary⟩ : Kripke.Model α) ⊧ φ


namespace ValidOnFrame

instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl

variable {F : Frame.Dep α} {φ ψ χ : Formula α}

protected lemma verum : F ⊧ ⊤ := ValidOnModel.verum

protected lemma and₁ : F ⊧ φ ⋏ ψ ➝ φ := ValidOnModel.and₁

protected lemma and₂ : F ⊧ φ ⋏ ψ ➝ ψ := ValidOnModel.and₂

protected lemma and₃ : F ⊧ φ ➝ ψ ➝ φ ⋏ ψ := ValidOnModel.and₃

protected lemma or₁ : F ⊧ φ ➝ φ ⋎ ψ := ValidOnModel.or₁

protected lemma or₂ : F ⊧ ψ ➝ φ ⋎ ψ := ValidOnModel.or₂

protected lemma or₃ : F ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := ValidOnModel.or₃

protected lemma imply₁ : F ⊧ φ ➝ ψ ➝ φ := ValidOnModel.imply₁

protected lemma imply₂ : F ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := ValidOnModel.imply₂

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := ValidOnModel.mdp hpq hp

protected lemma efq : F ⊧ Axioms.EFQ φ := ValidOnModel.efq

protected lemma neg_equiv : F ⊧ Axioms.NegEquiv φ := ValidOnModel.neg_equiv

protected lemma lem (F_symm : Symmetric F.Rel) : F ⊧ Axioms.LEM φ := ValidOnModel.lem F_symm

protected lemma dum (F_conn : Connected F.Rel) : F ⊧ Axioms.GD φ ψ := ValidOnModel.dum F_conn

protected lemma wlem (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM φ := ValidOnModel.wlem F_conf

protected lemma bot : ¬F ⊧ ⊥ := by
  simp [ValidOnFrame.models_iff, ValidOnFrame];
  use (λ _ _ => True);
  simp_all only [imp_self, implies_true];

instance : Semantics.Bot (Frame.Dep α) := ⟨λ _ => ValidOnFrame.bot⟩

end ValidOnFrame


@[simp] def ValidOnFrameClass (C : FrameClass) (φ : Formula α) := ∀ F, F ∈ C → F#α ⊧ φ

namespace ValidOnFrameClass

instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {C : FrameClass.Dep α}

@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

end ValidOnFrameClass

end Formula.Kripke


namespace Hilbert

open Formula.Kripke

variable {H : Hilbert α} {φ : Formula α}

namespace Kripke

abbrev frameclassOf (H : Hilbert α) : FrameClass.Dep α := { F | F#α ⊧* H.theorems }

lemma sound : H ⊢! φ → (frameclassOf H) ⊧ φ := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF φ hp;

instance : Sound H (frameclassOf H) := ⟨sound⟩

lemma unprovable_bot (hNonempty : (frameclassOf H).Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound;
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hNonempty;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;

instance (h_nonempty : (frameclassOf H).Nonempty) : System.Consistent H := System.Consistent.of_unprovable $ unprovable_bot h_nonempty

class Characterize (H : Hilbert α) (C : Kripke.FrameClass) where
  characterize : C ⊆ (frameclassOf H)
  nonempty : C.Nonempty

variable {C : Kripke.FrameClass.Dep.{v, u} α}

lemma sound_of_subset [Characterize H C] : H ⊢! φ → C ⊧ φ := by
  intro h F hF;
  apply sound h;
  exact Characterize.characterize hF;

instance instSoundOfSubset [Characterize H C] : Sound H C := ⟨sound_of_subset⟩

/-
instance instConsistentOf [c : Characterize H C] [Sound H C] : Consistent H := by sorry;
  apply System.Consistent.of_unprovable (f := ⊥);
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := c.nonempty;
  use F;
  exact c.characterize hF;
-/

/-
instance instConsistentNonempty [Sound.{u, u, v + 1, u} H C] (h : C.Nonempty) : Consistent H := by
  sorry
-/

end Kripke


open Kripke

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply ValidOnFrame.verum;
    | apply ValidOnFrame.imply₁;
    | apply ValidOnFrame.imply₂;
    | apply ValidOnFrame.and₁;
    | apply ValidOnFrame.and₂;
    | apply ValidOnFrame.and₃;
    | apply ValidOnFrame.or₁;
    | apply ValidOnFrame.or₂;
    | apply ValidOnFrame.or₃;
    | apply ValidOnFrame.neg_equiv;
    | exact ValidOnFrame.mdp (by assumption) (by assumption);
  )


namespace Int

lemma Kripke.subset_univ : Set.univ ⊆ frameclassOf (Hilbert.Int α) := by
  intro F _;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h => obtain ⟨_, rfl⟩ := h; exact ValidOnFrame.efq;
  | _ => trivial;
instance Kripke.characterize : Characterize (Hilbert.Int α) (Set.univ#α) := ⟨Kripke.subset_univ, by use Kripke.pointframe; tauto⟩
-- instance Kripke.sound : Sound (Hilbert.Int α) (Set.univ#α) := instSoundOfSubset (H := Hilbert.Int α) (C := Set.univ#α)
-- instance consistent : Consistent (Hilbert.Int α) := inferInstance

end Int


namespace Cl

lemma Kripke.subset_symmetric : SymmetricFrameClass ⊆ frameclassOf (Hilbert.Cl α) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.lem; exact hF;
  | _ => trivial;
instance Kripke.sound : Sound (Hilbert.Cl α) (SymmetricFrameClass#α) := instSoundOfSubset Kripke.subset_symmetric

end Cl


namespace KC

lemma Kripke.subset_concluent : ConfluentFrameClass ⊆ (frameclassOf (Hilbert.KC α)) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.wlem; exact hF;
  | _ => trivial;
instance Kripke.sound : Sound (Hilbert.KC α) (ConfluentFrameClass#α) := instSoundOfSubset Kripke.subset_concluent

end KC


namespace LC

lemma Kripke.subset_connected : ConnectedFrameClass ⊆ frameclassOf (Hilbert.LC α) := by
  intro F hF;
  simp at hF;
  simp [Hilbert.theorems, System.theory];
  intro φ hφ;
  induction hφ using Hilbert.Deduction.rec! with
  | eaxm h =>
    rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
    . apply ValidOnFrame.efq;
    . apply ValidOnFrame.dum; exact hF;
  | _ => trivial;
instance Kripke.sound : Sound (Hilbert.LC α) (ConnectedFrameClass#α) := instSoundOfSubset Kripke.subset_connected

end LC

end Hilbert





/-
section Classical

open LO.Kripke

namespace Formula.Kripke

abbrev ClassicalSatisfies (V : ClassicalValuation α) (φ : Formula α) : Prop := Satisfies (ClassicalModel V) () φ

instance : Semantics (Formula α) (ClassicalValuation α) := ⟨ClassicalSatisfies⟩

namespace ClassicalSatisfies

variable {V : ClassicalValuation α}

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp only [Semantics.Realize, Satisfies]

instance : Semantics.Tarski (ClassicalValuation α) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize, Satisfies]; tauto;
  realize_not := by simp [Semantics.Realize, Satisfies]; tauto;

end ClassicalSatisfies

end Formula.Kripke


namespace Kripke

open Formula.Kripke (ClassicalSatisfies)

lemma ValidOnClassicalFrame_iff : (Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.Cl α)) ⊧ φ → ∀ (V : ClassicalValuation α), V ⊧ φ := by
  intro h V;
  refine @h (ClassicalFrame) ?_ (λ _ a => V a) (by simp [Valuation.atomic_hereditary]) ();
  . apply @Cl_Characteraizable α |>.characterize;
    refine ⟨ClassicalFrame.reflexive, ClassicalFrame.transitive, ClassicalFrame.symmetric⟩;

lemma notClassicalValid_of_exists_ClassicalValuation : (∃ (V : ClassicalValuation α), ¬(V ⊧ φ)) → ¬(Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.Cl α)) ⊧ φ := by
  contrapose; push_neg;
  have := @ValidOnClassicalFrame_iff α φ;
  exact this;

lemma unprovable_classical_of_exists_ClassicalValuation (h : ∃ (V : ClassicalValuation α), ¬(V ⊧ φ)) : (Hilbert.Cl α) ⊬ φ := by
  apply not_imp_not.mpr $ Kripke.sound.{u, 0};
  apply notClassicalValid_of_exists_ClassicalValuation;
  assumption;

end Kripke

end Classical
-/

end LO.IntProp
