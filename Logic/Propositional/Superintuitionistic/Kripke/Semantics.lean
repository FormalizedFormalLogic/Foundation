import Logic.Vorspiel.BinaryRelations
import Logic.Logic.Semantics
import Logic.Propositional.Superintuitionistic.Deduction

namespace LO.Kripke

structure Frame where
  World : Type*
  Rel : Rel World World
  [World_nonempty : Nonempty World]

instance : CoeSort Frame Type* := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

instance {F : Frame} : Nonempty F.World := F.World_nonempty

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
scoped infix:45 " ≺ " => Frame.Rel'

noncomputable abbrev Frame.default {F : Frame} : F.World := Classical.choice F.World_nonempty
notation "﹫" => Frame.default


set_option linter.unusedVariables false in
abbrev Frame.Dep (α : Type*) := Frame

abbrev Frame.alt (F : Frame) {α} : Frame.Dep α := F
scoped postfix:max "#" => Frame.alt


structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance {F : FiniteFrame} : Finite (F.World) := F.World_finite
instance : Coe (FiniteFrame) (Frame) := ⟨λ F ↦ F.toFrame⟩


open Relation (ReflTransGen TransGen)


protected abbrev Frame.RelReflTransGen {F : Frame} : _root_.Rel F.World F.World:= ReflTransGen (· ≺ ·)
scoped infix:45 " ≺^* " => Frame.RelReflTransGen

namespace Frame.RelReflTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^* y := ReflTransGen.single hxy

@[simp] lemma reflexive : Reflexive F.RelReflTransGen := Relation.reflexive_reflTransGen

@[simp] lemma refl {x : F.World} : x ≺^* x := reflexive x

@[simp] lemma transitive : Transitive F.RelReflTransGen := Relation.transitive_reflTransGen

@[simp] lemma symmetric : Symmetric F.Rel → Symmetric F.RelReflTransGen := ReflTransGen.symmetric

end Frame.RelReflTransGen


abbrev Frame.TransitiveReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^* ·)
postfix:max "^*" => Frame.TransitiveReflexiveClosure

namespace Frame.TransitiveReflexiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^*.Rel x y := ReflTransGen.single hxy

lemma rel_reflexive : Reflexive F^*.Rel := by intro x; exact ReflTransGen.refl;

lemma rel_transitive : Transitive F^*.Rel := by simp;

lemma rel_symmetric : Symmetric F.Rel → Symmetric F^* := ReflTransGen.symmetric

end Frame.TransitiveReflexiveClosure



protected abbrev Frame.RelTransGen {F : Frame} : _root_.Rel F.World F.World := TransGen (· ≺ ·)
scoped infix:45 " ≺^+ " => Frame.RelTransGen

namespace Frame.RelTransGen

variable {F : Frame}

@[simp] lemma single {x y : F.World} (hxy : x ≺ y) : x ≺^+ y := TransGen.single hxy

@[simp]
lemma transitive : Transitive F.RelTransGen := λ _ _ _ => TransGen.trans

@[simp]
lemma symmetric (hSymm : Symmetric F.Rel) : Symmetric F.RelTransGen := by
  intro x y rxy;
  induction rxy with
  | single h => exact TransGen.single $ hSymm h;
  | tail _ hyz ih => exact TransGen.trans (TransGen.single $ hSymm hyz) ih

end Frame.RelTransGen


abbrev Frame.TransitiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^+ ·)
scoped postfix:max "^+" => Frame.TransitiveClosure

namespace Frame.TransitiveClosure

variable {F : Frame}

lemma single {x y : F.World} (hxy : x ≺ y) : F^+ x y := TransGen.single hxy

lemma rel_transitive : Transitive F^+ := by simp;

lemma rel_symmetric (hSymm : Symmetric F.Rel) : Symmetric F.TransitiveClosure := by simp_all

end Frame.TransitiveClosure


abbrev FrameProperty := Frame → Prop


abbrev FrameClass := Set (Frame)

set_option linter.unusedVariables false in
abbrev FrameClass.Dep (α : Type*) := FrameClass

abbrev FrameClass.alt (𝔽 : FrameClass) {α} : FrameClass.Dep α := 𝔽
scoped postfix:max "#" => FrameClass.alt


abbrev FiniteFrameClass := Set (FiniteFrame)

@[simp] def FiniteFrameClass.toFrameClass (𝔽 : FiniteFrameClass) : FrameClass := { F | ∃ F', F' ∈ 𝔽 ∧ F'.toFrame = F }
instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩

@[simp] def FrameClass.toFiniteFrameClass (𝔽 : FrameClass) : FiniteFrameClass := { F | F.toFrame ∈ 𝔽 }
instance : Coe (FrameClass) (FiniteFrameClass) := ⟨FrameClass.toFiniteFrameClass⟩

@[simp] abbrev FrameClass.restrictFinite (𝔽 : FrameClass) : FrameClass := FiniteFrameClass.toFrameClass ↑𝔽
postfix:max "ꟳ" => FrameClass.restrictFinite

lemma FrameClass.iff_mem_restrictFinite {𝔽 : FrameClass} (h : F ∈ 𝔽) (F_finite : Finite F.World) : F ∈ 𝔽ꟳ := by
  simp;
  use { toFrame := F, World_finite := F_finite };


abbrev FrameClassOfSystem [System F S] [Semantics F (Frame.Dep α)] (𝓢 : S) : FrameClass.Dep α := { (F : Frame.Dep α) | F ⊧* System.theory 𝓢 }
notation "𝔽(" 𝓢 ")" => FrameClassOfSystem 𝓢

abbrev FrameClassOfFrameProperty (P : FrameProperty) : FrameClass := { F | P F }
notation "𝔽(" P ")" => FrameClassOfFrameProperty P


class Characteraizable (𝔽 : FrameClass) (P : FrameProperty) where
  characterize : ∀ {F}, P F → F ∈ 𝔽
  nonempty : ∃ F, P F


section Soundness

variable [System F S] [Semantics F (Frame.Dep α)] {𝓢 : S}

lemma sound : 𝓢 ⊢! p → (FrameClassOfSystem (α := α) 𝓢) ⊧ p := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF p hp;

instance : Sound 𝓢 (FrameClassOfSystem (α := α) 𝓢) := ⟨sound⟩


lemma sound_of_characterizability (characterizability : Characteraizable (FrameClassOfSystem (α := α) 𝓢) P) : 𝓢 ⊢! p → 𝔽(P) ⊧ p := by
  intro h F hF;
  apply sound h;
  apply characterizability.characterize hF;

instance instSoundOfCharacterizability (characterizability : Characteraizable (FrameClassOfSystem (α := α) 𝓢) P)
  : Sound 𝓢 (FrameClassOfFrameProperty P) := ⟨sound_of_characterizability characterizability⟩


variable [LogicalConnective F] [Semantics.Bot (FrameClass.Dep α)]

lemma unprovable_bot : 𝓢 ⊬! ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  exact Semantics.Bot.realize_bot 𝔽(𝓢);

lemma unprovable_bot_of_characterizability [characterizability : Characteraizable (FrameClassOfSystem (α := α) 𝓢) P] : 𝓢 ⊬! ⊥ := by
  apply not_imp_not.mpr $ sound_of_characterizability (characterizability := characterizability);
  exact Semantics.Bot.realize_bot 𝔽(P);

-- instance : System.Consistent 𝓢 := System.Consistent.of_unprovable $ unprovable_bot (α := α)

end Soundness


abbrev Valuation (F : Frame) (α : Type*) := F.World → α → Prop

abbrev Valuation.atomic_hereditary (V : Valuation F α) : Prop := ∀ {w₁ w₂ : F.World}, (w₁ ≺ w₂) → ∀ {a}, (V w₁ a) → (V w₂ a)


structure Model (α) where
  Frame : Frame
  Valuation : Valuation Frame α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type u) := ⟨Model.World⟩

end LO.Kripke


namespace LO.Propositional.Superintuitionistic

/-
namespace Kripke

attribute [simp] Reflexive Transitive Antisymmetric in
structure Frame where
  World : Type u
  [World_nonempty : Inhabited World]
  Rel : World → World → Prop
  Rel_refl : Reflexive Rel := by aesop
  Rel_trans : Transitive Rel := by aesop
  Rel_antisymm : Antisymmetric Rel := by aesop

instance {F : Frame} : Inhabited F.World := F.World_nonempty

structure FiniteFrame extends Frame where
  [World_finite : Finite World]

instance {F : FiniteFrame} : Finite F.World := F.World_finite

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
-/

open System
open Kripke

variable [Inhabited α]

def Formula.Kripke.Satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a => M.Valuation w a
  | ⊤      => True
  | ⊥      => False
  | p ⋏ q  => Satisfies M w p ∧ Satisfies M w q
  | p ⋎ q  => Satisfies M w p ∨ Satisfies M w q
  | ~p     => ∀ {w' : M.World}, (w ≺ w') → ¬Satisfies M w' p
  | p ⟶ q => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' p → Satisfies M w' q)

instance instKripkeSemanticsFormulaWorld (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

open Formula.Kripke

namespace Formula.Kripke.Satisfies

variable {M : Model α} {w : M.World} {p q r : Formula α}

@[simp] protected lemma iff_models : w ⊧ p ↔ Formula.Kripke.Satisfies M w p := iff_of_eq rfl

@[simp] lemma atom_def : w ⊧ atom a ↔ M.Valuation w a := by simp [Satisfies];
@[simp] lemma top_def  : w ⊧ ⊤ ↔ True := by simp [Satisfies];
@[simp] lemma bot_def  : w ⊧ ⊥ ↔ False := by simp [Satisfies];
@[simp] lemma and_def  : w ⊧ p ⋏ q ↔ w ⊧ p ∧ w ⊧ q := by simp [Satisfies];
@[simp] lemma or_def   : w ⊧ p ⋎ q ↔ w ⊧ p ∨ w ⊧ q := by simp [Satisfies];
@[simp] lemma imp_def  : w ⊧ p ⟶ q ↔ ∀ {w' : M.World}, (w ≺ w') → (w' ⊧ p → w' ⊧ q) := by simp [Satisfies, imp_iff_not_or];
@[simp] lemma neg_def  : w ⊧ ~p ↔ ∀ {w' : M.World}, (w ≺ w') → ¬(w' ⊧ p) := by simp [Satisfies];

instance : Semantics.Top M.World where
  realize_top := by simp [Satisfies];

instance : Semantics.Bot M.World where
  realize_bot := by simp [Satisfies];

instance : Semantics.And M.World where
  realize_and := by simp [Satisfies];

instance : Semantics.Or M.World where
  realize_or := by simp [Satisfies];



lemma formula_hereditary
  (herditary : M.Valuation.atomic_hereditary)
  (F_trans : Transitive M.Frame.Rel)
  (hw : w ≺ w') : w ⊧ p → w' ⊧ p := by
  induction p using Formula.rec' with
  | hatom => apply herditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq $ F_trans hw hv;
  | hneg =>
    intro hp v hv;
    exact hp $ F_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

/-
lemma hereditary_int {M : Model (𝐈𝐧𝐭 W α)} {w w' : W} {p : Formula α} (hw : M.frame w w') : (M, w) ⊧ p → (M, w') ⊧ p := by
  apply hereditary (by simp [FrameClass.Intuitionistic]; tauto) hw;
-/

lemma neg_equiv : w ⊧ ~p ↔ w ⊧ p ⟶ ⊥ := by simp_all [Satisfies];

end Formula.Kripke.Satisfies


open Formula.Kripke.Satisfies (formula_hereditary)


def Formula.Kripke.ValidOnModel (M : Model α) (p : Formula α) := ∀ w : M.World, w ⊧ p

namespace Formula.Kripke.ValidOnModel

variable
  {M : Model α} {p q r : Formula α}
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel := by simpa)
  (F_refl : Reflexive M.Frame.Rel := by simpa)

instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models : M ⊧ p ↔ Formula.Kripke.ValidOnModel M p := iff_of_eq rfl

@[simp] protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

@[simp] protected lemma and₁ : M ⊧ p ⋏ q ⟶ p := by simp_all [ValidOnModel, Satisfies];

@[simp] protected lemma and₂ : M ⊧ p ⋏ q ⟶ q := by simp_all [ValidOnModel, Satisfies];

@[simp] protected lemma and₃ : M ⊧ p ⟶ q ⟶ p ⋏ q := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z p := formula_hereditary atom_hereditary F_trans Ryz hp;
  exact ⟨hp, hq⟩;

@[simp] protected lemma or₁ : M ⊧ p ⟶ p ⋎ q := by simp_all [ValidOnModel, Satisfies];

@[simp] protected lemma or₂ : M ⊧ q ⟶ p ⋎ q := by simp_all [ValidOnModel, Satisfies];

@[simp] protected lemma or₃ : M ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (F_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

@[simp] protected lemma imply₁ : M ⊧ p ⟶ q ⟶ p := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary atom_hereditary F_trans Ryz hp;

@[simp] protected lemma imply₂ : M ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw := F_trans Ryz Rzw;
  have Rww := F_refl w;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

@[simp] protected lemma mdp (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  intro w;
  exact hpq w (F_refl w) $ hp w;

@[simp] protected lemma efq : M ⊧ Axioms.EFQ p := by simp [ValidOnModel, Satisfies];

@[simp] protected lemma neg_equiv : M ⊧ Axioms.NegEquiv p := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

@[simp] protected lemma lem (hExt : Extensive M.Frame.Rel) : M ⊧ Axioms.LEM p := by
  simp_all [ValidOnModel];
  intro w;
  by_cases h : w ⊧ p
  . left; assumption;
  . right;
    intro w' hww';
    rw [←(hExt hww')];
    assumption;

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame) (p : Formula α) :=
  ∀ {V : Valuation F α}, (_ : V.atomic_hereditary) → (⟨F, V⟩ : Kripke.Model α) ⊧ p

namespace Formula.Kripke.ValidOnFrame

instance : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl

variable {F : Frame.Dep α} {p q r : Formula α}
         (F_trans : Transitive F)
         (F_refl : Reflexive F)

@[simp] protected lemma verum : F ⊧ ⊤ := fun _ => ValidOnModel.verum

@[simp] protected lemma and₁ : F ⊧ p ⋏ q ⟶ p := fun _ => ValidOnModel.and₁

@[simp] protected lemma and₂ : F ⊧ p ⋏ q ⟶ q := fun _ => ValidOnModel.and₂

@[simp] protected lemma and₃ : F ⊧ p ⟶ q ⟶ p ⋏ q := fun hV => ValidOnModel.and₃ hV F_trans

@[simp] protected lemma or₁ : F ⊧ p ⟶ p ⋎ q := fun _ => ValidOnModel.or₁

@[simp] protected lemma or₂ : F ⊧ q ⟶ p ⋎ q := fun _ => ValidOnModel.or₂

@[simp] protected lemma or₃ : F ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := fun _ => ValidOnModel.or₃ F_trans

@[simp] protected lemma imply₁ : F ⊧ p ⟶ q ⟶ p := fun hV => ValidOnModel.imply₁ hV F_trans

@[simp] protected lemma imply₂ : F ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := fun _ => ValidOnModel.imply₂ F_trans F_refl

@[simp] protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := fun hV => ValidOnModel.mdp F_refl (hpq hV) (hp hV)

@[simp] protected lemma efq : F ⊧ Axioms.EFQ p := fun _ => ValidOnModel.efq

@[simp] protected lemma neg_equiv : F ⊧ Axioms.NegEquiv p := fun _ => ValidOnModel.neg_equiv

@[simp] protected lemma lem (hExt : Extensive F.Rel) : F ⊧ Axioms.LEM p := fun _ => ValidOnModel.lem hExt

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by
    simp [ValidOnModel, ValidOnFrame];
    existsi (λ _ _ => True);
    simp_all [Satisfies, Valuation.atomic_hereditary];

end Formula.Kripke.ValidOnFrame


@[simp] def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F# ⊧ p

namespace Formula.Kripke.ValidOnFrameClass

instance : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

@[simp] protected lemma iff_models {𝔽 : FrameClass.Dep α} : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl

protected lemma realize_bot {𝔽 : FrameClass.Dep α} (ne : 𝔽.Nonempty) : ¬(𝔽 ⊧ ⊥) := by
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass];
  exact ne;

end Formula.Kripke.ValidOnFrameClass

/-
@[simp] def Formula.Kripke.ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass) (f : Formula α) := ∀ (F : FiniteFrame' α), F ∈ 𝔽 → F.toFrame' ⊧ f

instance : Semantics (Formula α) (FiniteFrameClass' α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFiniteFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFiniteFrameClass

@[simp] protected lemma models_iff {𝔽 : FiniteFrameClass' α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFiniteFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFiniteFrameClass
-/


namespace Kripke

instance Characteraizable_Int : Kripke.Characteraizable 𝔽((𝐈𝐧𝐭 : DeductionParameter α)) (λ F => Transitive F ∧ Reflexive F) where
  characterize := by
    simp [System.theory];
    intro F hTrans hRefl p hp;
    induction hp using Deduction.rec! with
    | verum => apply ValidOnFrame.verum;
    | imply₁ => apply ValidOnFrame.imply₁; simpa;
    | imply₂ => apply ValidOnFrame.imply₂; simpa; simpa;
    | and₁ => apply ValidOnFrame.and₁;
    | and₂ => apply ValidOnFrame.and₂;
    | and₃ => apply ValidOnFrame.and₃; simpa;
    | or₁ => apply ValidOnFrame.or₁;
    | or₂ => apply ValidOnFrame.or₂;
    | or₃ => apply ValidOnFrame.or₃; simpa;
    | neg_equiv => apply ValidOnFrame.neg_equiv;
    | mdp ihpq ihp =>
      apply ValidOnFrame.mdp;
      repeat simpa;
    | eaxm h =>
      obtain ⟨_, rfl⟩ := h;
      apply ValidOnFrame.efq;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    simp [Transitive, Reflexive];

abbrev _root_.LO.Kripke.TransitiveReflexiveFrameClass : FrameClass := 𝔽((λ F => Transitive F ∧ Reflexive F))


instance : Sound (𝐈𝐧𝐭 : DeductionParameter α) TransitiveReflexiveFrameClass# :=
  LO.Kripke.instSoundOfCharacterizability (characterizability := Kripke.Characteraizable_Int)

instance Characteraizable_Cl : Kripke.Characteraizable 𝔽((𝐂𝐥 : DeductionParameter α)) (λ F => Transitive F ∧ Reflexive F ∧ Extensive F) where
  characterize := by
    simp [System.theory];
    intro F hTrans hRefl hExt p hp;
    induction hp using Deduction.rec! with
    | verum => apply ValidOnFrame.verum;
    | imply₁ => apply ValidOnFrame.imply₁; simpa;
    | imply₂ => apply ValidOnFrame.imply₂; simpa; simpa;
    | and₁ => apply ValidOnFrame.and₁;
    | and₂ => apply ValidOnFrame.and₂;
    | and₃ => apply ValidOnFrame.and₃; simpa;
    | or₁ => apply ValidOnFrame.or₁;
    | or₂ => apply ValidOnFrame.or₂;
    | or₃ => apply ValidOnFrame.or₃; simpa;
    | neg_equiv => apply ValidOnFrame.neg_equiv;
    | mdp ihpq ihp =>
      apply ValidOnFrame.mdp;
      repeat simpa;
    | eaxm h =>
      rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩);
      . apply ValidOnFrame.efq;
      . apply ValidOnFrame.lem; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    simp [Transitive, Reflexive, Extensive];

abbrev _root_.LO.Kripke.TransitiveReflexiveExtensiveFrameClass : FrameClass := 𝔽((λ F => Transitive F ∧ Reflexive F ∧ Extensive F))

instance : Sound (𝐂𝐥 : DeductionParameter α) TransitiveReflexiveExtensiveFrameClass# :=
  LO.Kripke.instSoundOfCharacterizability (characterizability := Kripke.Characteraizable_Cl)

end Kripke

end LO.Propositional.Superintuitionistic
