import Foundation.Logic.Kripke.Basic
import Foundation.IntProp.Deduction

namespace LO.IntProp

open System
open Kripke

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

variable {M : Model α} {w : M.World} {φ ψ χ : Formula α}

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
  (herditary : M.Valuation.atomic_hereditary)
  (F_trans : Transitive M.Frame.Rel)
  (hw : w ≺ w') : w ⊧ φ → w' ⊧ φ := by
  induction φ using Formula.rec' with
  | hatom => apply herditary hw;
  | himp =>
    intro hpq v hv;
    exact hpq $ F_trans hw hv;
  | hneg =>
    intro hp v hv;
    exact hp $ F_trans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];


lemma neg_equiv : w ⊧ ∼φ ↔ w ⊧ φ ➝ ⊥ := by simp_all [Satisfies];

end Satisfies


open Satisfies


def ValidOnModel (M : Model α) (φ : Formula α) := ∀ w : M.World, w ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

variable {M : Model α} {φ ψ χ : Formula α}

@[simp] protected lemma iff_models : M ⊧ φ ↔ Formula.Kripke.ValidOnModel M φ := iff_of_eq rfl

protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

protected lemma and₁ : M ⊧ φ ⋏ ψ ➝ φ := by simp_all [ValidOnModel, Satisfies];

protected lemma and₂ : M ⊧ φ ⋏ ψ ➝ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma and₃
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel)
  : M ⊧ φ ➝ ψ ➝ φ ⋏ ψ := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z φ := formula_hereditary atom_hereditary F_trans Ryz hp;
  exact ⟨hp, hq⟩;

protected lemma or₁ : M ⊧ φ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma or₂ : M ⊧ ψ ➝ φ ⋎ ψ := by simp_all [ValidOnModel, Satisfies];

protected lemma or₃
  (F_trans : Transitive M.Frame.Rel)
  : M ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (F_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma imply₁
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel)
  : M ⊧ φ ➝ ψ ➝ φ := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary atom_hereditary F_trans Ryz hp;

protected lemma imply₂
  (F_trans : Transitive M.Frame.Rel)
  (F_refl : Reflexive M.Frame.Rel)
  : M ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw := F_trans Ryz Rzw;
  have Rww := F_refl w;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (F_refl : Reflexive M.Frame.Rel) (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro w;
  exact hpq w (F_refl w) $ hp w;

protected lemma efq : M ⊧ Axioms.EFQ φ := by simp [ValidOnModel, Satisfies];

protected lemma neg_equiv : M ⊧ Axioms.NegEquiv φ := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

protected lemma lem
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel)
  : Symmetric M.Frame.Rel → M ⊧ Axioms.LEM φ := by
  simp_all [ValidOnModel, Satisfies, Symmetric];
  contrapose; push_neg;
  rintro ⟨x, nhxp, ⟨y, Rxy, hyp⟩⟩;
  use x, y;
  constructor;
  . exact Rxy;
  . by_contra Ryx;
    have := formula_hereditary atom_hereditary F_trans Ryx hyp;
    contradiction;

protected lemma dum
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel)
  : Connected M.Frame.Rel → M ⊧ Axioms.GD φ ψ := by
  simp [ValidOnModel, Satisfies, Connected];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp, nhyq⟩, ⟨z, Ryz, hzq, nhyp⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Ryz, ?_, ?_⟩;
  . by_contra Ryz;
    have := formula_hereditary atom_hereditary F_trans Ryz hyp;
    contradiction;
  . by_contra Rzy;
    have := formula_hereditary atom_hereditary F_trans Rzy hzq;
    contradiction;

protected lemma wlem
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel)
  : Confluent M.Frame.Rel → M ⊧ Axioms.WeakLEM φ := by
  simp [ValidOnModel, Satisfies, Confluent];
  contrapose; push_neg;
  rintro ⟨x, ⟨y, Rxy, hyp⟩, ⟨z, Rxz, hz⟩⟩;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  rintro w Ryw;
  by_contra Rzw;
  have := formula_hereditary atom_hereditary F_trans Ryw hyp;
  have := hz w Rzw;
  contradiction;

end ValidOnModel


def ValidOnFrame (F : Frame) (φ : Formula α) := ∀ {V : Valuation F α}, (_ : V.atomic_hereditary) → (⟨F, V⟩ : Kripke.Model α) ⊧ φ


namespace ValidOnFrame

instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl

variable {F : Frame.Dep α} {φ ψ χ : Formula α}

protected lemma verum : F ⊧ ⊤ := fun _ => ValidOnModel.verum

protected lemma and₁ : F ⊧ φ ⋏ ψ ➝ φ := fun _ => ValidOnModel.and₁

protected lemma and₂ : F ⊧ φ ⋏ ψ ➝ ψ := fun _ => ValidOnModel.and₂

protected lemma and₃ (F_trans : Transitive F) : F ⊧ φ ➝ ψ ➝ φ ⋏ ψ := fun hV => ValidOnModel.and₃ hV F_trans

protected lemma or₁ : F ⊧ φ ➝ φ ⋎ ψ := fun _ => ValidOnModel.or₁

protected lemma or₂ : F ⊧ ψ ➝ φ ⋎ ψ := fun _ => ValidOnModel.or₂

protected lemma or₃ (F_trans : Transitive F) : F ⊧ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := fun _ => ValidOnModel.or₃ F_trans

protected lemma imply₁ (F_trans : Transitive F) : F ⊧ φ ➝ ψ ➝ φ := fun hV => ValidOnModel.imply₁ hV F_trans

protected lemma imply₂ (F_trans : Transitive F) (F_refl : Reflexive F) : F ⊧ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ := fun _ => ValidOnModel.imply₂ F_trans F_refl

protected lemma mdp (F_refl : Reflexive F) (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := fun hV => ValidOnModel.mdp F_refl (hpq hV) (hp hV)

protected lemma efq : F ⊧ Axioms.EFQ φ := fun _ => ValidOnModel.efq

protected lemma neg_equiv : F ⊧ Axioms.NegEquiv φ := fun _ => ValidOnModel.neg_equiv

protected lemma lem (F_trans : Transitive F)  (F_symm : Symmetric F.Rel) : F ⊧ Axioms.LEM φ := fun hV => ValidOnModel.lem hV F_trans F_symm

protected lemma dum (F_trans : Transitive F) (F_conn : Connected F.Rel) : F ⊧ Axioms.GD φ ψ := fun hV => ValidOnModel.dum hV F_trans F_conn

protected lemma wlem (F_trans : Transitive F) (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM φ := fun hV => ValidOnModel.wlem hV F_trans F_conf

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by
    simp [ValidOnModel, ValidOnFrame];
    existsi (λ _ _ => True);
    simp_all [Satisfies, Valuation.atomic_hereditary];

end ValidOnFrame


@[simp] def ValidOnFrameClass (𝔽 : FrameClass) (φ : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F#α ⊧ φ

namespace ValidOnFrameClass

instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass 𝔽 φ := iff_of_eq rfl

end ValidOnFrameClass

end Formula.Kripke


open Formula.Kripke
open Formula.Kripke.Satisfies (formula_hereditary)

namespace Kripke

abbrev FrameClassOfTheory (T : Theory α) : FrameClass.Dep α := { F | F#α ⊧* T }
notation "𝔽(" T ")" => FrameClassOfTheory T

abbrev FrameClassOfHilbert (Λ : Hilbert α) : FrameClass.Dep α := 𝔽((System.theory Λ))
notation "𝔽(" Λ ")" => FrameClassOfHilbert Λ

section Soundness

variable {Λ : Hilbert α}
         {φ : Formula α}

lemma sound : Λ ⊢! φ → 𝔽(Λ) ⊧ φ := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF φ hp;

instance : Sound Λ 𝔽(Λ) := ⟨sound⟩

lemma unprovable_bot (hc : 𝔽(Λ).Nonempty) : Λ ⊬ ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;

instance (hc : 𝔽(Λ).Nonempty) : System.Consistent Λ := System.Consistent.of_unprovable $ unprovable_bot hc


lemma sound_of_characterizability [characterizability : 𝔽(Λ).Characteraizable 𝔽₂] : Λ ⊢! φ → 𝔽₂#α ⊧ φ := by
  intro h F hF;
  apply sound h;
  apply characterizability.characterize hF;

instance instSoundOfCharacterizability [𝔽(Λ).Characteraizable 𝔽₂] : Sound Λ (𝔽₂#α) := ⟨sound_of_characterizability⟩

lemma unprovable_bot_of_characterizability [characterizability : 𝔽(Λ).Characteraizable 𝔽₂] : Λ ⊬ ⊥ := by
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := characterizability.nonempty;
  use F;
  apply characterizability.characterize hF;

instance instConsistentOfCharacterizability [FrameClass.Characteraizable.{u} 𝔽(Λ) 𝔽₂] : System.Consistent Λ := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability

end Soundness


section

variable {α : Type u}

instance Int_Characteraizable : 𝔽((Hilbert.Int α)).Characteraizable ReflexiveTransitiveFrameClass where
  characterize := by
    simp [System.theory];
    rintro F hTrans hRefl φ hp;
    induction hp using Hilbert.Deduction.rec! with
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
      repeat simpa only [ValidOnFrame.models_iff];
    | eaxm h =>
      obtain ⟨_, rfl⟩ := h;
      apply ValidOnFrame.efq;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    refine ⟨by simp [Reflexive], by simp [Transitive]⟩;


instance Int_sound : Sound (Hilbert.Int α) (ReflexiveTransitiveFrameClass#α) := inferInstance

instance : System.Consistent (Hilbert.Int α) := inferInstance


instance Cl_Characteraizable : 𝔽(Hilbert.Cl α).Characteraizable ReflexiveTransitiveSymmetricFrameClass#α where
  characterize := by
    simp [System.theory];
    rintro F hTrans hRefl hSymm φ hp;
    induction hp using Hilbert.Deduction.rec! with
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
      . apply ValidOnFrame.lem; simpa; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    refine ⟨by simp [Reflexive], by simp [Transitive], by simp [Symmetric]⟩;

instance : Sound (Hilbert.Cl α) (ReflexiveTransitiveSymmetricFrameClass#α) := inferInstance

instance : System.Consistent (Hilbert.Cl α) := inferInstance



instance KC_Characteraizable : 𝔽(Hilbert.KC α).Characteraizable ReflexiveTransitiveConfluentFrameClass where
  characterize := by
    rintro F ⟨F_trans, F_refl, F_confl⟩;
    simp [System.theory];
    intro φ hp;
    induction hp using Hilbert.Deduction.rec! with
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
      rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
      . apply ValidOnFrame.efq;
      . apply ValidOnFrame.wlem; simpa; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    refine ⟨by simp [Reflexive], by simp [Transitive], by simp [Confluent]⟩;

instance : Sound (Hilbert.KC α) (ReflexiveTransitiveConfluentFrameClass#α) := inferInstance

instance : System.Consistent (Hilbert.KC α) := inferInstance


instance LC_Characteraizable : 𝔽((Hilbert.LC α)).Characteraizable ReflexiveTransitiveConnectedFrameClass where
  characterize := by
    rintro F ⟨F_trans, F_refl, F_conn⟩;
    simp [System.theory];
    intro φ hp;
    induction hp using Hilbert.Deduction.rec! with
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
      rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
      . apply ValidOnFrame.efq;
      . apply ValidOnFrame.dum; simpa; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    refine ⟨by simp [Reflexive], by simp [Transitive], by simp [Connected]⟩;

instance : Sound (Hilbert.LC α) (ReflexiveTransitiveConnectedFrameClass#α) := inferInstance

instance : System.Consistent (Hilbert.LC α) := inferInstance

end

end Kripke


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


end LO.IntProp
