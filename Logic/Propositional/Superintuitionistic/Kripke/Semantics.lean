import Logic.Logic.Kripke.Basic
import Logic.Propositional.Superintuitionistic.Deduction

namespace LO.Propositional.Superintuitionistic

open System
open Kripke

variable [Inhabited α]

namespace Formula.Kripke

def Satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a => M.Valuation w a
  | ⊤      => True
  | ⊥      => False
  | p ⋏ q  => Satisfies M w p ∧ Satisfies M w q
  | p ⋎ q  => Satisfies M w p ∨ Satisfies M w q
  | ~p     => ∀ {w' : M.World}, (w ≺ w') → ¬Satisfies M w' p
  | p ⟶ q => ∀ {w' : M.World}, (w ≺ w') → (Satisfies M w' p → Satisfies M w' q)
instance (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

namespace Satisfies

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


lemma neg_equiv : w ⊧ ~p ↔ w ⊧ p ⟶ ⊥ := by simp_all [Satisfies];

end Satisfies


open Satisfies


def ValidOnModel (M : Model α) (p : Formula α) := ∀ w : M.World, w ⊧ p
instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace ValidOnModel

variable
  {M : Model α} {p q r : Formula α}
  (atom_hereditary : ∀ {w₁ w₂ : M.World}, (w₁ ≺ w₂) → ∀ {a}, (M.Valuation w₁ a) → (M.Valuation w₂ a))
  (F_trans : Transitive M.Frame.Rel := by simpa)
  (F_refl : Reflexive M.Frame.Rel := by simpa)

@[simp] protected lemma iff_models : M ⊧ p ↔ Formula.Kripke.ValidOnModel M p := iff_of_eq rfl

protected lemma verum : M ⊧ ⊤ := by simp_all [ValidOnModel];

protected lemma and₁ : M ⊧ p ⋏ q ⟶ p := by simp_all [ValidOnModel, Satisfies];

protected lemma and₂ : M ⊧ p ⋏ q ⟶ q := by simp_all [ValidOnModel, Satisfies];

protected lemma and₃ : M ⊧ p ⟶ q ⟶ p ⋏ q := by
  intro x y _ hp z Ryz hq;
  replace hp : Satisfies M z p := formula_hereditary atom_hereditary F_trans Ryz hp;
  exact ⟨hp, hq⟩;

protected lemma or₁ : M ⊧ p ⟶ p ⋎ q := by simp_all [ValidOnModel, Satisfies];

protected lemma or₂ : M ⊧ q ⟶ p ⋎ q := by simp_all [ValidOnModel, Satisfies];

protected lemma or₃ : M ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models, Satisfies.imp_def, Satisfies.or_def];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (F_trans hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

protected lemma imply₁ : M ⊧ p ⟶ q ⟶ p := by
  intro x y _ hp z Ryz _;
  exact formula_hereditary atom_hereditary F_trans Ryz hp;

protected lemma imply₂ : M ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by
  intro x y _ hpqr z Ryz hpq w Rzw hp;
  have Ryw := F_trans Ryz Rzw;
  have Rww := F_refl w;
  exact hpqr Ryw hp Rww (hpq Rzw hp);

protected lemma mdp (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  intro w;
  exact hpq w (F_refl w) $ hp w;

protected lemma efq : M ⊧ Axioms.EFQ p := by simp [ValidOnModel, Satisfies];

protected lemma neg_equiv : M ⊧ Axioms.NegEquiv p := by
  simp_all [ValidOnModel, Axioms.NegEquiv];
  intro w;
  constructor;
  . intro x _ h y rxy hyp; exact h rxy hyp;
  . intro x _ h y rxy; exact h rxy;

protected lemma lem (F_ext : Extensive M.Frame.Rel) : M ⊧ Axioms.LEM p := by
  simp_all [ValidOnModel];
  intro w;
  by_cases h : w ⊧ p
  . left; assumption;
  . right;
    intro w' hww';
    rw [←(F_ext hww')];
    assumption;

protected lemma dum : Connected M.Frame.Rel → M ⊧ Axioms.GD p q := by
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

protected lemma wlem : Confluent M.Frame.Rel → M ⊧ Axioms.WeakLEM p := by
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


def ValidOnFrame (F : Frame) (p : Formula α) := ∀ {V : Valuation F α}, (_ : V.atomic_hereditary) → (⟨F, V⟩ : Kripke.Model α) ⊧ p

instance : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

namespace ValidOnFrame

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl

variable {F : Frame.Dep α} {p q r : Formula α}
         (F_trans : Transitive F)
         (F_refl : Reflexive F)

protected lemma verum : F ⊧ ⊤ := fun _ => ValidOnModel.verum

protected lemma and₁ : F ⊧ p ⋏ q ⟶ p := fun _ => ValidOnModel.and₁

protected lemma and₂ : F ⊧ p ⋏ q ⟶ q := fun _ => ValidOnModel.and₂

protected lemma and₃ : F ⊧ p ⟶ q ⟶ p ⋏ q := fun hV => ValidOnModel.and₃ hV F_trans

protected lemma or₁ : F ⊧ p ⟶ p ⋎ q := fun _ => ValidOnModel.or₁

protected lemma or₂ : F ⊧ q ⟶ p ⋎ q := fun _ => ValidOnModel.or₂

protected lemma or₃ : F ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := fun _ => ValidOnModel.or₃ F_trans

protected lemma imply₁ : F ⊧ p ⟶ q ⟶ p := fun hV => ValidOnModel.imply₁ hV F_trans

protected lemma imply₂ : F ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := fun _ => ValidOnModel.imply₂ F_trans F_refl

protected lemma mdp (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := fun hV => ValidOnModel.mdp F_refl (hpq hV) (hp hV)

protected lemma efq : F ⊧ Axioms.EFQ p := fun _ => ValidOnModel.efq

protected lemma neg_equiv : F ⊧ Axioms.NegEquiv p := fun _ => ValidOnModel.neg_equiv

protected lemma lem (hExt : Extensive F.Rel) : F ⊧ Axioms.LEM p := fun _ => ValidOnModel.lem hExt

protected lemma dum (F_conn : Connected F.Rel) : F ⊧ Axioms.GD p q := fun hV => ValidOnModel.dum hV F_trans F_conn

protected lemma wlem (F_conf : Confluent F.Rel) : F ⊧ Axioms.WeakLEM p := fun hV => ValidOnModel.wlem hV F_trans F_conf

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by
    simp [ValidOnModel, ValidOnFrame];
    existsi (λ _ _ => True);
    simp_all [Satisfies, Valuation.atomic_hereditary];

end ValidOnFrame


instance : Semantics (Formula α) (FrameClass.Dep α) := LO.Semantics.instSet (Frame.Dep α)


end Formula.Kripke

open Formula.Kripke
open Formula.Kripke.Satisfies (formula_hereditary)

namespace Kripke


abbrev FrameClassOfSystem (α : Type u) {S : Type u} [System (Formula α) S] (𝓢 : S) : FrameClass.Dep α := { (F : Frame.Dep α) | F ⊧* System.theory 𝓢 }
notation "𝔽(" 𝓢 " of " α ")" => FrameClassOfSystem α 𝓢

section Soundness

variable {α : Type u} [System (Formula α) S] {𝓢 : S} {p : Formula α} {P : FrameProperty}

lemma sound : 𝓢 ⊢! p → 𝔽(𝓢 of α) ⊧ p := by
  intro hp F hF;
  simp [System.theory] at hF;
  exact hF p hp;

instance : Sound 𝓢 𝔽(𝓢 of α) := ⟨sound⟩

lemma unprovable_bot (hc : 𝔽(𝓢 of α).Nonempty) : 𝓢 ⊬! ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;

instance (hc : 𝔽(𝓢 of α).Nonempty) : System.Consistent 𝓢 := System.Consistent.of_unprovable $ unprovable_bot hc


lemma sound_of_characterizability [characterizability : 𝔽(𝓢 of α).Characteraizable P] : 𝓢 ⊢! p → 𝔽(P)#α ⊧ p := by
  intro h F hF;
  apply sound h;
  apply characterizability.characterize hF;

instance instSoundOfCharacterizability [𝔽(𝓢 of α).Characteraizable P] : Sound 𝓢 (𝔽(P)#α) := ⟨sound_of_characterizability⟩

lemma unprovable_bot_of_characterizability [characterizability : 𝔽(𝓢 of α).Characteraizable P] : 𝓢 ⊬! ⊥ := by
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := characterizability.nonempty;
  use F;
  apply characterizability.characterize hF;

instance instConsistentOfCharacterizability [FrameClass.Characteraizable.{u} 𝔽(𝓢 of α) P] : System.Consistent 𝓢 := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability

end Soundness


variable {α : Type u}

instance Int_Characteraizable : 𝔽(𝐈𝐧𝐭 of α).Characteraizable (λ F => Reflexive F ∧ Transitive F) where
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
      repeat simpa only [ValidOnFrame.models_iff];
    | eaxm h =>
      obtain ⟨_, rfl⟩ := h;
      apply ValidOnFrame.efq;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    simp [Transitive, Reflexive];

instance : Sound 𝐈𝐧𝐭 (ReflexiveTransitiveFrameClass#α) := inferInstance

instance : System.Consistent (𝐈𝐧𝐭 : DeductionParameter α) := inferInstance


instance Cl_Characteraizable : 𝔽(𝐂𝐥 of α).Characteraizable (λ F => Reflexive F ∧ Transitive F ∧ Extensive F) where
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

instance : Sound 𝐂𝐥 (ReflexiveTransitiveExtensiveFrameClass#α) := inferInstance

instance : System.Consistent (𝐂𝐥 : DeductionParameter α) := inferInstance



instance KC_Characteraizable : 𝔽(𝐊𝐂 of α).Characteraizable (λ F => Reflexive F ∧ Transitive F ∧ Confluent F) where
  characterize := by
    rintro F ⟨F_trans, F_refl, F_confl⟩;
    simp [System.theory];
    intro p hp;
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
      rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
      . apply ValidOnFrame.efq;
      . apply ValidOnFrame.wlem; simpa; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    simp [Transitive, Reflexive, Confluent];

instance : Sound 𝐊𝐂 (ReflexiveTransitiveConfluentFrameClass#α) := inferInstance

instance : System.Consistent (𝐊𝐂 : DeductionParameter α) := inferInstance


instance LC_Characteraizable : 𝔽(𝐋𝐂 of α).Characteraizable (λ F => Reflexive F ∧ Transitive F ∧ Connected F) where
  characterize := by
    rintro F ⟨F_trans, F_refl, F_conn⟩;
    simp [System.theory];
    intro p hp;
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
      rcases h with (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
      . apply ValidOnFrame.efq;
      . apply ValidOnFrame.dum; simpa; simpa;
  nonempty := by
    use { World := PUnit, Rel := λ _ _ => True };
    simp [Transitive, Reflexive, Connected];

instance : Sound 𝐋𝐂 (ReflexiveTransitiveConnectedFrameClass#α) := inferInstance

instance : System.Consistent (𝐋𝐂 : DeductionParameter α) := inferInstance

end Kripke

end LO.Propositional.Superintuitionistic
