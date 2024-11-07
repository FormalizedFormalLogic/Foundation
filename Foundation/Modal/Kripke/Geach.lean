import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Geach
import Foundation.Modal.Kripke.Completeness


namespace LO.Kripke


abbrev GeachConfluentFrameClass (t : GeachTaple) : FrameClass := { F | (GeachConfluent t) F.Rel }

namespace GeachConfluentFrameClass

instance nonempty : (GeachConfluentFrameClass t).Nonempty := by
  use ⟨PUnit, λ _ _ => True⟩;
  simp [GeachConfluentFrameClass];
  intros x _ _ _; use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

end GeachConfluentFrameClass


abbrev MultiGeachConfluentFrameClass (ts : List GeachTaple) : FrameClass := { F | (MultiGeachConfluent ts) F.Rel }

namespace MultiGeachConfluentFrameClass

@[simp]
lemma def_nil : MultiGeachConfluentFrameClass [] = AllFrameClass := by rfl;

@[simp]
lemma def_one (t : GeachTaple) : MultiGeachConfluentFrameClass [t] = GeachConfluentFrameClass t := by rfl;

lemma def_cons {t : GeachTaple} {ts : List GeachTaple} (ts_nil : ts ≠ [])
  : MultiGeachConfluentFrameClass (t :: ts) = GeachConfluentFrameClass t ∩ MultiGeachConfluentFrameClass ts := by
  apply Set.eq_of_subset_of_subset;
  . rintro F hF;
    apply MultiGeachConfluent.iff_cons ts_nil |>.mp;
    exact hF;
  . rintro F ⟨hF₁, hF₂⟩;
    apply MultiGeachConfluent.iff_cons ts_nil |>.mpr;
    constructor;
    . apply hF₁;
    . apply hF₂;

@[simp]
instance nonempty : (MultiGeachConfluentFrameClass ts).Nonempty := by
  use ⟨PUnit,  λ _ _ => True⟩;
  induction ts using List.induction_with_singleton with
  | hnil => simp only [def_nil, Set.mem_univ];
  | hsingle t =>
    simp [GeachConfluentFrameClass];
    intros x _ _ _; use x;
    constructor <;> { apply Rel.iterate.true_any; tauto; }
  | hcons t ts ts_nil ih =>
    simp [MultiGeachConfluentFrameClass.def_cons ts_nil];
    constructor;
    . intro x _ _ _; use x;
      constructor <;> { apply Rel.iterate.true_any; tauto; }
    . exact ih;

end MultiGeachConfluentFrameClass


abbrev FrameClass.IsGeach (𝔽 : FrameClass) (ts : List GeachTaple) := FrameClass.DefinedBy 𝔽 (MultiGeachConfluentFrameClass ts)

lemma FrameClass.IsGeach.equality {𝔽 : FrameClass} [geach : 𝔽.IsGeach ts] : 𝔽 = MultiGeachConfluentFrameClass ts := by
  apply Set.eq_of_subset_of_subset;
  . intro F hF; exact geach.define.mp hF;
  . intro F hF; exact geach.define.mpr hF;


section

open GeachConfluent

instance ReflexiveFrameClass.isGeach : ReflexiveFrameClass.IsGeach [⟨0, 0, 1, 0⟩] where
  define := by intro _; apply reflexive_def;
  nonempty := MultiGeachConfluentFrameClass.nonempty


instance : SerialFrameClass.IsGeach [⟨0, 0, 1, 1⟩] where
  define := by intro _; apply serial_def;
  nonempty := MultiGeachConfluentFrameClass.nonempty


instance TransitiveFrameClass.isGeach : TransitiveFrameClass.IsGeach ([⟨0, 2, 1, 0⟩]) where
  define := by intro _; apply transitive_def;
  nonempty := MultiGeachConfluentFrameClass.nonempty

instance : ReflexiveEuclideanFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]) where
  define := by
    intro F;
    constructor;
    . rintro ⟨F_refl, F_eucl⟩;
      refine ⟨reflexive_def.mp F_refl, euclidean_def.mp F_eucl⟩;
    . rintro ⟨F_refl, F_eucl⟩;
      refine ⟨reflexive_def.mpr F_refl, euclidean_def.mpr F_eucl⟩;
  nonempty := MultiGeachConfluentFrameClass.nonempty

instance : ReflexiveSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩]) where
  define := by
    intro F;
    constructor;
    . rintro ⟨F_refl, F_symm⟩;
      refine ⟨reflexive_def.mp F_refl, symmetric_def.mp F_symm⟩;
    . rintro ⟨F_refl, F_symm⟩;
      refine ⟨reflexive_def.mpr F_refl, symmetric_def.mpr F_symm⟩;
  nonempty := MultiGeachConfluentFrameClass.nonempty

instance : PreorderFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩,]) where
  define := by
    intro F;
    constructor;
    . rintro ⟨F_refl, F_trans⟩;
      refine ⟨reflexive_def.mp F_refl, transitive_def.mp F_trans⟩;
    . rintro ⟨F_refl, F_trans⟩;
      refine ⟨reflexive_def.mpr F_refl, transitive_def.mpr F_trans⟩;
  nonempty := MultiGeachConfluentFrameClass.nonempty


instance : EquivalenceFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]) where
  define := by
    intro F;
    constructor;
    . rintro ⟨F_refl, F_trans, F_symm⟩;
      refine ⟨reflexive_def.mp F_refl, transitive_def.mp F_trans, symmetric_def.mp F_symm⟩;
    . rintro ⟨F_refl, F_trans, F_symm⟩;
      refine ⟨reflexive_def.mpr F_refl, transitive_def.mpr F_trans, symmetric_def.mpr F_symm⟩;
  nonempty := MultiGeachConfluentFrameClass.nonempty

end

end LO.Kripke


namespace LO.Modal

namespace Kripke

open LO.Kripke
open Formula (atom Kripke.Satisfies)
open Formula.Kripke.Satisfies (multibox_def multidia_def)

variable {α : Type u}


section

variable [Inhabited α]

lemma axiomGeach_defines : ∀ {F : Kripke.Frame}, (F#α ⊧* 𝗴𝗲(t) ↔ F ∈ (GeachConfluentFrameClass t)) := by
  intro F;
  simp [Semantics.RealizeSet];
  constructor;
  . rintro h x y z ⟨hi, hj⟩;
    let M : Model α := { Frame := F, Valuation := λ v _ => y ≺^[t.m] v };
    simp at h;
    have him_x : Kripke.Satisfies M x (◇^[t.i](□^[t.m](atom default))) := by
      apply Kripke.Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . exact hi;
      . apply Kripke.Satisfies.multibox_def.mpr; aesop;
    have hjn_x : Kripke.Satisfies M x (□^[t.j](◇^[t.n](atom default))) := Kripke.Satisfies.imp_def.mp (h (atom default) M.Valuation x) him_x;
    have hn_z : Kripke.Satisfies M z (◇^[t.n](atom default)) := Kripke.Satisfies.multibox_def.mp hjn_x hj;
    obtain ⟨u, hzu, hyu⟩ := Kripke.Satisfies.multidia_def.mp hn_z;
    use u;
    exact ⟨hyu, hzu⟩;
  . simp [Axioms.Geach, Kripke.Satisfies];
    intro h φ V x him;
    apply multibox_def.mpr;
    intro z rxz;
    apply multidia_def.mpr;
    obtain ⟨y, rxy, hbp⟩ := multidia_def.mp him;
    obtain ⟨u, ryu, rzu⟩ := h ⟨rxy, rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (multibox_def.mp hbp) ryu;

instance axiomGeach_definability : 𝔽((𝗴𝗲(t) : Theory α)).DefinedBy (GeachConfluentFrameClass t) where
  define := axiomGeach_defines;
  nonempty := GeachConfluentFrameClass.nonempty

instance axiomT_defines : 𝔽((𝗧 : Theory α)).DefinedBy ReflexiveFrameClass := by
  convert axiomGeach_definability (α := α) (t := ⟨0, 0, 1, 0⟩);
  simp [GeachConfluentFrameClass, ←GeachConfluent.reflexive_def];

instance axiomFour_defines : 𝔽((𝟰 : Theory α)).DefinedBy TransitiveFrameClass := by
  convert axiomGeach_definability (α := α) (t := ⟨0, 2, 1, 0⟩);
  simp [GeachConfluentFrameClass, ←GeachConfluent.transitive_def];

lemma axiomMultiGeach_defines : ∀ {F : Kripke.Frame}, (F#α ⊧* 𝗚𝗲(ts) ↔ F ∈ (MultiGeachConfluentFrameClass ts)) := by
  intro F;
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluentFrameClass];
  | hsingle t => convert axiomGeach_defines (α := α); simp;
  | hcons t ts ts_nil ih =>
    simp_all only [Semantics.RealizeSet.union_iff, Axioms.MultiGeach.iff_cons, ih];
    rw [(MultiGeachConfluentFrameClass.def_cons ts_nil)];
    constructor;
    . rintro ⟨ht, hts⟩;
      constructor;
      . exact (axiomGeach_defines.mp ht);
      . exact hts;
    . rintro ⟨ht, hts⟩;
      constructor;
      . exact (axiomGeach_defines.mpr ht);
      . exact hts;

instance axiomMultiGeach_definability : 𝔽((𝗚𝗲(ts) : Theory α)).DefinedBy (MultiGeachConfluentFrameClass ts) where
  define := axiomMultiGeach_defines;
  nonempty := MultiGeachConfluentFrameClass.nonempty

instance Geach_definability : 𝔽(Hilbert.Geach α ts).DefinedBy (MultiGeachConfluentFrameClass ts) := inferInstance

instance sound_Geach : Sound (Hilbert.Geach α ts) ((MultiGeachConfluentFrameClass ts)#α) := inferInstance

instance : System.Consistent (Hilbert.Geach α ts) := inferInstance


instance instGeachLogicSound
  {H : Hilbert α} {𝔽 : FrameClass} [logic_geach : H.IsGeach ts] [class_geach : 𝔽.IsGeach ts] : Sound H (𝔽#α) := by
  convert sound_Geach (α := α) (ts := ts);
  . exact logic_geach.char;
  . exact class_geach.equality;

instance KD_sound : Sound (Hilbert.KD α) (SerialFrameClass#α) := inferInstance

instance KT_sound : Sound (Hilbert.KT α) (ReflexiveFrameClass#α) := inferInstance

instance KTB_sound : Sound (Hilbert.KTB α) (ReflexiveSymmetricFrameClass#α) := inferInstance

instance K4_sound : Sound (Hilbert.K4 α) (TransitiveFrameClass#α) := inferInstance

instance S4_sound : Sound (Hilbert.S4 α) (PreorderFrameClass#α) := inferInstance

@[deprecated] lemma S4_sound_aux : (Hilbert.S4 α) ⊢! φ → (PreorderFrameClass#α) ⊧ φ := S4_sound.sound

instance S5_sound : Sound (Hilbert.S5 α) (ReflexiveEuclideanFrameClass#α) := inferInstance

instance KT4B_sound : Sound (Hilbert.KT4B α) (EquivalenceFrameClass#α) := inferInstance

end


open System
open Theory MaximalConsistentTheory CanonicalFrame

variable {Ax : Theory α} [System.Consistent (Hilbert.ExtK Ax)] [DecidableEq α]

lemma geachConfluent_CanonicalFrame (h : 𝗴𝗲(t) ⊆ Ax) : GeachConfluent t (CanonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rintro Ω₁ Ω₂ Ω₃ h;
  have ⟨r₁₂, r₁₃⟩ := h; clear h;
  have ⟨Ω, hΩ⟩ := lindenbaum (H := (Hilbert.ExtK Ax)) (T := □''⁻¹^[t.m]Ω₂.theory ∪ □''⁻¹^[t.n]Ω₃.theory) $ by
    apply intro_union_consistent;
    rintro Γ Δ ⟨hΓ, hΔ⟩ hC;

    replace hΓ : ∀ φ ∈ Γ, □^[t.m]φ ∈ Ω₂.theory := by simpa using hΓ;
    have hΓconj : □^[t.m]⋀Γ ∈ Ω₂.theory := iff_mem_multibox_conj.mpr hΓ;

    replace hΔ : ∀ φ ∈ Δ, □^[t.n]φ ∈ Ω₃.theory := by simpa using hΔ;
    have : □^[t.n]⋀Δ ∈ Ω₃.theory := iff_mem_multibox_conj.mpr hΔ;

    have : □^[t.j](◇^[t.n]⋀Γ) ∈ Ω₁.theory := iff_mem_imp.mp
      (membership_iff.mpr $ Context.of! $ Hilbert.ExtK.maxm! (by aesop))
      (multirel_def_multidia.mp r₁₂ hΓconj)
    have : ◇^[t.n]⋀Γ ∈ Ω₃.theory := multirel_def_multibox.mp r₁₃ this;

    have : (Hilbert.ExtK Ax) ⊢! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := by {
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show _ ⊢! □^[t.n]⋀Δ ➝ □^[t.n](∼⋀Γ) by exact imply_multibox_distribute'! $ contra₁'! $ imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! neg_equiv!))
        (show _ ⊢! □^[t.n](∼⋀Γ) ➝ (◇^[t.n]⋀Γ) ➝ ⊥ by exact imp_trans''! (contra₁'! $ and₁'! $ multidia_duality!) (and₁'! neg_equiv!));
    }
    have : (Hilbert.ExtK Ax) ⊬ □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ➝ ⊥ := by simpa using (def_consistent.mp Ω₃.consistent) (Γ := [□^[t.n]⋀Δ, ◇^[t.n]⋀Γ]) (by simp_all)

    contradiction;

  use Ω; simp only [Set.union_subset_iff] at hΩ;
  constructor;
  . apply multirel_def_multibox.mpr; apply hΩ.1;
  . apply multirel_def_multibox.mpr; apply hΩ.2;

lemma multiGeachConfluent_CanonicalFrame (h : 𝗚𝗲(ts) ⊆ Ax) : MultiGeachConfluent ts (CanonicalFrame (Hilbert.ExtK Ax)).Rel := by
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluent];
  | hsingle t =>
    simp [MultiGeachConfluent.iff_singleton] at h;
    exact geachConfluent_CanonicalFrame h;
  | hcons t ts ts_nil ih =>
    simp [(MultiGeachConfluent.iff_cons ts_nil)];
    constructor;
    . apply geachConfluent_CanonicalFrame; simp_all;
    . apply ih; simp_all;


variable [Inhabited α]

instance instMultiGeachComplete : Complete (Hilbert.ExtK (𝗚𝗲(ts))) ((MultiGeachConfluentFrameClass.{u} ts)#α) :=
  instComplete_of_mem_canonicalFrame (MultiGeachConfluentFrameClass ts) $ by
    apply multiGeachConfluent_CanonicalFrame;
    tauto;

instance {H : Hilbert α} {𝔽 : FrameClass.{u}} [logic_geach : H.IsGeach ts] [class_geach : 𝔽.IsGeach ts] : Complete H (𝔽#α) := by
  convert instMultiGeachComplete (α := α) (ts := ts);
  . exact logic_geach.char;
  . exact class_geach.equality;


instance KT_complete : Complete (Hilbert.KT α) ReflexiveFrameClass.{u}#α := inferInstance

instance KTB_complete : Complete (Hilbert.KTB α) ReflexiveSymmetricFrameClass.{u}#α := inferInstance

instance S4_complete : Complete (Hilbert.S4 α) PreorderFrameClass.{u}#α := inferInstance

instance K4_complete : Complete (Hilbert.K4 α) TransitiveFrameClass.{u}#α := inferInstance

instance KT4B_complete : Complete (Hilbert.KT4B α) EquivalenceFrameClass.{u}#α := inferInstance

instance S5_complete : Complete (Hilbert.S5 α) ReflexiveEuclideanFrameClass.{u}#α := inferInstance

end Kripke


namespace Hilbert

open System
open LO.Kripke
open Kripke
open Formula (atom)
open Formula.Kripke

variable [Inhabited α] [DecidableEq α]

lemma KD_weakerThan_KT : (Hilbert.KD α) ≤ₛ (Hilbert.KT α) := by
  apply weakerThan_of_subset_FrameClass SerialFrameClass ReflexiveFrameClass;
  intro F hF; apply serial_of_refl hF;

theorem KD_strictlyWeakerThan_KT : (Hilbert.KD α) <ₛ (Hilbert.KT α) := by
  constructor;
  . apply KD_weakerThan_KT;
  . simp [weakerThan_iff];
    use (□(atom default) ➝ (atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KD_sound.not_provable_of_countermodel;
      simp [Semantics.Realize];
      use ⟨Fin 2, λ _ y => y = 1⟩;
      constructor;
      . intro x; use 1;
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 1), 0;
        simp [Satisfies];

theorem K_strictlyWeakerThan_KT : (Hilbert.K α) <ₛ (Hilbert.KT α) := strictlyWeakerThan.trans K_strictlyWeakerThan_KD KD_strictlyWeakerThan_KT

theorem K4_strictlyWeakerThan_S4 : (Hilbert.K4 α) <ₛ (Hilbert.S4 α) := by
  constructor;
  . apply K4_weakerThan_S4;
  . simp [weakerThan_iff]
    use (□(atom default) ➝ (atom default));
    constructor;
    . exact Deduction.maxm! (by simp)
    . apply K4_sound.not_provable_of_countermodel;
      simp [Semantics.Realize];
      use ⟨Fin 3, λ _ y => y = 1⟩;
      constructor;
      . intro _ _ _; simp_all;
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 1), 0;
        simp [Satisfies];

lemma S4_weakerThan_S5 : (Hilbert.S4 α) ≤ₛ (Hilbert.S5 α) := by
  apply weakerThan_of_subset_FrameClass PreorderFrameClass ReflexiveEuclideanFrameClass;
  rintro _ ⟨F_refl, F_eucl⟩;
  refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl⟩;

theorem S4_strictlyWeakerThan_S5 : (Hilbert.S4 α) <ₛ (Hilbert.S5 α) := by
  constructor;
  . apply S4_weakerThan_S5;
  . simp [weakerThan_iff];
    use (◇(atom default) ➝ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply S4_sound.not_provable_of_countermodel;
      simp [Semantics.Realize];
      use ⟨Fin 3, λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩;
      refine ⟨⟨?_, ?_⟩, ?_⟩;
      . simp [Reflexive];
      . simp [Transitive]; aesop;
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 2), 0;
        simp [Satisfies];
        constructor;
        . omega;
        . use 1; omega;

theorem equiv_S5_KT4B : (Hilbert.S5 α) =ₛ (Hilbert.KT4B α) := by
  apply equiv_of_eq_FrameClass ReflexiveEuclideanFrameClass EquivalenceFrameClass;
  apply Set.eq_of_subset_of_subset;
  . rintro F ⟨F_refl, F_eucl⟩;
    refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl, symm_of_refl_eucl F_refl F_eucl⟩;
  . rintro F ⟨F_refl, F_eucl, F_symm⟩;
    refine ⟨F_refl, eucl_of_symm_trans F_symm F_eucl⟩;

end Hilbert

end LO.Modal
