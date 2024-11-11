import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Geach
import Foundation.Modal.Kripke.Completeness


namespace LO.Modal

namespace Kripke

abbrev GeachConfluentFrameClass (t : GeachConfluent.Taple) : FrameClass := { F | (GeachConfluent t) F.Rel }

instance GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass t).Nonempty := by
  use reflexivePointFrame.toFrame;
  intros x _ _ _; use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }


abbrev MultiGeachConfluentFrameClass (ts : List GeachConfluent.Taple) : FrameClass := { F | (MultiGeachConfluent ts) F.Rel }

namespace MultiGeachConfluentFrameClass

@[simp] lemma def_nil : MultiGeachConfluentFrameClass [] = AllFrameClass := by rfl;

lemma def_one (t : GeachConfluent.Taple) : MultiGeachConfluentFrameClass [t] = GeachConfluentFrameClass t := by rfl;

lemma def_cons {t : GeachConfluent.Taple} {ts : List GeachConfluent.Taple} (ts_nil : ts ≠ [])
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


abbrev FrameClass.IsGeach (C : FrameClass) (ts : List GeachConfluent.Taple) := C = MultiGeachConfluentFrameClass ts


section

abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F.Rel }

lemma ReflexiveFrameClass.is_geach : ReflexiveFrameClass.IsGeach [⟨0, 0, 1, 0⟩] := by
  simp only [FrameClass.IsGeach, ReflexiveFrameClass, GeachConfluent.reflexive_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];


abbrev SerialFrameClass : FrameClass := { F | Serial F.Rel }

lemma SerialFrameClass.is_geach : SerialFrameClass.IsGeach [⟨0, 0, 1, 1⟩] := by
  simp only [FrameClass.IsGeach, SerialFrameClass, GeachConfluent.serial_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];


abbrev TransitiveFrameClass : FrameClass := { F | Transitive F.Rel }

lemma TransitiveFrameClass.is_geach : TransitiveFrameClass.IsGeach ([⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, TransitiveFrameClass, GeachConfluent.transitive_def,
    MultiGeachConfluentFrameClass.def_one, GeachConfluentFrameClass];


abbrev ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F.Rel ∧ Euclidean F.Rel }

lemma ReflexiveEuclideanFrameClass.is_geach : ReflexiveEuclideanFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨1, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveEuclideanFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.euclidean_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];


abbrev ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }

lemma ReflexiveSymmetricFrameClass.is_geach : ReflexiveSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveSymmetricFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.symmetric_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];


abbrev ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }

lemma ReflexiveTransitiveFrameClass.is_geach : ReflexiveTransitiveFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveFrameClass, GeachConfluent.reflexive_def,
    GeachConfluent.transitive_def, MultiGeachConfluentFrameClass, MultiGeachConfluent];


abbrev ReflexiveTransitiveConfluentFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F }

lemma ReflexiveTransitiveConfluentFrameClass.is_geach : ReflexiveTransitiveConfluentFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveConfluentFrameClass,
    GeachConfluent.reflexive_def, GeachConfluent.transitive_def, GeachConfluent.confluent_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];


abbrev ReflexiveTransitiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }

lemma ReflexiveTransitiveSymmetricFrameClass.is_geach : ReflexiveTransitiveSymmetricFrameClass.IsGeach ([⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩]) := by
  simp only [FrameClass.IsGeach, ReflexiveTransitiveSymmetricFrameClass,
    GeachConfluent.reflexive_def, GeachConfluent.transitive_def, GeachConfluent.symmetric_def,
    MultiGeachConfluentFrameClass, MultiGeachConfluent];

end


section definability

open Kripke
open Formula
open Formula.Kripke (Satisfies)
open Formula.Kripke.Satisfies

lemma GeachConfluentFrameClass.isDefinedBy {t : GeachConfluent.Taple} : (GeachConfluentFrameClass t).DefinedBy 𝗴𝗲(t) := by
  intro F;
  constructor;
  . intro hG;
    simp [GeachConfluentFrameClass];
    intro φ V x him;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨y, Rxy, hbp⟩ := multidia_def.mp him;
    obtain ⟨u, Ryu, Rzu⟩ := hG ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (Satisfies.multibox_def.mp hbp) Ryu;
  . rintro h x y z ⟨hi, hj⟩;
    simp [Kripke.ValidOnFrame] at h;
    let M : Model := ⟨F, λ v _ => y ≺^[t.m] v ⟩;
    have him_x : Satisfies M x (◇^[t.i](□^[t.m](atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . exact hi;
      . apply Satisfies.multibox_def.mpr; aesop;
    have hjn_x : Kripke.Satisfies M x (□^[t.j](◇^[t.n](atom 0))) := Satisfies.imp_def.mp (h (atom 0) M.Val x) him_x;
    have hn_z : Kripke.Satisfies M z (◇^[t.n](atom 0)) := Satisfies.multibox_def.mp hjn_x hj;
    obtain ⟨u, hzu, hyu⟩ := Kripke.Satisfies.multidia_def.mp hn_z;
    use u;
    exact ⟨hyu, hzu⟩;

lemma MultiGeachConfluentFrameClass.isDefinedBy {ts : List GeachConfluent.Taple} : (MultiGeachConfluentFrameClass ts).DefinedBy 𝗚𝗲(ts) := by
  intro F;
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluentFrameClass];
  | hsingle t =>
    simp only [MultiGeachConfluentFrameClass.def_one, Axioms.MultiGeach.def_one];
    apply GeachConfluentFrameClass.isDefinedBy;
  | hcons t ts ts_nil ih =>
    simp [MultiGeachConfluentFrameClass.def_cons (ts_nil := ts_nil)];
    constructor;
    . rintro ⟨ht, hts⟩;
      constructor;
      . intro φ
        apply Semantics.realizeSet_iff.mp $ @GeachConfluentFrameClass.isDefinedBy (t := t) F |>.mp ht
        tauto;
      . apply ih.mp;
        exact hts;
    . rintro ⟨ht, hts⟩;
      constructor;
      . apply @GeachConfluentFrameClass.isDefinedBy t F |>.mpr;
        apply Semantics.realizeSet_iff.mpr;
        simpa using ht;
      . apply ih.mpr hts;

lemma ReflexiveFrameClass.isDefinedBy : (ReflexiveFrameClass).DefinedBy 𝗧 := by
  rw [ReflexiveFrameClass.is_geach, Axioms.T.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

lemma SerialFrameClass.isDefinedBy : (SerialFrameClass).DefinedBy 𝗗 := by
  rw [SerialFrameClass.is_geach, Axioms.D.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

lemma TransitiveFrameClass.isDefinedBy : (TransitiveFrameClass).DefinedBy 𝟰 := by
  rw [TransitiveFrameClass.is_geach, Axioms.Four.is_geach];
  apply GeachConfluentFrameClass.isDefinedBy;

end definability

end Kripke


namespace Hilbert

open Modal.Kripke


section soundness

open Hilbert.Kripke

instance KD.Kripke.sound : Sound (Hilbert.KD ℕ) (SerialFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [SerialFrameClass.is_geach]; apply GeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach, Axioms.MultiGeach.def_one])

instance KD.consistent : System.Consistent (Hilbert.KD ℕ) := instConsistent_of_nonempty_frameclass (C := SerialFrameClass) $ by
  rw [SerialFrameClass.is_geach];
  simp;


instance KT.Kripke.sound : Sound (Hilbert.KT ℕ) (ReflexiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveFrameClass.is_geach]; apply GeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach, Axioms.MultiGeach.def_one])

instance KT.consistent : System.Consistent (Hilbert.KT ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveFrameClass) $ by
  rw [ReflexiveFrameClass.is_geach];
  simp;


instance KTB.Kripke.sound : Sound (Hilbert.KTB ℕ) (ReflexiveSymmetricFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveSymmetricFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance KTB.consistent : System.Consistent (Hilbert.KTB ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveSymmetricFrameClass) $ by
  rw [ReflexiveSymmetricFrameClass.is_geach];
  simp;


instance K4.Kripke.sound : Sound (Hilbert.K4 ℕ) (TransitiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [TransitiveFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance K4.consistent : System.Consistent (Hilbert.K4 ℕ) := instConsistent_of_nonempty_frameclass (C := TransitiveFrameClass) $ by
  rw [TransitiveFrameClass.is_geach];
  simp;


instance S4.Kripke.sound : Sound (Hilbert.S4 ℕ) (ReflexiveTransitiveFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveTransitiveFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance S4.consistent : System.Consistent (Hilbert.S4 ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveTransitiveFrameClass) $ by
  rw [ReflexiveTransitiveFrameClass.is_geach];
  simp;


instance S5.Kripke.sound : Sound (Hilbert.S5 ℕ) (ReflexiveEuclideanFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveEuclideanFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance S5.consistent : System.Consistent (Hilbert.S5 ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveEuclideanFrameClass) $ by
  rw [ReflexiveEuclideanFrameClass.is_geach];
  simp;


instance KT4B.Kripke.sound : Sound (Hilbert.KT4B ℕ) (ReflexiveTransitiveSymmetricFrameClass) :=
  instSound_of_frameClass_definedBy
  (by rw [ReflexiveTransitiveSymmetricFrameClass.is_geach]; apply MultiGeachConfluentFrameClass.isDefinedBy)
  (by simp [is_geach, Hilbert.Geach])

instance KT4B.consistent : System.Consistent (Hilbert.KT4B ℕ) := instConsistent_of_nonempty_frameclass (C := ReflexiveTransitiveSymmetricFrameClass) $ by
  rw [ReflexiveTransitiveSymmetricFrameClass.is_geach];
  simp;

end soundness


namespace Kripke

open System
open Theory MaximalConsistentTheory
open canonicalFrame

namespace canonicalFrame

variable {Ax : Theory ℕ} [(Hilbert.ExtK Ax).Consistent]

lemma is_geachConfluent_of_subset_Geach (h : 𝗴𝗲(t) ⊆ Ax) : GeachConfluent t (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
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

lemma is_multiGeachConfluent_of_subset_MultiGeach (h : 𝗚𝗲(ts) ⊆ Ax) : MultiGeachConfluent ts (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  induction ts using List.induction_with_singleton with
  | hnil => simp [MultiGeachConfluent];
  | hsingle t =>
    simp [MultiGeachConfluent.iff_singleton] at h;
    exact is_geachConfluent_of_subset_Geach h;
  | hcons t ts ts_nil ih =>
    simp [(MultiGeachConfluent.iff_cons ts_nil)];
    constructor;
    . apply is_geachConfluent_of_subset_Geach; simp_all;
    . apply ih; simp_all;

lemma is_reflexive_of_subset_T (h : 𝗧 ⊆ Ax) : Reflexive (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.reflexive_def, Axioms.T.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_serial_of_subset_D (h : 𝗗 ⊆ Ax) : Serial (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.serial_def, Axioms.D.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_transitive_of_subset_Four (h : 𝟰 ⊆ Ax) : Transitive (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.transitive_def, Axioms.Four.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_euclidean_of_subset_Five (h : 𝟱 ⊆ Ax) : Euclidean (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.euclidean_def, Axioms.Five.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

lemma is_symmetric_of_subset_B (h : 𝗕 ⊆ Ax) : Symmetric (canonicalFrame (Hilbert.ExtK Ax)).Rel := by
  rw [GeachConfluent.symmetric_def, Axioms.B.is_geach] at *
  apply is_geachConfluent_of_subset_Geach;
  exact h;

end canonicalFrame

end Kripke


section completeness

instance KT.Kripke.complete : Complete (Hilbert.KT ℕ) ReflexiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp [Axioms.T.is_geach];

instance KTB.Kripke.complete : Complete (Hilbert.KTB ℕ) ReflexiveSymmetricFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveSymmetricFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp [Axioms.MultiGeach.def_two, Axioms.T.is_geach, Axioms.B.is_geach];

instance K4.Kripke.complete : Complete (Hilbert.K4 ℕ) TransitiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [TransitiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp;

instance S4.Kripke.complete : Complete (Hilbert.S4 ℕ) ReflexiveTransitiveFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveTransitiveFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.MultiGeach.def_two];

instance KT4B.Kripke.complete : Complete (Hilbert.KT4B ℕ) ReflexiveTransitiveSymmetricFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveTransitiveSymmetricFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp [Axioms.T.is_geach, Axioms.Four.is_geach, Axioms.B.is_geach, Axioms.MultiGeach.def_three];

instance S5.Kripke.complete : Complete (Hilbert.S5 ℕ) ReflexiveEuclideanFrameClass := Kripke.instCompleteOfCanonical $ by
  rw [ReflexiveEuclideanFrameClass.is_geach];
  apply Kripke.canonicalFrame.is_multiGeachConfluent_of_subset_MultiGeach;
  simp [Axioms.T.is_geach, Axioms.Five.is_geach, Axioms.MultiGeach.def_two];

end completeness


section

open System
open Formula (atom)
open Formula.Kripke

lemma KD_weakerThan_KT : (Hilbert.KD ℕ) ≤ₛ (Hilbert.KT ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass SerialFrameClass ReflexiveFrameClass;
  intro F hF; apply serial_of_refl hF;

theorem KD_strictlyWeakerThan_KT : (Hilbert.KD ℕ) <ₛ (Hilbert.KT ℕ) := by
  constructor;
  . apply KD_weakerThan_KT;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KD.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ _ y => y = 1⟩;
      constructor;
      . intro x; use 1;
      . use (λ w _ => w = 1), 0;
        simp [Semantics.Realize, Satisfies];

theorem K_strictlyWeakerThan_KT : (Hilbert.K ℕ) <ₛ (Hilbert.KT ℕ) := strictlyWeakerThan.trans K_strictlyWeakerThan_KD KD_strictlyWeakerThan_KT

theorem K4_strictlyWeakerThan_S4 : (Hilbert.K4 ℕ) <ₛ (Hilbert.S4 ℕ) := by
  constructor;
  . apply K4_weakerThan_S4;
  . simp [weakerThan_iff]
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! (by simp)
    . apply K4.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 3, λ _ y => y = 1⟩;
      constructor;
      . intro _ _ _; simp_all;
      . use (λ w _ => w = 1), 0;
        simp [Semantics.Realize, Satisfies];

lemma S4_weakerThan_S5 : (Hilbert.S4 ℕ) ≤ₛ (Hilbert.S5 ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass ReflexiveTransitiveFrameClass ReflexiveEuclideanFrameClass;
  rintro _ ⟨F_refl, F_eucl⟩;
  refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl⟩;

theorem S4_strictlyWeakerThan_S5 : (Hilbert.S4 ℕ) <ₛ (Hilbert.S5 ℕ) := by
  constructor;
  . apply S4_weakerThan_S5;
  . simp [weakerThan_iff];
    use (◇(atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply S4.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 3, λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩;
      refine ⟨?_, ?_, ?_⟩;
      . simp [Reflexive];
      . simp [Transitive]; aesop;
      . use (λ w _ => w = 2), 0;
        simp [Satisfies, Semantics.Realize];
        constructor;
        . omega;
        . use 1; omega;

theorem equiv_S5_KT4B : (Hilbert.S5 ℕ) =ₛ (Hilbert.KT4B ℕ) := by
  apply Kripke.equiv_of_eq_FrameClass ReflexiveEuclideanFrameClass ReflexiveTransitiveSymmetricFrameClass;
  apply Set.eq_of_subset_of_subset;
  . rintro F ⟨F_refl, F_eucl⟩;
    refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl, symm_of_refl_eucl F_refl F_eucl⟩;
  . rintro F ⟨F_refl, F_eucl, F_symm⟩;
    refine ⟨F_refl, eucl_of_symm_trans F_symm F_eucl⟩;

end

end Hilbert

end LO.Modal
