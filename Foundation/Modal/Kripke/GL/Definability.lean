import Foundation.Modal.Kripke.Semantics
import Foundation.Vorspiel.BinaryRelations

namespace LO.Modal

namespace Kripke

open System
open Kripke
open Formula
open Formula.Kripke

abbrev TransitiveConverseWellFoundedFrameClass : FrameClass := { F | Transitive F.Rel ∧ ConverseWellFounded F.Rel }
abbrev TransitiveIrreflexiveFiniteFrameClass : FiniteFrameClass := { F | Transitive F.Rel ∧ Irreflexive F.Rel }

private lemma L_of_trans_and_cwf {F : Kripke.Frame} : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F ⊧* 𝗟 := by
  rintro ⟨hTrans, hWF⟩;
  simp [Axioms.L];
  intro φ V w;
  apply Satisfies.imp_def.mpr;
  contrapose;
  intro h; simp [Kripke.Satisfies] at h;
  obtain ⟨x, Rwx, h⟩ := by simpa using Kripke.Satisfies.box_def.not.mp h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Kripke.Satisfies ⟨F, V⟩ x φ) }) $ by use x; tauto;
  apply Satisfies.box_def.not.mpr; push_neg;
  use m;
  constructor;
  . exact rwm;
  . apply Satisfies.imp_def.not.mpr; push_neg;
    constructor;
    . simp [flip] at hm₂;
      intro n rmn;
      apply not_imp_not.mp $ hm₂ n (hTrans rwm rmn);
      exact rmn;
    . exact hm;

private lemma trans_of_L {F : Kripke.Frame} : F ⊧* 𝗟 → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w, v, Rwv, u, Rvu, nRwu⟩ := hT;
  simp [ValidOnFrame, ValidOnModel];
  use (atom 0), (λ w _ => w ≠ v ∧ w ≠ u), w;
  apply Satisfies.imp_def.not.mpr; push_neg;
  constructor;
  . intro x Rwx hx;
    by_cases exv : x = v;
    . rw [exv] at hx;
      simpa [Satisfies] using @hx u Rvu
    . simp [Satisfies];
      constructor;
      . assumption;
      . by_contra hC;
        rw [hC] at Rwx;
        contradiction;
  . apply Satisfies.box_def.not.mpr;
    push_neg;
    use v;
    constructor;
    . assumption;
    . simp [Semantics.Realize, Kripke.Satisfies];

private lemma cwf_of_L {F : Kripke.Frame} : F ⊧* 𝗟 → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, ⟨x, _⟩, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  simp [ValidOnFrame, ValidOnModel];
  use (atom 0), (λ w _ => w ∉ X), x;
  apply Satisfies.imp_def.not.mpr; push_neg;
  constructor;
  . intro y _;
    by_cases hys : y ∈ X
    . obtain ⟨z, _, Rxz⟩ := hX₂ y hys;
      intro hy;
      have := hy z Rxz;
      simp [Satisfies] at this;
      contradiction;
    . intro _;
      simpa [Satisfies];
  . obtain ⟨y, _, _⟩ := hX₂ x (by assumption);
    apply Satisfies.box_def.not.mpr; push_neg;
    use y;
    constructor;
    . assumption;
    . simpa [Semantics.Realize, Kripke.Satisfies];

lemma TransitiveConverseWellFoundedFrameClass.is_defined_by_L : TransitiveConverseWellFoundedFrameClass.DefinedBy 𝗟 := by
  intro F;
  constructor;
  . apply L_of_trans_and_cwf;
  . intro h;
    constructor;
    . exact trans_of_L h;
    . exact cwf_of_L h;

lemma FiniteIrreflexiveFrameClass.is_finite_defined_by_L : TransitiveIrreflexiveFiniteFrameClass.DefinedBy 𝗟 := by
  intro F;
  constructor;
  . rintro ⟨hTrans, hIrrefl⟩;
    apply L_of_trans_and_cwf;
    constructor
    . assumption;
    . apply Finite.converseWellFounded_of_trans_irrefl';
      . exact F.world_finite;
      . assumption;
      . assumption
  . rintro h;
    refine ⟨?_, ?_⟩;
    . exact trans_of_L h;
    . intro w;
      simpa using ConverseWellFounded.iff_has_max.mp (cwf_of_L h) {w} (by simp);

end Kripke


namespace Hilbert

open Modal.Kripke

instance GL.Kripke.sound : Sound (Hilbert.GL ℕ) (TransitiveConverseWellFoundedFrameClass) :=
  Kripke.instSound_of_frameClass_definedBy (C := TransitiveConverseWellFoundedFrameClass) Kripke.TransitiveConverseWellFoundedFrameClass.is_defined_by_L rfl

instance GL.Kripke.finite_sound : Sound (Hilbert.GL ℕ) (TransitiveIrreflexiveFiniteFrameClass) :=
  Kripke.instSound_of_finiteFrameClass_definedBy FiniteIrreflexiveFrameClass.is_finite_defined_by_L rfl

instance GL.consistent : System.Consistent (Hilbert.GL ℕ) := Kripke.instConsistent_of_nonempty_finiteFrameclass (FC := TransitiveIrreflexiveFiniteFrameClass) $ by
  use irreflexivePointFrame;
  simp [Transitive, Irreflexive];

end Hilbert

end LO.Modal
