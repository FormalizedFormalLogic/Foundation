import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]

section Definability_and_Soundness

variable {F : Kripke.Frame}

abbrev TransitiveCWFFrameClass : FrameClass := { F | Transitive F ∧ ConverseWellFounded F }

private lemma trans_of_L : F# ⊧* (𝗟 : AxiomSet α) → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, r₁₂, w₃, r₂₃, nr₁₃⟩ := hT;
  simp [Kripke.ValidOnFrame, Kripke.ValidOnFrame, Kripke.ValidOnModel, Kripke.Satisfies];
  use (atom default), (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁;
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . subst hx₂; simpa [Kripke.Satisfies] using h r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [Kripke.Satisfies, hx₃];
  . existsi w₂; simpa [Kripke.Satisfies];

private lemma cwf_of_L  : F# ⊧* (𝗟 : AxiomSet α) → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  simp [Kripke.ValidOnFrame, Kripke.ValidOnFrame, Kripke.ValidOnModel, Kripke.Satisfies];
  use (atom default), (λ w _ => w ∉ X), hX₁.some;
  constructor;
  . intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      intro h;
      exact h (by simp_all only [Kripke.Satisfies]);
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ hX₁.some (by apply Set.Nonempty.some_mem);
    existsi w';
    constructor;
    . simpa using hw'₂;
    . simpa [Kripke.Satisfies];

private lemma L_of_trans_and_cwf : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F# ⊧* (𝗟 : AxiomSet α) := by
  rintro ⟨hTrans, hWF⟩;
  simp [Axioms.L];
  intro p V w;
  simp [Kripke.Satisfies];
  contrapose; push_neg;
  intro h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(Kripke.Satisfies ⟨F, V⟩ x p) }) (by use z; simp_all)
  use m;
  constructor;
  . exact rwm;
  . constructor;
    . simp [flip] at hm₂;
      intro n rmn;
      apply not_imp_not.mp $ hm₂ n (hTrans rwm rmn);
      exact rmn;
    . exact hm;

lemma axiomL_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗟 (TransitiveCWFFrameClass) := by
  intro F;
  constructor;
  . intro h;
    constructor;
    . exact trans_of_L h;
    . exact cwf_of_L h;
  . exact L_of_trans_and_cwf;


abbrev TransitiveIrreflexiveFrameClass : FrameClass := { F | Transitive F ∧ Irreflexive F }

/-
lemma TransitiveIrreflexiveFiniteFrameClass.nonempty : TransitiveIrreflexiveFrameClass.Nonempty.{0} := by
  use PointFrame;
  simp [Transitive, Irreflexive];
-/

lemma axiomL_finite_defines : AxiomSet.FinitelyDefinesKripkeFrameClass (α := α) 𝗟 ↑TransitiveIrreflexiveFrameClass := by
  intro F;
  constructor;
  . intro h;
    obtain ⟨hTrans, hCWF⟩ := axiomL_defines.mp h;
    refine ⟨hTrans, ?irreflexive⟩;
    . intro w;
      simpa using ConverseWellFounded.iff_has_max.mp hCWF {w} (by simp);
  . intro d;
    have ⟨hTrans, hIrrefl⟩ := d;
    apply axiomL_defines.mpr;
    constructor;
    . exact hTrans;
    . exact Finite.converseWellFounded_of_trans_irrefl' F.World_finite hTrans hIrrefl;

instance : Sound (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClassꟳ# := sound_of_finitely_defines axiomL_finite_defines

instance : System.Consistent (𝐆𝐋 : DeductionParameter α) := consistent_of_finitely_defines.{0} axiomL_finite_defines $ by
  use PointFrame;
  simp [Transitive, Irreflexive];

end Definability_and_Soundness

end Kripke

end LO.Modal.Standard
