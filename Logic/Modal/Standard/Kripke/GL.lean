import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Soundness

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]
variable {F : Kripke.Frame δ}

abbrev TransitiveCWFFrameClass : FrameClass := { ⟨_, F⟩ | Transitive F ∧ ConverseWellFounded F }

private lemma trans_of_L : F[α] ⊧* 𝗟 → Transitive F.Rel := by
  contrapose;
  intro hT; simp [Transitive] at hT;
  obtain ⟨w₁, w₂, r₁₂, w₃, r₂₃, nr₁₃⟩ := hT;
  simp [valid_on_KripkeFrame, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];
  use (atom default), (λ w' _ => w' ≠ w₂ ∧ w' ≠ w₃), w₁;
  constructor;
  . intro x hx h;
    by_cases hx₂ : x = w₂;
    . subst hx₂; simpa [kripke_satisfies] using h r₂₃;
    . by_cases hx₃ : x = w₃ <;> simp_all [kripke_satisfies, hx₃];
  . existsi w₂; simpa [kripke_satisfies];

private lemma cwf_of_L  : F[α] ⊧* 𝗟 → ConverseWellFounded F.Rel := by
  contrapose;
  intro hCF;
  obtain ⟨X, hX₁, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
  simp [valid_on_KripkeFrame, valid_on_KripkeFrame, valid_on_KripkeModel, kripke_satisfies];
  use (atom default), (λ w _ => w ∉ X), hX₁.some;
  constructor;
  . intro x _;
    by_cases hxs : x ∈ X
    . obtain ⟨y, hy₁, hy₂⟩ := hX₂ x hxs;
      intro h;
      exact h (by simp_all only [kripke_satisfies]);
    . aesop;
  . obtain ⟨w', hw'₁, hw'₂⟩ := hX₂ hX₁.some (by apply Set.Nonempty.some_mem);
    existsi w';
    constructor;
    . simpa using hw'₂;
    . simpa [kripke_satisfies];

private lemma L_of_trans_and_cwf : (Transitive F.Rel ∧ ConverseWellFounded F.Rel) → F[α] ⊧* 𝗟 := by
  rintro ⟨hTrans, hWF⟩;
  simp [AxiomSet.L, Axioms.L];
  intro p V w;
  simp [kripke_satisfies];
  contrapose; push_neg;
  intro h;
  obtain ⟨z, rwz, hz⟩ := h;
  obtain ⟨m, ⟨⟨rwm, hm⟩, hm₂⟩⟩ := hWF.has_min ({ x | (F.Rel w x) ∧ ¬(kripke_satisfies ⟨F, V⟩ x p) }) (by use z; simp_all)
  use m;
  constructor;
  . exact rwm;
  . constructor;
    . simp [flip] at hm₂;
      intro n rmn;
      apply not_imp_not.mp $ hm₂ n (hTrans rwm rmn);
      exact rmn;
    . exact hm;

lemma axiomL_defines : 𝗟.DefinesKripkeFrameClass (α := α) (TransitiveCWFFrameClass) := by
  intro _ F;
  constructor;
  . intro h;
    constructor;
    . exact trans_of_L h;
    . exact cwf_of_L h;
  . exact L_of_trans_and_cwf;


abbrev TransitiveIrreflexiveFiniteFrameClass : FiniteFrameClass := { ⟨_, F⟩ | Transitive F.toFrame ∧ Irreflexive F.toFrame }


lemma TransitiveIrreflexiveFiniteFrameClass.nonempty : TransitiveIrreflexiveFiniteFrameClass.Nonempty.{0} := by
  use ⟨Fin 1, PointFrame⟩;
  simp [Transitive, Irreflexive];

lemma axiomL_finite_defines : 𝗟.FinitelyDefinesKripkeFrameClass (α := α) TransitiveIrreflexiveFiniteFrameClass := by
  intro δ F;
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
    . exact Finite.converseWellFounded_of_trans_irrefl' F.δ_finite hTrans hIrrefl;

instance : Sound 𝐆𝐋 TransitiveIrreflexiveFiniteFrameClass[α] := sound_of_finitely_defines axiomL_finite_defines

instance : System.Consistent (𝐆𝐋 : DeductionParameter α) := consistent_of_finitely_defines axiomL_finite_defines TransitiveIrreflexiveFiniteFrameClass.nonempty


end Kripke

end LO.Modal.Standard
