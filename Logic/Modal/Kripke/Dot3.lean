import Logic.Modal.Kripke.Geach

namespace LO.Kripke

end LO.Kripke

namespace LO.Modal

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α] [DecidableEq α] [atleast : Atleast 2 α]
variable {F : Kripke.Frame}

private lemma connected_of_dot3 : F#α ⊧* (.𝟯 : AxiomSet α) → Connected F := by
  contrapose;
  intro hCon; simp [Connected] at hCon;
  obtain ⟨x, y, rxy, z, ryz, nryz, nrzy⟩ := hCon;
  simp [Kripke.ValidOnFrame];
  obtain ⟨f, finv, fInj⟩ := atleast.mapping;
  existsi f 0, f 1, (λ w a =>
    match (finv a) with
    | 0 => y ≺ w
    | 1 => z ≺ w
  );
  simp [Kripke.ValidOnModel];
  use x;
  apply Kripke.Satisfies.or_def.not.mpr;
  push_neg;
  constructor;
  . apply Kripke.Satisfies.box_def.not.mpr; push_neg;
    use y;
    simp_all [Semantics.Realize, Kripke.Satisfies, (fInj 0), (fInj 1)];
  . apply Kripke.Satisfies.box_def.not.mpr; push_neg;
    use z;
    simp_all [Semantics.Realize, Kripke.Satisfies, (fInj 0), (fInj 1)];

private lemma dot3_of_connected : Connected F → F#α ⊧* (.𝟯 : AxiomSet α) := by
  intro hCon;
  simp [Kripke.ValidOnFrame, Kripke.ValidOnModel, Axioms.Dot3];
  intro δ p q e V x; subst e;
  apply Kripke.Satisfies.or_def.mpr;
  simp [Kripke.Satisfies];
  by_contra hC; push_neg at hC;
  obtain ⟨⟨y, rxy, hp, hnq⟩, ⟨z, rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨rxy, rxz⟩ with
  | inl ryz => have := hp z ryz; contradiction;
  | inr rzy => have := hq y rzy; contradiction;

instance axiomDot3_Definability : 𝔽((.𝟯 : Theory α)).DefinedBy ConnectedFrameClass where
  define := by
    intro F;
    constructor;
    . exact connected_of_dot3;
    . exact dot3_of_connected;
  nonempty := by
    use ⟨PUnit, λ _ _ => True⟩;
    tauto;

instance axiomS4Dot3_defines : 𝔽(((𝗧 ∪ 𝟰 ∪ .𝟯) : Theory α)).DefinedBy ReflexiveTransitiveConnectedFrameClass := by
  rw [(show ReflexiveTransitiveConnectedFrameClass = ({ F | (Reflexive F ∧ Transitive F) ∧ Connected F } : FrameClass) by aesop)];
  apply definability_union_frameclass_of_theory;
  . convert axiomMultiGeach_definability (ts := [⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩]);
    . aesop;
    . simp [GeachConfluent.reflexive_def, GeachConfluent.transitive_def]; rfl;
    . assumption;
  . exact axiomDot3_Definability;
  . use ⟨PUnit, λ _ _ => True⟩;
    simp [Reflexive, Transitive, Connected];
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> tauto;

instance S4Dot3_defines : 𝔽((𝐒𝟒.𝟑 : DeductionParameter α)).DefinedBy ReflexiveTransitiveConnectedFrameClass := inferInstance

instance : System.Consistent (𝐒𝟒.𝟑 : DeductionParameter α) := inferInstance

open MaximalConsistentTheory in
lemma connected_CanonicalFrame {Ax : AxiomSet α} (hAx : .𝟯 ⊆ Ax) [System.Consistent (𝝂Ax)] : Connected (CanonicalFrame 𝝂Ax) := by
  dsimp only [Connected];
  intro X Y Z ⟨hXY, hXZ⟩;
  by_contra hC; push_neg at hC;
  have ⟨nhYZ, nhZY⟩ := hC; clear hC;
  simp only [Frame.Rel', Set.not_subset] at nhYZ nhZY;
  obtain ⟨p, hpY, hpZ⟩ := nhYZ; replace hpY : □p ∈ Y.theory := hpY;
  obtain ⟨q, hqZ, hqY⟩ := nhZY; replace hqZ : □q ∈ Z.theory := hqZ;

  have hpqX : □(□p ⟶ q) ∉ X.theory := by
    apply iff_mem_box.not.mpr; push_neg;
    use Y;
    constructor;
    . assumption;
    . apply iff_mem_imp.not.mpr; simp [hpY, hqY];
  have hqpX : □(□q ⟶ p) ∉ X.theory := by
    apply iff_mem_box.not.mpr; push_neg;
    use Z;
    constructor;
    . assumption;
    . apply iff_mem_imp.not.mpr; simp [hpZ, hqZ];

  have : (□(□p ⟶ q) ⋎ □(□q ⟶ p)) ∉ X.theory := by apply iff_mem_or.not.mpr; push_neg; exact ⟨hpqX, hqpX⟩;
  have : □(□p ⟶ q) ⋎ □(□q ⟶ p) ∈ X.theory := by apply subset_axiomset _; aesop;
  contradiction;

instance : Complete (𝐒𝟒.𝟑 : DeductionParameter α) (ReflexiveTransitiveConnectedFrameClass.{u}#α) := instComplete_of_mem_canonicalFrame ReflexiveTransitiveConnectedFrameClass $ by
  refine ⟨?reflexive, ?transitive, ?connective⟩;
  . simp [GeachConfluent.reflexive_def];
    apply geachConfluent_CanonicalFrame;
    simp [AxiomSet.Geach.T_def];
  . rw [GeachConfluent.transitive_def];
    apply geachConfluent_CanonicalFrame;
    simp [AxiomSet.Geach.Four_def];
  . apply connected_CanonicalFrame;
    simp;

end Kripke

end LO.Modal
