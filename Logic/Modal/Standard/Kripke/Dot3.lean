import Logic.Modal.Standard.Kripke.Geach

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

abbrev ConnectedFrameClass (α) : FrameClass α := { F | Connected F }

variable {α} [Inhabited α] [DecidableEq α] [atleast : Atleast 2 α]
variable {F : Kripke.Frame α}

private lemma connected_of_dot3 : F ⊧* .𝟯 → Connected F.Rel := by
  contrapose;
  intro hCon; simp [Connected] at hCon;
  obtain ⟨x, y, rxy, z, ryz, nryz, nrzy⟩ := hCon;
  simp [valid_on_KripkeFrame];
  obtain ⟨f, finv, fInj⟩ := atleast.mapping;
  existsi f 0, f 1, (λ w a =>
    match (finv a) with
    | 0 => y ≺ w
    | 1 => z ≺ w
  );
  simp [valid_on_KripkeModel, kripke_satisfies];
  use x;
  constructor;
  . use y;
    constructor;
    . assumption;
    . simp_all [kripke_satisfies, (fInj 0), (fInj 1)];
  . use z;
    constructor;
    . assumption;
    . simp_all [kripke_satisfies, (fInj 0), (fInj 1)];

private lemma dot3_of_connected : Connected F.Rel → F ⊧* .𝟯 := by
  intro hCon;
  simp [valid_on_KripkeFrame, valid_on_KripkeModel, Axioms.Dot3];
  intro _ p q e V x; subst e;
  simp [kripke_satisfies];
  by_contra hC; push_neg at hC;
  obtain ⟨⟨y, rxy, hp, hnq⟩, ⟨z, rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨rxy, rxz⟩ with
  | inl ryz => exact hnp $ hp ryz;
  | inr rzy => exact hnq $ hq rzy;

lemma AxDot3_Definability : .𝟯.DefinesKripkeFrameClass (ConnectedFrameClass α) := by
  intro F;
  constructor;
  . exact connected_of_dot3;
  . exact dot3_of_connected;

abbrev ReflexiveTransitiveConnectedFrameClass (α) : FrameClass α := { F | Reflexive F ∧ Transitive F ∧ Connected F }

lemma ReflexiveTransitiveConnectedFrameClass.nonempty : (ReflexiveTransitiveConnectedFrameClass α).Nonempty := by
  use (TerminalFrame α);
  simp [Reflexive, Transitive, Connected];


private lemma S4Dot3_defines' : (𝗧 ∪ 𝟰 ∪ .𝟯).DefinesKripkeFrameClass (ReflexiveTransitiveConnectedFrameClass α) := by
  rw [(show ReflexiveTransitiveConnectedFrameClass α = { (F : Frame α) | (Reflexive F ∧ Transitive F) ∧ Connected F } by aesop)];
  apply AxiomSet.DefinesKripkeFrameClass.union;
  . exact S4_defines.toAx';
  . exact AxDot3_Definability;

lemma S4Dot3_defines : 𝐒𝟒.𝟑.DefinesKripkeFrameClass (ReflexiveTransitiveConnectedFrameClass α) :=
  DeductionParameter.DefinesKripkeFrameClass.ofAx S4Dot3_defines'

instance : System.Consistent (𝐒𝟒.𝟑 : DeductionParameter α) := consistent_of_defines S4Dot3_defines' ReflexiveTransitiveConnectedFrameClass.nonempty


open MaximalConsistentTheory in
lemma connected_CanonicalFrame {Ax : AxiomSet α} (hAx : .𝟯 ⊆ Ax) [System.Consistent Axᴺ] : Connected (CanonicalFrame Ax).Rel := by
  dsimp only [Connected];
  intro X Y Z ⟨hXY, hXZ⟩;
  by_contra hC; push_neg at hC;
  have ⟨nhYZ, nhZY⟩ := hC; clear hC;
  simp only [Set.not_subset] at nhYZ nhZY;
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

instance : Complete (𝐒𝟒.𝟑 : DeductionParameter α) (ReflexiveTransitiveConnectedFrameClass α) := instComplete_of_mem_canonicalFrame $ by
  refine ⟨?reflexive, ?transitive, ?connective⟩;
  . rw [←GeachConfluent.reflexive_def];
    apply geachConfluent_CanonicalFrame;
    rw [AxiomSet.Geach.T_def]; simp;
  . rw [←GeachConfluent.transitive_def];
    apply geachConfluent_CanonicalFrame;
    rw [AxiomSet.Geach.Four_def]; simp;
  . apply connected_CanonicalFrame; simp;

end Kripke

end LO.Modal.Standard
