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

instance AxDot3_Definability : .𝟯.DefinesKripkeFrameClass (ConnectedFrameClass α) where
  defines := by
    intro F;
    constructor;
    . exact connected_of_dot3;
    . exact dot3_of_connected;

abbrev ReflexiveTransitiveConnectedFrameClass (α) : FrameClass α := { F | (Reflexive F ∧ Transitive F) ∧ Connected F }

instance S4dot3_definability : (𝗧 ∪ 𝟰 ∪ .𝟯).DefinesKripkeFrameClass (ReflexiveTransitiveConnectedFrameClass α) :=
  AxiomSet.DefinesKripkeFrameClass.union (by sorry) (AxDot3_Definability)

/-
instance S4dot3.definability : Definability (α := α) Ax(𝐒𝟒.𝟑) (λ F => Reflexive F.Rel ∧ Transitive F.Rel ∧ Connected F.Rel) := by
  have d := Definability.union (P₁ := λ F => (Reflexive F.Rel ∧ Transitive F.Rel)) (by simpa using instGeachDefinability (α := α) (L := 𝐒𝟒)) AxiomSet.Dot3.definability;
  simp at d;
  suffices p : ∀ {F : Frame α}, (Reflexive F.Rel ∧ Transitive F.Rel) ∧ Connected F.Rel ↔ Reflexive F.Rel ∧ Transitive F.Rel ∧ Connected F.Rel by
    constructor;
    intro F;
    constructor;
    . intro h;
      apply p.mp;
      exact d.defines F |>.mp h;
    . intro h;
      exact d.defines F |>.mpr $ p.mpr h;
  aesop;

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(Ax(𝐒𝟒.𝟑)) : FiniteFrameClass α) where
  nonempty := by
    use (TerminalFrame α);
    apply iff_definability_memAxiomSetFrameClass (S4dot3.definability) |>.mpr;
    refine ⟨?reflexive, ?transitive, ?connective⟩;
    . intro x; apply TerminalFrame.iff_rel.mpr; trivial;
    . intro x y z hxy hyz;
      have := TerminalFrame.iff_rel.mp hxy;
      have := TerminalFrame.iff_rel.mp hyz;
      apply TerminalFrame.iff_rel.mpr;
      tauto;
    . intro x y z ⟨hxy, hxz⟩;
      have := TerminalFrame.iff_rel.mp hxy;
      have := TerminalFrame.iff_rel.mp hxz;
      subst_vars;
      left; assumption;

instance : FrameClass.IsNonempty (𝔽(Ax(𝐒𝟒.𝟑)) : FrameClass α) := inferInstance

namespace Kripke

open MaximalConsistentTheory

lemma definability_canonicalFrame_Dot3 {𝓓 : DeductionParameter α} [𝓓.IsNormal] [Inhabited (𝓓)-MCT] (hAx : .𝟯 ⊆ Ax(𝓓))
  : Connected (CanonicalFrame 𝓓).Rel := by
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
  have : (□(□p ⟶ q) ⋎ □(□q ⟶ p)) ∉ X.theory := by
    apply iff_mem_or.not.mpr; push_neg; exact ⟨hpqX, hqpX⟩;

  have : □(□p ⟶ q) ⋎ □(□q ⟶ p) ∈ X.theory := by
    apply subset_axiomset _
    exact hAx (by aesop);
  contradiction;

-- MEMO: 冗長すぎる
instance : Canonical (𝐒𝟒.𝟑 : DeductionParameter α)  := by
  apply canonical_of_definability S4dot3.definability;
  refine ⟨?reflexive, ?transitive, ?connective⟩;
  . rw [←GeachConfluent.reflexive_def];
    apply definability_canonicalFrame_GeachAxiom;
    intro _; aesop;
  . rw [←GeachConfluent.transitive_def];
    apply definability_canonicalFrame_GeachAxiom;
    intro _; aesop;
  . apply definability_canonicalFrame_Dot3;
    intro _; aesop;

instance : Complete (𝐒𝟒.𝟑 : DeductionParameter α) 𝔽(Ax(𝐒𝟒.𝟑)) := instComplete
-/

end Kripke

end LO.Modal.Standard
