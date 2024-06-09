import Logic.Modal.Standard.Kripke.Geach.Completeness

-- MEMO: 相違な2要素が存在する．一般に`n`に拡張できると便利だが出来るかわからない．
class Element₂ (α : Type*) where
  elem₁ : α
  elem₂ : α
  neq₁₂ : elem₂ ≠ elem₁
attribute [simp] Element₂.neq₁₂

namespace LO.Modal.Standard

open System
open Kripke
open Formula Formula.Kripke

variable {α} [Inhabited α] [DecidableEq α]

variable [Element₂ α]
variable {F : Kripke.Frame' α}

open Element₂

private lemma AxiomSet.Dot3.definability.implies : F ⊧* .𝟯 → Connected F.Rel := by
  contrapose;
  intro hCon; simp [Connected] at hCon;
  obtain ⟨x, y, rxy, z, ryz, nryz, nrzy⟩ := hCon;
  simp [ValidOnFrame];
  existsi (atom elem₁), (atom elem₂), (λ w a => if a = elem₁ then y ≺ w else if a = elem₂ then z ≺ w else False); -- TODO: `match`などでどうにか出来ないだろうか？
  simp [ValidOnModel, not_forall, Axioms.Dot3];
  existsi x;
  constructor;
  . existsi y;
    constructor;
    . assumption;
    . simp_all [Satisfies];
  . existsi z;
    constructor;
    . assumption;
    . simp_all [Satisfies];

private lemma AxiomSet.Dot3.definability.impliedBy : Connected F.Rel → F ⊧* .𝟯 := by
  intro hCon;
  simp [ValidOnFrame, ValidOnModel, Axioms.Dot3];
  intro _ p q e V x; subst e;
  simp only [Satisfies.or_def, or_iff_not_imp_left];
  intro hnxpq;
  obtain ⟨y, rxy, hyp, hnyq⟩ := by simpa using hnxpq;
  intro z rxz;
  cases hCon ⟨rxy, rxz⟩ with
  | inl ryz =>
    have := hyp _ ryz;
    simp_all only [Satisfies.imp_def, implies_true];
  | inr rzy =>
    simp [Satisfies.box_def, Satisfies.imp_def]
    intro hq;
    have hyp := hq y rzy;
    contradiction;

instance AxiomSet.Dot3.definability : Definability (α := α) .𝟯 (λ F => Connected F.Rel) where
  defines F := by
    constructor;
    . exact AxiomSet.Dot3.definability.implies;
    . exact AxiomSet.Dot3.definability.impliedBy;

instance S4dot3.definability : Definability (α := α) Ax(𝐒𝟒.𝟑) (λ F => Reflexive F.Rel ∧ Transitive F.Rel ∧ Connected F.Rel) := by
  have d := Definability.union (P₁ := λ F => (Reflexive F.Rel ∧ Transitive F.Rel)) (by simpa using instGeachDefinability (α := α) (L := 𝐒𝟒)) AxiomSet.Dot3.definability;
  simp at d;
  suffices p : ∀ {F : Frame' α}, (Reflexive F.Rel ∧ Transitive F.Rel) ∧ Connected F.Rel ↔ Reflexive F.Rel ∧ Transitive F.Rel ∧ Connected F.Rel by
    constructor;
    intro F;
    constructor;
    . intro h;
      apply p.mp;
      exact d.defines F |>.mp h;
    . intro h;
      exact d.defines F |>.mpr $ p.mpr h;
  aesop;

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(Ax(𝐒𝟒.𝟑)) : FiniteFrameClass' α) := by
  existsi Frame.terminal;
  apply iff_definability_memAxiomSetFrameClass (S4dot3.definability) |>.mpr;
  refine ⟨?reflexive, ?transitive, ?connective⟩;
  . intro x; apply Frame.terminal.rel.mpr; trivial;
  . intro x y z hxy hyz;
    have := Frame.terminal.rel.mp hxy;
    have := Frame.terminal.rel.mp hyz;
    apply Frame.terminal.rel.mpr;
    tauto;
  . intro x y z ⟨hxy, hxz⟩;
    have := Frame.terminal.rel.mp hxy;
    have := Frame.terminal.rel.mp hxz;
    subst_vars;
    left; assumption;

instance : FrameClass.IsNonempty (𝔽(Ax(𝐒𝟒.𝟑)) : FrameClass' α) := inferInstance

namespace Kripke

open MaximalParametricConsistentTheory

lemma definability_canonicalFrame_Dot3 {𝓓 : DeductionParameter α} [𝓓.Normal] [Inhabited (MCT 𝓓)] (hAx : .𝟯 ⊆ Ax(𝓓))
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
    simp only [AxiomSet.Geach.T_def, Set.subset_tetraunion₂];
  . rw [←GeachConfluent.transitive_def];
    apply definability_canonicalFrame_GeachAxiom;
    simp only [AxiomSet.Geach.Four_def, Set.subset_triunion₂];
  . apply definability_canonicalFrame_Dot3;
    simp only [Set.subset_union_right];

instance : Complete (𝐒𝟒.𝟑 : DeductionParameter α) 𝔽(Ax(𝐒𝟒.𝟑)) := instComplete

end Kripke

end LO.Modal.Standard
