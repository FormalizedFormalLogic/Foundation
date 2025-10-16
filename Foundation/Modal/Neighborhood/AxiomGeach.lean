import Foundation.Modal.Neighborhood.Completeness

namespace LO.Modal.Neighborhood

open Formula (atom)
open Formula.Neighborhood


variable {F : Frame} {X Y : Set F.World}

namespace Frame

class IsGeachConvergent (g : Axioms.Geach.Taple) (F : Frame) : Prop where
  gconv : ∀ X : Set F, F.dia^[g.i] (F.box^[g.m] X) ⊆ F.box^[g.j] (F.dia^[g.n] X)

@[simp, grind]
lemma gconv [F.IsGeachConvergent g] : F.dia^[g.i] (F.box^[g.m] X) ⊆ F.box^[g.j] (F.dia^[g.n] X) := IsGeachConvergent.gconv X


class IsReflexive (F : Frame) : Prop where
  refl : ∀ X : Set F, F.box X ⊆ X

@[simp, grind] lemma refl [F.IsReflexive] : F.box X ⊆ X := IsReflexive.refl X
@[simp, grind] lemma refl_dual [F.IsReflexive] : X ⊆ F.dia X := by
  intro x;
  contrapose!;
  intro h;
  have := F.refl (X := Xᶜ);
  have := @this x;
  simp_all [Frame.dia, Frame.box];

instance [F.IsReflexive] : F.IsGeachConvergent ⟨0, 0, 1, 0⟩ := ⟨by simp⟩

instance [F.IsGeachConvergent ⟨0, 0, 1, 0⟩] : F.IsReflexive := ⟨λ _ => F.gconv (g := ⟨0, 0, 1, 0⟩)⟩


class IsTransitive (F : Frame) : Prop where
  trans : ∀ X : Set F, F.box X ⊆ F.box^[2] X

@[simp, grind] lemma trans [F.IsTransitive] : F.box X ⊆ F.box^[2] X := IsTransitive.trans X

instance [F.IsTransitive] : F.IsGeachConvergent ⟨0, 2, 1, 0⟩ := ⟨fun _ ↦ trans⟩

instance [F.IsGeachConvergent ⟨0, 2, 1, 0⟩] : F.IsTransitive := ⟨λ _ => F.gconv (g := ⟨0, 2, 1, 0⟩)⟩


class IsSerial (F : Frame) : Prop where
  serial : ∀ X : Set F, F.box X ⊆ F.dia X
@[simp] lemma serial [F.IsSerial] : F.box X ⊆ F.dia X := IsSerial.serial X

instance [F.IsSerial] : F.IsGeachConvergent ⟨0, 0, 1, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨0, 0, 1, 1⟩] : F.IsSerial := ⟨λ _ => F.gconv (g := ⟨0, 0, 1, 1⟩)⟩


class IsSymmetric (F : Frame) : Prop where
  symm : ∀ X : Set F, X ⊆ F.box (F.dia X)
@[simp] lemma symm [F.IsSymmetric] : X ⊆ F.box (F.dia X) := IsSymmetric.symm X
instance [F.IsSymmetric] : F.IsGeachConvergent ⟨0, 1, 0, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨0, 1, 0, 1⟩] : F.IsSymmetric := ⟨λ _ => F.gconv (g := ⟨0, 1, 0, 1⟩)⟩

lemma IsSymmetric.of_dual {F : Frame} (h : ∀ X : Set F, F.dia (F.box X) ⊆ X) : F.IsSymmetric := by
  constructor;
  intro X w hw;
  have := @h Xᶜ w;
  simp_all;

lemma IsSymmetric.of_alt {F : Frame} (h : ∀ X a, { b | Xᶜ ∉ F.𝒩 b } ∉ F.𝒩 a → a ∉ X) : F.IsSymmetric := by
  constructor;
  intro X a ha;
  have := h X a;
  grind;

lemma iff_IsSymmetric_dual : F.IsSymmetric ↔ ∀ X : Set F, F.dia (F.box X) ⊆ X := by
  constructor;
  . intro h X w;
    have := @F.symm Xᶜ _ w;
    simp_all [Frame.dia, Frame.box];
    tauto;
  . intro h; apply IsSymmetric.of_dual h;

class IsEuclidean (F : Frame) : Prop where
  eucl : ∀ X : Set F, F.dia X ⊆ F.box (F.dia X)

@[simp] lemma eucl [F.IsEuclidean] : F.dia X ⊆ F.box (F.dia X) := IsEuclidean.eucl X

@[simp] lemma eucl_dual [F.IsEuclidean] : F.dia (F.box X) ⊆ F.box X := by
  intro x;
  contrapose!;
  intro h;
  have := F.eucl (X := Xᶜ);
  have := @this x;
  simp_all [Frame.dia, Frame.box];

lemma IsEuclidean.of_dual {F : Frame} (h : ∀ X, F.dia (F.box X) ⊆ F.box X) : F.IsEuclidean := by
  constructor;
  intro X w hw;
  have := @h Xᶜ w;
  simp_all;

lemma IsEuclidean.of_alt {F : Frame} (h : ∀ X a, X ∉ F.𝒩 a → { b | X ∉ F.𝒩 b } ∈ F.𝒩 a) : F.IsEuclidean := by
  constructor;
  intro X a ha;
  have := h X a;
  simp_all [Frame.dia, Frame.box];
  grind;

instance [F.IsEuclidean] : F.IsGeachConvergent ⟨1, 1, 0, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨1, 1, 0, 1⟩] : F.IsEuclidean := ⟨λ _ => F.gconv (g := ⟨1, 1, 0, 1⟩)⟩

end Frame


section

variable {a : ℕ}

lemma valid_axiomGeach_of_isGeachConvergent [F.IsGeachConvergent g] : F ⊧ Axioms.Geach g (.atom a) := by
  intro V x;
  apply Satisfies.def_imp.mpr;
  suffices x ∈ F.dia^[g.i] (F.box^[g.m] (V a)) → x ∈ F.box^[g.j] (F.dia^[g.n] (V a)) by
    simpa [Semantics.Realize, Satisfies];
  apply F.gconv;

@[simp] lemma valid_axiomT_of_isReflexive [F.IsReflexive] : F ⊧ Axioms.T (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 0, 1, 0⟩)
@[simp] lemma valid_axiomD_of_isSerial [F.IsSerial] : F ⊧ Axioms.D (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 0, 1, 1⟩)
@[simp] lemma valid_axiomB_of_isSymmetric [F.IsSymmetric] : F ⊧ Axioms.B (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 1, 0, 1⟩)
@[simp] lemma valid_axiomFour_of_isTransitive [F.IsTransitive] : F ⊧ Axioms.Four (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 2, 1, 0⟩)
@[simp] lemma valid_axiomFive_of_isEuclidean [F.IsEuclidean] : F ⊧ Axioms.Five (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨1, 1, 0, 1⟩)

lemma isGeachConvergent_of_valid_axiomGeach (h : F ⊧ Axioms.Geach g (.atom a)) : F.IsGeachConvergent g := by
  constructor;
  intro X x hx;
  have : x ∈ F.dia^[g.i] (F.box^[g.m] X) → x ∈ F.box^[g.j] (F.dia^[g.n] X) := by
    simpa [Semantics.Realize, Satisfies] using Satisfies.def_imp.mp $ @h (λ _ => X) x;
  apply this;
  apply hx;

lemma isReflexive_of_valid_axiomT (h : F ⊧ Axioms.T (.atom a)) : F.IsReflexive := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 0, 1, 0⟩) h;
  infer_instance;

lemma isTransitive_of_valid_axiomFour (h : F ⊧ Axioms.Four (.atom a)) : F.IsTransitive := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 2, 1, 0⟩) h;
  infer_instance;

lemma isSerial_of_valid_axiomD (h : F ⊧ Axioms.D (.atom a)) : F.IsSerial := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 0, 1, 1⟩) h;
  infer_instance;

lemma isSymmetric_of_valid_axiomB (h : F ⊧ Axioms.B (.atom a)) : F.IsSymmetric := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨0, 1, 0, 1⟩) h;
  infer_instance;

lemma isEuclidean_of_valid_axiomFive (h : F ⊧ Axioms.Five (.atom a)) : F.IsEuclidean := by
  have := isGeachConvergent_of_valid_axiomGeach (g := ⟨1, 1, 0, 1⟩) h;
  infer_instance;

end



section

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.E 𝓢] [Entailment.Consistent 𝓢]

open LO.Entailment Modal.Entailment
open MaximalConsistentSet

namespace Canonicity

variable {𝓒 : Canonicity 𝓢}

protected instance isGeachean (g) [Entailment.HasAxiomGeach g 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.dia^[g.i] (𝓒.box^[g.m] X) ⊆ 𝓒.box^[g.j] (𝓒.dia^[g.n] X))
  : 𝓒.toModel.IsGeachConvergent g := by
  constructor;
  rintro X A hX;
  by_cases X_np : Proofset.IsNonproofset X;
  . apply h <;> assumption;
  . obtain ⟨φ, rfl⟩ := iff_not_isNonProofset_exists.mp X_np; clear X_np;
    replace hX : A ∈ proofset 𝓢 (◇^[g.i](□^[g.m]φ)) := by simpa using hX;
    suffices A ∈ proofset 𝓢 (□^[g.j](◇^[g.n]φ)) by simpa;
    apply MaximalConsistentSet.mdp_provable ?_ hX;
    simp;

instance isReflexive [Entailment.HasAxiomT 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.box X ⊆ X) : 𝓒.toModel.IsReflexive := by
  have := Canonicity.isGeachean ⟨0, 0, 1, 0⟩ h;
  infer_instance

instance isTransitive [Entailment.HasAxiomFour 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.box X ⊆ 𝓒.box^[2] X) : 𝓒.toModel.IsTransitive := by
  have := Canonicity.isGeachean ⟨0, 2, 1, 0⟩ h;
  infer_instance

instance isSerial [Entailment.HasAxiomD 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.box X ⊆ 𝓒.dia X) : 𝓒.toModel.IsSerial := by
  have := Canonicity.isGeachean ⟨0, 0, 1, 1⟩ h;
  infer_instance

instance isEuclidean [Entailment.HasAxiomFive 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.dia X ⊆ 𝓒.box (𝓒.dia X)) : 𝓒.toModel.IsEuclidean := by
  have := Canonicity.isGeachean ⟨1, 1, 0, 1⟩ h;
  infer_instance

instance isSymmetric [Entailment.HasAxiomB 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → X ⊆ 𝓒.box (𝓒.dia X)) : 𝓒.toModel.IsSymmetric := by
  have := Canonicity.isGeachean ⟨0, 1, 0, 1⟩ h;
  infer_instance

instance isSymmetric' [Entailment.HasAxiomGeach ⟨1, 0, 1, 0⟩ 𝓢]
  (h : ∀ X : Proofset 𝓢, X.IsNonproofset → 𝓒.dia (𝓒.box X) ⊆ X) : 𝓒.toModel.IsSymmetric := by
  apply Frame.IsSymmetric.of_dual;
  apply Canonicity.isGeachean ⟨1, 0, 1, 0⟩ h |>.gconv;

end Canonicity



instance [Entailment.HasAxiomT 𝓢] : (minimalCanonicity 𝓢).toModel.IsReflexive := by
  apply Canonicity.isReflexive;
  intro X hX A hA;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hA;
  apply proofset.imp_subset.mp (by simp) hφ;

instance [Entailment.HasAxiomFour 𝓢] : (minimalCanonicity 𝓢).toModel.IsTransitive := by
  apply Canonicity.isTransitive;
  intro X hX A hA;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hA;
  simp only [Canonicity.multibox_proofset];
  apply proofset.imp_subset.mp (by simp) hφ;

instance [Entailment.HasAxiomD 𝓢] : (minimalCanonicity 𝓢).toModel.IsSerial := by
  apply Canonicity.isSerial;
  intro X hX A hA;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hA;
  simp only [Canonicity.dia_proofset];
  apply proofset.imp_subset.mp (by simp) hφ;



def relativeMinimalCanonicity (𝓢 : S) [Entailment.E 𝓢] (P : MaximalConsistentSet 𝓢 → Set (Proofset 𝓢)) : Canonicity 𝓢 where
  𝒩 A (X : Proofset 𝓢) := (minimalCanonicity 𝓢 |>.𝒩 A X) ∨ (X.IsNonproofset ∧ X ∈ P A);
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      left;
      use φ;
    . rintro (⟨ψ, hψ₁, hψ₂⟩ | h);
      . have := proofset.eq_boxed_of_eq hψ₂;
        grind;
      . simpa using h.1 φ;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

namespace relativeMinimalCanonicity

variable {P} {X : Proofset 𝓢} {A : (relativeMinimalCanonicity 𝓢 P).toModel.World}

protected lemma iff_mem_box :
  (A ∈ (relativeMinimalCanonicity 𝓢 P).box X) ↔
  ((A ∈ (minimalCanonicity 𝓢).box X) ∨ (X.IsNonproofset ∧ X ∈ P A)) := by
  constructor;
  . rintro (h | h);
    . left; exact h;
    . right; exact h;
  . rintro (h | ⟨h₁, h₂⟩);
    . left; exact h;
    . right;
      constructor;
      . assumption;
      . assumption;

protected lemma iff_mem_dia :
  (A ∈ (relativeMinimalCanonicity 𝓢 P).dia X) ↔
  ((A ∉ (minimalCanonicity 𝓢).box Xᶜ) ∧ ((∃ φ, Xᶜ = proofset 𝓢 φ) ∨ Xᶜ ∉ P A)) := by
  suffices A ∉ ((relativeMinimalCanonicity 𝓢 P).box Xᶜ) ↔ A ∉ (minimalCanonicity 𝓢).box Xᶜ ∧ ((∃ φ, Xᶜ = proofset 𝓢 φ) ∨ Xᶜ ∉ P A) by
    simpa [Frame.dia];
  rw [relativeMinimalCanonicity.iff_mem_box.not, Proofset.IsNonproofset]
  set_option push_neg.use_distrib true in push_neg;
  tauto;

protected instance isSerial [Entailment.HasAxiomD 𝓢]
  (hP : ∀ X : Proofset 𝓢, X.IsNonproofset → ∀ A, X ∈ P A → A ∈ (relativeMinimalCanonicity 𝓢 P).dia X)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsSerial := by
  apply Canonicity.isSerial;
  intro X hX A hA;
  apply hP;
  . assumption;
  . rcases hA with (h | ⟨_, h⟩);
    . exfalso; exact minimalCanonicity.not_isNonproofset_of_mem_box h $ hX;
    . assumption;

protected instance isReflexive [Entailment.HasAxiomT 𝓢]
  (hP : ∀ X : Proofset 𝓢, X.IsNonproofset → ∀ A, X ∈ P A → A ∈ X)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsReflexive := by
  apply Canonicity.isReflexive;
  intro X hX A hA;
  apply hP;
  . assumption;
  . rcases hA with (h | ⟨_, h⟩);
    . exfalso; exact minimalCanonicity.not_isNonproofset_of_mem_box h $ hX;
    . assumption;

protected instance isTransitive [Entailment.HasAxiomFour 𝓢]
  (hP : ∀ X : Proofset 𝓢, X.IsNonproofset → ∀ A, X ∈ P A → A ∈ (relativeMinimalCanonicity 𝓢 P).box^[2] X)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsTransitive := by
  apply Canonicity.isTransitive;
  intro X hX A hA;
  apply hP;
  . assumption;
  . rcases hA with (h | ⟨_, h⟩);
    . exfalso; exact minimalCanonicity.not_isNonproofset_of_mem_box h $ hX;
    . assumption;

protected instance isEuclidean [Entailment.HasAxiomFive 𝓢]
  (hP : ∀ X : Proofset 𝓢, X.IsNonproofset → ∀ A, Xᶜ ∉ P A → A ∈ (relativeMinimalCanonicity 𝓢 P).box ((relativeMinimalCanonicity 𝓢 P).dia X))
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsEuclidean := by
  apply Canonicity.isEuclidean;
  intro X hX A hA;
  apply hP;
  . assumption;
  . rcases relativeMinimalCanonicity.iff_mem_dia.mp hA with ⟨hA₁, (⟨φ, hφ⟩ | hA₂)⟩
    . exfalso;
      apply hX (∼φ);
      grind;
    . assumption;

/-
protected instance isSymmetric [Entailment.HasAxiomGeach ⟨1, 0, 1, 0⟩ 𝓢]
  (hP₁ : ∀ X : Proofset 𝓢, X.IsNonproofset → ∀ A, ((relativeMinimalCanonicity 𝓢 P).box X)ᶜ ∉ P A → A ∈ X)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsSymmetric := by
  apply Canonicity.isSymmetric';
  intro X hX A hA;
  apply hP₁;
  . assumption;
  . rcases relativeMinimalCanonicity.iff_mem_dia.mp hA with ⟨hA, (⟨φ, hφ⟩ | hA)⟩
    . rw [hφ] at hA;
      sorry;
    . assumption;
-/

end relativeMinimalCanonicity


/-- contains no non-proofset -/
abbrev minimalRelativeMaximalCanonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 := relativeMinimalCanonicity 𝓢 (λ _ _ => False)

namespace minimalRelativeMaximalCanonicity

protected instance isSerial [Entailment.HasAxiomD 𝓢] : (minimalRelativeMaximalCanonicity 𝓢).toModel.IsSerial := relativeMinimalCanonicity.isSerial $ by tauto;

protected instance isReflexive [Entailment.HasAxiomT 𝓢] : (minimalRelativeMaximalCanonicity 𝓢).toModel.IsReflexive := relativeMinimalCanonicity.isReflexive $ by tauto;

protected instance isTransitive [Entailment.HasAxiomFour 𝓢] : (minimalRelativeMaximalCanonicity 𝓢).toModel.IsTransitive := relativeMinimalCanonicity.isTransitive $ by tauto;

end minimalRelativeMaximalCanonicity


/-- contains all non-proofsets -/
abbrev maximalRelativeMaximalCanonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 := relativeMinimalCanonicity 𝓢 (λ _ _ => True)


namespace maximalRelativeMaximalCanonicity

protected instance IsEuclidean [Entailment.HasAxiomFive 𝓢] : (maximalRelativeMaximalCanonicity 𝓢).toModel.IsEuclidean := relativeMinimalCanonicity.isEuclidean $ by tauto;

end maximalRelativeMaximalCanonicity


end

end LO.Modal.Neighborhood
