import Foundation.Modal.Neighborhood.Completeness

namespace LO.Modal.Neighborhood

open Formula (atom)
open Formula.Neighborhood


variable {F : Frame} {X Y : Set F.World} {g : Axioms.Geach.Taple}

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

lemma IsSymmetric.of_alt {F : Frame} (h : ∀ a X, a ∈ X → { b | Xᶜ ∉ F.𝒩 b } ∈ F.𝒩 a) : F.IsSymmetric := by
  constructor;
  intro X a ha;
  have := h a;
  simp_all [Frame.dia, Frame.box];
  grind;


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

lemma IsEuclidean.of_alt {F : Frame} (h : ∀ a X, X ∉ F.𝒩 a → { b | X ∉ F.𝒩 b } ∈ F.𝒩 a) : F.IsEuclidean := by
  constructor;
  intro X a ha;
  have := h a;
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

instance [Entailment.HasAxiomT 𝓢] : (minimalCanonicity 𝓢).toModel.IsReflexive := by
  constructor;
  intro X Γ hΓ;
  obtain ⟨φ, rfl, _, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hΓ;
  apply proofset.imp_subset.mp (by simp) hφ;

instance [Entailment.HasAxiomFour 𝓢] : (minimalCanonicity 𝓢).toModel.IsTransitive := by
  constructor;
  intro X Γ hΓ;
  obtain ⟨φ, rfl, _, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hΓ;
  simp only [Canonicity.multibox_proofset];
  apply proofset.imp_subset.mp (by simp) hφ;

instance [Entailment.HasAxiomD 𝓢] : (minimalCanonicity 𝓢).toModel.IsSerial := by
  constructor;
  intro X Γ hΓ;
  obtain ⟨φ, rfl, _, hφ⟩ := minimalCanonicity.iff_mem_box_exists_fml.mp hΓ;
  simp only [Canonicity.dia_proofset];
  apply proofset.imp_subset.mp (by simp) hφ;


instance Canonicity.isEuclidean {𝓒 : Canonicity 𝓢} [Entailment.HasAxiomFive 𝓢]
  (h : ∀ A X, (∀ φ, X ≠ proofset 𝓢 φ) → { B | X ∉ 𝓒.𝒩 B } ∈ 𝓒.𝒩 A)
  : 𝓒.toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hA : ∀ φ, X ≠ proofset 𝓢 φ;
  . apply h;
    assumption;
  . push_neg at hA;
    obtain ⟨φ, rfl⟩ := hA;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ 𝓒.toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ 𝓒.𝒩 A := 𝓒.def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←𝓒.dia_proofset, Canonicity.toModel];


def relativeMinimalCanonicity (𝓢 : S) [Entailment.E 𝓢] (P : MaximalConsistentSet 𝓢 → Set (Proofset 𝓢)) : Canonicity 𝓢 where
  𝒩 A := (minimalCanonicity 𝓢 |>.𝒩 A) ∪ ({ X | (∀ φ, X ≠ proofset 𝓢 φ) ∧ (X ∈ P A) });
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

omit [Entailment.Consistent 𝓢] in
lemma relativeMinimalCanonicity.mem_nonproofset {P A X} (hX : ∀ φ, X ≠ proofset 𝓢 φ) (hP : X ∈ P A) : X ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A := by
  right;
  constructor;
  . assumption;
  . assumption;

instance relativeMinimalCanonicity.isEuclidean [Entailment.HasAxiomFive 𝓢] {P}
  (hP : ∀ X A, { B | X ∉ (relativeMinimalCanonicity 𝓢 P).𝒩 B} ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A)
  : (relativeMinimalCanonicity 𝓢 P).toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hX_np : ∀ φ, X ≠ proofset 𝓢 φ;
  . apply hP;
  . push_neg at hX_np;
    obtain ⟨φ, rfl⟩ := hX_np;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ (relativeMinimalCanonicity 𝓢 P).toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ (relativeMinimalCanonicity 𝓢 P).𝒩 A := (relativeMinimalCanonicity 𝓢 P).def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←(relativeMinimalCanonicity 𝓢 P).dia_proofset, Canonicity.toModel];



def maximalCanonicity (𝓢 : S) [Entailment.E 𝓢] : Canonicity 𝓢 where
  𝒩 A := (minimalCanonicity 𝓢 |>.𝒩 A) ∪ ({ X | ∀ φ, X ≠ proofset 𝓢 φ})
  def_𝒩 := by
    intro X φ;
    constructor;
    . intro h;
      left;
      use φ;
    . rintro (⟨ψ, hψ₁, hψ₂⟩ | h);
      . have := proofset.eq_boxed_of_eq hψ₂;
        grind;
      . grind;
  V a := proofset 𝓢 (.atom a);
  def_V := by simp;

instance maximalCanonicity.isEuclidean [Entailment.HasAxiomFive 𝓢]
  : (maximalCanonicity 𝓢).toModel.IsEuclidean := by
  apply Frame.IsEuclidean.of_alt;
  rintro A X hX;
  by_cases hA : ∀ φ, X ≠ proofset 𝓢 φ;
  . replace ⟨_, ⟨ψ, hψ⟩⟩ : X ∉ (minimalCanonicity 𝓢).𝒩 A ∧ ∃ x, X = proofset 𝓢 x := by
      simpa [maximalCanonicity, Canonicity.toModel] using hX;
    grind;
  . push_neg at hA;
    obtain ⟨φ, rfl⟩ := hA;
    suffices proofset 𝓢 (◇(∼φ)) = {b | proofset 𝓢 φ ∉ (maximalCanonicity 𝓢).toModel.𝒩 b} by
      have H : proofset 𝓢 (◇(∼φ)) ∈ (maximalCanonicity 𝓢).𝒩 A := (maximalCanonicity 𝓢).def_𝒩 _ _ |>.mp
        $ MaximalConsistentSet.mdp_provable (show 𝓢 ⊢ ∼□φ ➝ □◇(∼φ) by exact C!_trans (by simp) Entailment.axiomFive!)
        $ MaximalConsistentSet.iff_mem_neg.mpr
        $ by apply Canonicity.iff_box.not.mpr; simpa [Canonicity.toModel];
      rwa [this] at H;
    ext _;
    simp [←(maximalCanonicity 𝓢).dia_proofset, Canonicity.toModel];

end



section

end

end LO.Modal.Neighborhood
