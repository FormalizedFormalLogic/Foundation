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
@[simp] lemma valid_axiomFour_of_isTransitive [F.IsTransitive] : F ⊧ Axioms.Four (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 2, 1, 0⟩)
@[simp] lemma valid_axiomD_of_isSerial [F.IsSerial] : F ⊧ Axioms.D (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 0, 1, 1⟩)


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

end



section

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

open Entailment
open MaximalConsistentSet

instance [Entailment.ET 𝓢] : (minimalCanonicalFrame 𝓢).IsReflexive := by
  constructor;
  intro X Γ hΓ;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicalFrame.exists_box X Γ hΓ;
  have : proofset 𝓢 (□φ) ⊆ proofset 𝓢 φ := proofset.imp_subset.mp (by simp);
  exact Frame.IsCanonical.iff_mem (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) |>.mp $ this (hφ ▸ hΓ);

instance [Entailment.E4 𝓢] : (minimalCanonicalFrame 𝓢).IsTransitive := by
  constructor;
  intro X Γ hΓ;
  obtain ⟨φ, rfl, hφ⟩ := minimalCanonicalFrame.exists_box X Γ hΓ;
  have : proofset 𝓢 (□φ) ⊆ proofset 𝓢 (□□φ) := proofset.imp_subset.mp (by simp);
  have := Frame.IsCanonical.iff_mem (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) |>.mp $ this (hφ ▸ hΓ);
  rw [
    ←(Frame.IsCanonical.box_proofset (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) (□φ)),
    ←(Frame.IsCanonical.box_proofset (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) φ)
  ] at this;
  exact Frame.IsCanonical.iff_mem (F := minimalCanonicalFrame 𝓢) (𝓢 := 𝓢) |>.mpr this;

end


end LO.Modal.Neighborhood
