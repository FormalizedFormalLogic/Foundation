import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula (atom)
open Formula.Neighborhood


variable {F : Frame} {X Y : Set F.World} {g : Axioms.Geach.Taple}

namespace Frame

class IsGeachConvergent (g : Axioms.Geach.Taple) (F : Frame) : Prop where
  gconv : ∀ X : Set F, 𝒟^[g.i] (ℬ^[g.m] X) ⊆ ℬ^[g.j] (𝒟^[g.n] X)

@[simp, grind]
lemma gconv [F.IsGeachConvergent g] : 𝒟^[g.i] (ℬ^[g.m] X) ⊆ ℬ^[g.j] (𝒟^[g.n] X) := IsGeachConvergent.gconv X


class IsReflexive (F : Frame) : Prop where
  refl : ∀ X : Set F, ℬ X ⊆ X

@[simp, grind] lemma refl [F.IsReflexive] : ℬ X ⊆ X := IsReflexive.refl X

instance [F.IsReflexive] : F.IsGeachConvergent ⟨0, 0, 1, 0⟩ := ⟨by simp⟩

instance [F.IsGeachConvergent ⟨0, 0, 1, 0⟩] : F.IsReflexive := ⟨λ _ => F.gconv (g := ⟨0, 0, 1, 0⟩)⟩


class IsTransitive (F : Frame) : Prop where
  trans : ∀ X : Set F, ℬ X ⊆ ℬ^[2] X

@[simp, grind] lemma trans [F.IsTransitive] : ℬ X ⊆ ℬ^[2] X := IsTransitive.trans X

instance [F.IsTransitive] : F.IsGeachConvergent ⟨0, 2, 1, 0⟩ := ⟨by simp⟩

instance [F.IsGeachConvergent ⟨0, 2, 1, 0⟩] : F.IsTransitive := ⟨λ _ => F.gconv (g := ⟨0, 2, 1, 0⟩)⟩


class IsSerial (F : Frame) : Prop where
  serial : ∀ X : Set F, ℬ X ⊆ 𝒟 X
@[simp] lemma serial [F.IsSerial] : ℬ X ⊆ 𝒟 X := IsSerial.serial X
instance [F.IsSerial] : F.IsGeachConvergent ⟨0, 0, 1, 1⟩ := ⟨by simp⟩
instance [F.IsGeachConvergent ⟨0, 0, 1, 1⟩] : F.IsSerial := ⟨λ _ => F.gconv (g := ⟨0, 0, 1, 1⟩)⟩

end Frame


section

variable {a : ℕ}

lemma valid_axiomGeach_of_isGeachConvergent [F.IsGeachConvergent g] : F ⊧ Axioms.Geach g (.atom a) := by
  intro V x;
  apply Satisfies.def_imp.mpr;
  suffices x ∈ 𝒟^[g.i] (ℬ^[g.m] (V a)) → x ∈ ℬ^[g.j] (𝒟^[g.n] (V a)) by simpa [Semantics.Realize, Satisfies];
  apply F.gconv;

@[simp] lemma valid_axiomT_of_isReflexive [F.IsReflexive] : F ⊧ Axioms.T (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 0, 1, 0⟩)
@[simp] lemma valid_axiomFour_of_isTransitive [F.IsTransitive] : F ⊧ Axioms.Four (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 2, 1, 0⟩)
@[simp] lemma valid_axiomD_of_isSerial [F.IsSerial] : F ⊧ Axioms.D (.atom a) := valid_axiomGeach_of_isGeachConvergent (g := ⟨0, 0, 1, 1⟩)


lemma isGeachConvergent_of_valid_axiomGeach (h : F ⊧ Axioms.Geach g (.atom a)) : F.IsGeachConvergent g := by
  constructor;
  intro X x hx;
  have : x ∈ 𝒟^[g.i] (ℬ^[g.m] X) → x ∈ ℬ^[g.j] (𝒟^[g.n] X) := by
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

end LO.Modal.Neighborhood
