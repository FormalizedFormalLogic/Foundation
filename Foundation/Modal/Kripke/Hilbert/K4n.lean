import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Relation.Iterate

namespace LO.Axioms.Modal

variable {F : Type*} [BasicModalLogicalConnective F]

protected abbrev FourN (n : ℕ+) (φ : F) := □^[n]φ ➝ □^[(n + 1)]φ

lemma eq_FourN_Geach {φ : F} : (Axioms.Modal.FourN n) φ = (Axioms.Geach ⟨0, n + 1, n, 0⟩ φ) := by rfl

end LO.Axioms.Modal


section

variable {n : ℕ+}  {α : Type u} {rel : α → α → Prop}

def WeakTransitive (n : ℕ+) (rel : α → α → Prop) := ∀ x y, (Rel.iterate rel (n + 1)) x y → (Rel.iterate rel n) x y

@[simp]
lemma weak_transitive_one_transitive : (WeakTransitive 1 rel) ↔ Transitive rel := by
  simp only [WeakTransitive, PNat.val_ofNat, Nat.reduceAdd, Rel.iterate.iff_succ, Rel.iterate.iff_zero, exists_eq_right, forall_exists_index, and_imp, Transitive];
  constructor;
  . intro h x y z; apply h;
  . intro h x y z; apply h;

class IsWeakTrans (n) (α) (rel : α → α → Prop) : Prop where
  weakTrans : WeakTransitive n rel

instance [IsWeakTrans n _ rel] : IsGeachean ⟨0, n + 1, n, 0⟩ _ rel := ⟨by
  simp only [Rel.iterate.iff_zero, Rel.iterate.iff_succ, exists_eq_right', and_imp, forall_exists_index];
  rintro x _ y rfl u Rxw Rwz;
  apply IsWeakTrans.weakTrans;
  use u;
⟩

instance [IsGeachean ⟨0, n + 1, n, 0⟩ _ rel] : IsWeakTrans n _ rel := ⟨by
  rintro x y ⟨u, Rxu, Ruy⟩;
  have : ∀ u, rel x u → Rel.iterate rel (↑n) u y → Rel.iterate rel (↑n) x y := by
    simpa using @IsGeachean.geachean (g := ⟨0, n + 1, n, 0⟩) (R := rel) _ _ x x y;
  apply this u Rxu Ruy;
⟩

end


namespace LO.Entailment.Modal

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}

class HasAxiomFourN (n) (𝓢 : S) where
  FourN (φ : F) : 𝓢 ⊢ Axioms.Modal.FourN n φ

section

variable [HasAxiomFourN n 𝓢]

def axiomFourN : 𝓢 ⊢ □^[n]φ ➝ □^[(n + 1)]φ := by apply HasAxiomFourN.FourN
@[simp] lemma axiomFourN! : 𝓢 ⊢!  □^[n]φ ➝ □^[(n + 1)]φ := ⟨axiomFourN⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFourN n Γ := ⟨fun _ ↦ FiniteContext.of axiomFourN⟩
instance (Γ : Context F 𝓢) : HasAxiomFourN n Γ := ⟨fun _ ↦ Context.of axiomFourN⟩

instance : HasAxiomGeach ⟨0, n + 1, n, 0⟩ 𝓢 := ⟨fun _ ↦ axiomFourN⟩

end


end LO.Entailment.Modal



namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Hilbert

variable {α} [DecidableEq α] {H : Hilbert α} {n : ℕ+}

open Deduction

/-
class HasFourN (n : ℕ+) (H : Hilbert α) where
  p : α
  mem_FourN : Axioms.Modal.FourN n (.atom p) ∈ H.axioms := by tauto;

open Classical in
instance [hFourN : Hilbert.HasFourN n H] : Entailment.Modal.HasAxiomFourN n H where
  FourN φ := by
    apply maxm;
    use Axioms.Modal.FourN n (.atom hFourN.p);
    constructor;
    . exact hFourN.mem_FourN;
    . use (λ b => if hFourN.p = b then φ else (.atom b));
      simp;
-/

protected abbrev K4n (n : ℕ+) : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Modal.FourN n (.atom 0)}⟩
instance : (Hilbert.K4n n).HasK where p := 0; q := 1;
instance : Entailment.Modal.K (Hilbert.K4n n) where
instance : Entailment.Modal.HasAxiomFourN n (Hilbert.K4n n) where
  FourN φ := by
    apply maxm;
    use Axioms.Modal.FourN n (.atom 0);
    constructor;
    . simp;
    . use (λ b => if b = 0 then φ else (.atom b));
      simp;

end Hilbert



namespace Kripke

variable {n : ℕ+}

protected abbrev FrameClass.weak_trans (n : ℕ+) : FrameClass := { F | IsWeakTrans n _ F.Rel }

lemma validate_AxiomFourN_of_weak_transitive {F : Kripke.Frame} [IsWeakTrans n _ F.Rel] : F ⊧ (Axioms.Modal.FourN n (.atom 0)) := validate_AxiomGeach_of_Geachean (g := ⟨0, n + 1, n, 0⟩)

namespace Canonical

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance isWeakTrans [Entailment.Modal.HasAxiomFourN n 𝓢] : IsWeakTrans n _ (canonicalFrame 𝓢).Rel := by
  have : IsGeachean ⟨0, n + 1, n, 0⟩ _ (canonicalFrame 𝓢).Rel := isGeachean (g := ⟨0, n + 1, n, 0⟩) (𝓢 := 𝓢);
  infer_instance;

end Canonical

end Kripke


namespace Hilbert.K4n.Kripke

variable {n : ℕ+}

instance sound : Sound (Hilbert.K4n n) (Kripke.FrameClass.weak_trans n) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  apply @validate_AxiomFourN_of_weak_transitive n F F_trans;

instance consistent : Entailment.Consistent (Hilbert.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.weak_trans n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;> { simp [WeakTransitive]; tauto; }

instance canonical : Canonical (Hilbert.K4n n) (FrameClass.weak_trans n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K4n n) (FrameClass.weak_trans n) := inferInstance

end Hilbert.K4n.Kripke

end LO.Modal
