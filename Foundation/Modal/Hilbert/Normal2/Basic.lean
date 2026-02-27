module

public import Foundation.Modal.Entailment.GL
public import Foundation.Modal.Entailment.Grz
public import Foundation.Modal.Entailment.K4Hen
public import Foundation.Modal.Entailment.K4Henkin
public import Foundation.Modal.Entailment.S5Grz
public import Foundation.Modal.Hilbert.Axiom
public import Foundation.Modal.Logic.Basic
public import Foundation.Modal.Logic.Basic
public import Foundation.Propositional.Entailment.Cl.Łukasiewicz

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.Normal2 {α} (Ax : Set (Formula α)) : Logic α
| axm {φ}       : φ ∈ Ax → Normal2 Ax φ
| mdp {φ ψ}     : Normal2 Ax (φ ➝ ψ) → Normal2 Ax φ → Normal2 Ax ψ
| nec {φ}       : Normal2 Ax φ → Normal2 Ax (□φ)
| implyK φ ψ    : Normal2 Ax $ Axioms.ImplyK φ ψ
| implyS φ ψ χ  : Normal2 Ax $ Axioms.ImplyS φ ψ χ
| ec φ ψ        : Normal2 Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.Normal2

variable {Ax Ax₁ Ax₂ : Axiom α}

instance : Entailment.Łukasiewicz (Hilbert.Normal2 Ax) where
  implyK {_ _} := by constructor; apply Hilbert.Normal2.implyK;
  implyS {_ _ _} := by constructor; apply Hilbert.Normal2.implyS;
  elimContra {_ _} := by constructor; apply Hilbert.Normal2.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Normal2.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.Normal2 Ax) where
  nec h := by constructor; apply Hilbert.Normal2.nec; exact h.1;

lemma axm' {φ} : φ ∈ Ax → Hilbert.Normal2 Ax ⊢ φ := fun h ↦ ⟨⟨axm h⟩⟩

protected lemma rec!
  {motive   : (φ : Formula α) → (Normal2 Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α}, (h : φ ∈ Ax) → motive φ (axm' h))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Normal2 Ax) ⊢ φ ➝ ψ} → {hφ : (Normal2 Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Normal2 Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : Normal2 Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm h => apply axm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | implyK φ ψ => apply implyK;
  | implyS φ ψ χ => apply implyS;
  | ec φ ψ => apply ec;

open Axiom


end Hilbert.Normal2


section

open Hilbert.Normal2

protected abbrev K' (α) : Logic α := Hilbert.Normal2 { Axioms.K φ ψ | (φ : Formula α) (ψ : Formula α) }
instance : Entailment.K (Modal.K' α) where
  K φ ψ := by constructor; apply Hilbert.Normal2.axm; simp;

protected abbrev KT' (α) : Logic α := Hilbert.Normal2 (
  { Axioms.K φ ψ | (φ : Formula α) (ψ : Formula α) } ∪
  { Axioms.T φ   | (φ : Formula α) }
)
instance : Entailment.KT (Modal.KT' α) where
  K φ ψ := by constructor; apply Hilbert.Normal2.axm; simp;
  T φ   := by constructor; apply Hilbert.Normal2.axm; simp;

end

end LO.Modal

end
