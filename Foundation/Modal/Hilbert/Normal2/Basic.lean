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

inductive Hilbert.Normal {α} (Ax : Set (Formula α)) : Logic α
| axm {φ}       : φ ∈ Ax → Normal Ax φ
| mdp {φ ψ}     : Normal Ax (φ ➝ ψ) → Normal Ax φ → Normal Ax ψ
| nec {φ}       : Normal Ax φ → Normal Ax (□φ)
| implyK φ ψ    : Normal Ax $ Axioms.ImplyK φ ψ
| implyS φ ψ χ  : Normal Ax $ Axioms.ImplyS φ ψ χ
| ec φ ψ        : Normal Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.Normal

variable {Ax Ax₁ Ax₂ : Axiom α}

instance : Entailment.Łukasiewicz (Hilbert.Normal Ax) where
  implyK {_ _} := by constructor; apply Hilbert.Normal.implyK;
  implyS {_ _ _} := by constructor; apply Hilbert.Normal.implyS;
  elimContra {_ _} := by constructor; apply Hilbert.Normal.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Normal.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.Normal Ax) where
  nec h := by constructor; apply Hilbert.Normal.nec; exact h.1;

lemma axm' {φ} : φ ∈ Ax → Hilbert.Normal Ax ⊢ φ := fun h ↦ ⟨⟨axm h⟩⟩

protected lemma rec!
  {motive   : (φ : Formula α) → (Normal Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α}, (h : φ ∈ Ax) → motive φ (axm' h))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Normal Ax) ⊢ φ ➝ ψ} → {hφ : (Normal Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Normal Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : Normal Ax ⊢ φ) → motive φ d := by
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


end Hilbert.Normal


section

open Hilbert.Normal

protected abbrev K (α) : Logic α := Hilbert.Normal { Axioms.K φ ψ | (φ : Formula α) (ψ : Formula α) }

end

end LO.Modal

end
