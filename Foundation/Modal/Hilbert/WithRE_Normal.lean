module

public import Foundation.Modal.Hilbert.WithRE.Basic
public import Foundation.Modal.Hilbert.Normal.Basic


@[expose] public section

namespace LO.Modal

open LO.Modal.Entailment

lemma equiv_WithRE_Normal_of_provable_axiomInstances
  {AxE AxN : Axiom ℕ}
  [Necessitation (Hilbert.WithRE AxE)] [RE (Hilbert.Normal AxN)]
  (hN : (Hilbert.Normal AxN) ⊢* AxE.instances)
  (hE : (Hilbert.WithRE AxE) ⊢* AxN.instances)
  : (Hilbert.WithRE AxE) ≊ (Hilbert.Normal AxN) := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro h;
    induction h using Modal.Hilbert.WithRE.rec! with
    | axm s h => apply hN; grind;
    | re h => apply re! h;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ
    | _ => simp;
  . intro h;
    induction h using Modal.Hilbert.Normal.rec! with
    | axm s h => apply hE; grind;
    | nec h => exact nec! h;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => simp;

instance : Modal.EMCN ≊ Modal.K := by
  apply equiv_WithRE_Normal_of_provable_axiomInstances;
  . rintro φ (⟨_, (rfl | rfl | rfl), ⟨_, rfl⟩⟩) <;> simp;
  . rintro φ (⟨_, rfl, ⟨_, rfl⟩⟩); simp;

instance : Modal.EMCNT ≊ Modal.KT := by
  apply equiv_WithRE_Normal_of_provable_axiomInstances;
  . rintro _ ⟨φ, (rfl | rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp;
  . rintro _ ⟨φ, (rfl | rfl), ⟨_, rfl⟩⟩ <;> simp;

instance : Modal.EMCNT4 ≊ Modal.S4 := by
  apply equiv_WithRE_Normal_of_provable_axiomInstances;
  . rintro _ ⟨φ, (rfl | rfl | rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp;
  . rintro _ ⟨φ, (rfl | rfl | rfl), ⟨_, rfl⟩⟩ <;> simp;

end LO.Modal
end
