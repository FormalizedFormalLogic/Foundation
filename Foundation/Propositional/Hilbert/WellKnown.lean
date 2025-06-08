import Foundation.Propositional.Hilbert.Basic
import Foundation.Propositional.Entailment.Basic

namespace LO.Propositional

namespace Hilbert

variable {H : Hilbert α}

open Deduction

section

class HasEFQ (H : Hilbert α) where
  p : α
  mem_efq : (⊥ ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hEfq : H.HasEFQ] : Entailment.HasAxiomEFQ H where
  efq φ := by
    apply maxm;
    use Axioms.EFQ (Formula.atom hEfq.p);
    constructor;
    . exact hEfq.mem_efq;
    . use (λ b => if hEfq.p = b then φ else (.atom b));
      simp;
instance [DecidableEq α] [H.HasEFQ] : Entailment.Int H where


class HasLEM (H : Hilbert α) where
  p : α
  mem_lem : (.atom p ⋎ ∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hLEM : H.HasLEM] : Entailment.HasAxiomLEM H where
  lem φ := by
    apply maxm;
    use Axioms.LEM (.atom hLEM.p);
    constructor;
    . exact hLEM.mem_lem;
    . use (λ b => if hLEM.p = b then φ else (.atom b));
      simp;


class HasDNE (H : Hilbert α) where
  p : α
  mem_dne : (∼∼(.atom p) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hDNE : H.HasDNE] : Entailment.HasAxiomDNE H where
  dne φ := by
    apply maxm;
    use Axioms.DNE (.atom hDNE.p);
    constructor;
    . exact hDNE.mem_dne;
    . use (λ b => if hDNE.p = b then φ else (.atom b));
      simp;


class HasWeakLEM (H : Hilbert α) where
  p : α
  mem_wlem : (∼(.atom p) ⋎ ∼∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hWLEM : H.HasWeakLEM] : Entailment.HasAxiomWeakLEM H where
  wlem φ := by
    apply maxm;
    use Axioms.WeakLEM (.atom hWLEM.p);
    constructor;
    . exact hWLEM.mem_wlem;
    . use (λ b => if hWLEM.p = b then φ else (.atom b));
      simp;


class HasDummett (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by tauto;
  mem_dummet : ((.atom p) ➝ (.atom q)) ⋎ ((.atom q) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hDummett : H.HasDummett] : Entailment.HasAxiomDummett H where
  dummett φ ψ := by
    apply maxm;
    use Axioms.Dummett (.atom hDummett.p) (.atom hDummett.q);
    constructor;
    . exact hDummett.mem_dummet;
    . use (λ b =>
        if hDummett.p = b then φ
        else if hDummett.q = b then ψ
        else (.atom b)
      );
      simp [hDummett.ne_pq];

class HasKrieselPutnam (H : Hilbert α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by tauto;
  ne_pr : p ≠ r := by tauto;
  ne_qr : q ≠ r := by tauto;
  mem_kp : Axioms.KrieselPutnam (.atom p) (.atom q) (.atom r) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hKrieselPutnam : H.HasKrieselPutnam] : Entailment.HasAxiomKrieselPutnam H where
  krieselputnam φ ψ χ := by
    apply maxm;
    use Axioms.KrieselPutnam (.atom hKrieselPutnam.p) (.atom hKrieselPutnam.q) (.atom hKrieselPutnam.r);
    constructor;
    . exact hKrieselPutnam.mem_kp;
    . use (λ b =>
        if hKrieselPutnam.p = b then φ
        else if hKrieselPutnam.q = b then ψ
        else if hKrieselPutnam.r = b then χ
        else (.atom b)
      );
      simp [hKrieselPutnam.ne_pq, hKrieselPutnam.ne_pr, hKrieselPutnam.ne_qr];


end

end Hilbert


protected abbrev Hilbert.Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩
protected abbrev Logic.Int : Logic := Hilbert.Int.logic

namespace Hilbert.Int

instance : Hilbert.Int.FiniteAxiomatizable where
instance : Hilbert.Int.HasEFQ where p := 0;

end Hilbert.Int


protected abbrev Hilbert.Cl : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}⟩
protected abbrev Logic.Cl : Logic := Hilbert.Cl.logic

namespace Hilbert

instance : Hilbert.Cl.FiniteAxiomatizable where
instance : Hilbert.Cl.HasEFQ where p := 0;
instance : Hilbert.Cl.HasLEM where p := 0;
instance : Entailment.Cl (Hilbert.Cl) where

end Hilbert

lemma Hilbert.Int_weakerThan_Cl : (Hilbert.Int) ⪯ (Hilbert.Cl) := by
  apply weakerThan_of_subset_axioms;
  tauto;


protected abbrev Hilbert.KC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}⟩
protected abbrev Logic.KC : Logic := Hilbert.KC.logic

namespace Hilbert.KC

instance : Hilbert.KC.FiniteAxiomatizable where
instance : Hilbert.KC.HasEFQ where p := 0;
instance : Hilbert.KC.HasWeakLEM where p := 0;
instance : Entailment.KC (Hilbert.KC) where

end Hilbert.KC


protected abbrev Hilbert.LC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}⟩
protected abbrev Logic.LC : Logic := Hilbert.LC.logic

namespace Hilbert.LC

instance : Hilbert.LC.FiniteAxiomatizable where
instance : Hilbert.LC.HasEFQ where p := 0;
instance : Hilbert.LC.HasDummett where p := 0; q := 1;
instance : Entailment.LC (Hilbert.LC) where

end Hilbert.LC


protected abbrev Hilbert.KP : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)}⟩
protected abbrev Logic.KP : Logic := Hilbert.KP.logic

namespace Hilbert.KP

instance : Hilbert.KP.FiniteAxiomatizable where
instance : Hilbert.KP.HasEFQ where p := 0;
instance : Hilbert.KP.HasKrieselPutnam where p := 0; q := 1; r := 2;
instance : Entailment.KP (Hilbert.KP) where

end Hilbert.KP


end LO.Propositional
