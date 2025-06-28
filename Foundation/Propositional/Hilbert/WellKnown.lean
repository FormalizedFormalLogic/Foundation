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

instance [DecidableEq α] [H.HasEFQ] : Entailment.HasAxiomEFQ H.logic where
  efq φ := by
    constructor;
    apply maxm;
    use Axioms.EFQ (Formula.atom (HasEFQ.p H));
    constructor;
    . exact HasEFQ.mem_efq;
    . use (λ b => if (HasEFQ.p H) = b then φ else (.atom b));
      simp;
instance [DecidableEq α] [H.HasEFQ] : Entailment.Int H.logic where


class HasLEM (H : Hilbert α) where
  p : α
  mem_lem : (.atom p ⋎ ∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasLEM] : Entailment.HasAxiomLEM H.logic where
  lem φ := by
    constructor;
    apply maxm;
    use Axioms.LEM (.atom (HasLEM.p H));
    constructor;
    . exact HasLEM.mem_lem;
    . use (λ b => if (HasLEM.p H) = b then φ else (.atom b));
      simp;


class HasDNE (H : Hilbert α) where
  p : α
  mem_dne : (∼∼(.atom p) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasDNE] : Entailment.HasAxiomDNE H.logic where
  dne φ := by
    constructor;
    apply maxm;
    use Axioms.DNE (.atom (HasDNE.p H));
    constructor;
    . exact HasDNE.mem_dne;
    . use (λ b => if (HasDNE.p H) = b then φ else (.atom b));
      simp;


class HasWeakLEM (H : Hilbert α) where
  p : α
  mem_wlem : (∼(.atom p) ⋎ ∼∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasWeakLEM] : Entailment.HasAxiomWeakLEM H.logic where
  wlem φ := by
    constructor;
    apply maxm;
    use Axioms.WeakLEM (.atom (HasWeakLEM.p H));
    constructor;
    . exact HasWeakLEM.mem_wlem;
    . use (λ b => if (HasWeakLEM.p H) = b then φ else (.atom b));
      simp;


class HasDummett (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by tauto;
  mem_dummet : ((.atom p) ➝ (.atom q)) ⋎ ((.atom q) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasDummett] : Entailment.HasAxiomDummett H.logic where
  dummett φ ψ := by
    constructor;
    apply maxm;
    use Axioms.Dummett (.atom (HasDummett.p H)) (.atom (HasDummett.q H));
    constructor;
    . exact HasDummett.mem_dummet;
    . use (λ b =>
        if (HasDummett.p H) = b then φ
        else if (HasDummett.q H) = b then ψ
        else (.atom b)
      );
      simp [HasDummett.ne_pq];

class HasKrieselPutnam (H : Hilbert α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by tauto;
  ne_pr : p ≠ r := by tauto;
  ne_qr : q ≠ r := by tauto;
  mem_kp : Axioms.KrieselPutnam (.atom p) (.atom q) (.atom r) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasKrieselPutnam] : Entailment.HasAxiomKrieselPutnam H.logic where
  krieselputnam φ ψ χ := by
    constructor;
    apply maxm;
    use Axioms.KrieselPutnam (.atom (HasKrieselPutnam.p H)) (.atom (HasKrieselPutnam.q H)) (.atom (HasKrieselPutnam.r H));
    constructor;
    . exact HasKrieselPutnam.mem_kp;
    . use (λ b =>
        if (HasKrieselPutnam.p H) = b then φ
        else if (HasKrieselPutnam.q H)= b then ψ
        else if (HasKrieselPutnam.r H) = b then χ
        else (.atom b)
      );
      simp [HasKrieselPutnam.ne_pq, HasKrieselPutnam.ne_pr, HasKrieselPutnam.ne_qr];


end

end Hilbert


protected abbrev Hilbert.Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩
protected abbrev Logic.Int := Hilbert.Int.logic
instance : Hilbert.Int.HasEFQ where p := 0;
instance : Entailment.Int (Logic.Int) where

protected abbrev Hilbert.Cl : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}⟩
protected abbrev Logic.Cl := Hilbert.Cl.logic
instance : Hilbert.Cl.HasEFQ where p := 0;
instance : Hilbert.Cl.HasLEM where p := 0;
instance : Entailment.Cl (Logic.Cl) where

lemma Hilbert.Int_weakerThan_Cl : (Logic.Int) ⪯ (Logic.Cl) := by apply weakerThan_of_subset_axioms; tauto;


protected abbrev Hilbert.KC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}⟩
protected abbrev Logic.KC := Hilbert.KC.logic
instance : Hilbert.KC.HasEFQ where p := 0;
instance : Hilbert.KC.HasWeakLEM where p := 0;
instance : Entailment.KC (Logic.KC) where


protected abbrev Hilbert.LC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}⟩
protected abbrev Logic.LC := Hilbert.LC.logic
instance : Hilbert.LC.HasEFQ where p := 0;
instance : Hilbert.LC.HasDummett where p := 0; q := 1;
instance : Entailment.LC (Logic.LC) where


protected abbrev Hilbert.KP : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)}⟩
protected abbrev Logic.KP := Hilbert.KP.logic
instance : Hilbert.KP.HasEFQ where p := 0;
instance : Hilbert.KP.HasKrieselPutnam where p := 0; q := 1; r := 2;
instance : Entailment.KP (Logic.KP) where


end LO.Propositional
