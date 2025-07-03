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

instance [DecidableEq α] [H.HasEFQ] : Entailment.HasAxiomEFQ H where
  efq φ := by
    simpa using Deduction.axm
      (φ := Axioms.EFQ (.atom (HasEFQ.p H)))
      (s := λ b => if (HasEFQ.p H) = b then φ else (.atom b))
      HasEFQ.mem_efq;
instance [DecidableEq α] [H.HasEFQ] : Entailment.Int H where


class HasLEM (H : Hilbert α) where
  p : α
  mem_lem : (.atom p ⋎ ∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasLEM] : Entailment.HasAxiomLEM H where
  lem φ := by
    simpa using Deduction.axm
      (φ := Axioms.LEM (.atom (HasLEM.p H)))
      (s := λ b => if (HasLEM.p H) = b then φ else (.atom b))
      HasLEM.mem_lem;


class HasDNE (H : Hilbert α) where
  p : α
  mem_dne : (∼∼(.atom p) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasDNE] : Entailment.HasAxiomDNE H where
  dne φ := by
    simpa using Deduction.axm
      (φ := Axioms.DNE (.atom (HasDNE.p H)))
      (s := λ b => if (HasDNE.p H) = b then φ else (.atom b))
      HasDNE.mem_dne;


class HasWeakLEM (H : Hilbert α) where
  p : α
  mem_wlem : (∼(.atom p) ⋎ ∼∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasWeakLEM] : Entailment.HasAxiomWeakLEM H where
  wlem φ := by
    simpa using Deduction.axm
      (φ := Axioms.WeakLEM (.atom (HasWeakLEM.p H)))
      (s := λ b => if (HasWeakLEM.p H) = b then φ else (.atom b))
      HasWeakLEM.mem_wlem;


class HasDummett (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by tauto;
  mem_dummet : ((.atom p) ➝ (.atom q)) ⋎ ((.atom q) ➝ (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasDummett] : Entailment.HasAxiomDummett H where
  dummett φ ψ := by
    simpa [HasDummett.ne_pq] using Deduction.axm
      (φ := Axioms.Dummett (.atom (HasDummett.p H)) (.atom (HasDummett.q H)))
      (s := λ b =>
        if (HasDummett.p H) = b then φ
        else if (HasDummett.q H) = b then ψ
        else (.atom b))
      HasDummett.mem_dummet;


class HasKrieselPutnam (H : Hilbert α) where
  p : α
  q : α
  r : α
  ne_pq : p ≠ q := by tauto;
  ne_qr : q ≠ r := by tauto;
  ne_rp : r ≠ p := by tauto;
  mem_kp : Axioms.KrieselPutnam (.atom p) (.atom q) (.atom r) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasKrieselPutnam] : Entailment.HasAxiomKrieselPutnam H where
  krieselputnam φ ψ χ := by
    simpa [HasKrieselPutnam.ne_pq, HasKrieselPutnam.ne_qr, HasKrieselPutnam.ne_rp, HasKrieselPutnam.ne_rp.symm] using Deduction.axm
      (φ := Axioms.KrieselPutnam (.atom (HasKrieselPutnam.p H)) (.atom (HasKrieselPutnam.q H)) (.atom (HasKrieselPutnam.r H)))
      (s := λ b =>
        if (HasKrieselPutnam.p H) = b then φ
        else if (HasKrieselPutnam.q H) = b then ψ
        else if (HasKrieselPutnam.r H) = b then χ
        else (.atom b))
      HasKrieselPutnam.mem_kp;


end

end Hilbert


protected abbrev Hilbert.Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩
protected abbrev Int := Hilbert.Int.logic
notation "𝐈𝐧𝐭" => Propositional.Int
instance : Hilbert.Int.HasEFQ where p := 0;
instance : Entailment.Int (Hilbert.Int) where

protected abbrev Hilbert.Cl : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}⟩
protected abbrev Cl := Hilbert.Cl.logic
notation "𝐂𝐥" => Propositional.Cl
instance : Hilbert.Cl.HasEFQ where p := 0;
instance : Hilbert.Cl.HasLEM where p := 0;
instance : Entailment.Cl (Hilbert.Cl) where

lemma Hilbert.Int_weakerThan_Cl : (Hilbert.Int) ⪯ (Hilbert.Cl) := by apply weakerThan_of_subset_axioms; tauto;


protected abbrev Hilbert.KC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}⟩
protected abbrev KC := Hilbert.KC.logic
notation "𝐊𝐂" => Propositional.KC
instance : Hilbert.KC.HasEFQ where p := 0;
instance : Hilbert.KC.HasWeakLEM where p := 0;
instance : Entailment.KC (Hilbert.KC) where


protected abbrev Hilbert.LC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}⟩
protected abbrev LC := Hilbert.LC.logic
notation "𝐋𝐂" => Propositional.LC
instance : Hilbert.LC.HasEFQ where p := 0;
instance : Hilbert.LC.HasDummett where p := 0; q := 1;
instance : Entailment.LC (Hilbert.LC) where


protected abbrev Hilbert.KrieselPutnam : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)}⟩
protected abbrev KrieselPutnam := Hilbert.KrieselPutnam.logic
notation "𝐊𝐏" => Propositional.KrieselPutnam
instance : Hilbert.KrieselPutnam.HasEFQ where p := 0;
instance : Hilbert.KrieselPutnam.HasKrieselPutnam where p := 0; q := 1; r := 2;
instance : Entailment.KrieselPutnam (Hilbert.KrieselPutnam) where

end LO.Propositional
