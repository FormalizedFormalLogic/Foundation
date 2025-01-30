import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Formula

namespace LO.IntProp

variable {α : Type u}

structure Hilbert (α) where
  axioms : Set (Formula α)

class Hilbert.FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms

class Hilbert.HasEFQ (H : Hilbert α) where
  p : α
  mem_efq : (⊥ ➝ (.atom p)) ∈ H.axioms := by tauto;

class Hilbert.HasLEM (H : Hilbert α) where
  p : α
  mem_lem : (.atom p ⋎ ∼(.atom p)) ∈ H.axioms := by tauto;

class Hilbert.HasDNE (H : Hilbert α) where
  p : α
  mem_dne : (∼∼(.atom p) ➝ (.atom p)) ∈ H.axioms := by tauto;

class Hilbert.HasWeakLEM (H : Hilbert α) where
  p : α
  mem_wlem : (∼(.atom p) ⋎ ∼∼(.atom p)) ∈ H.axioms := by tauto;

class Hilbert.HasDummett (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q
  mem_dummet : ((.atom p) ➝ (.atom q)) ⋎ ((.atom q) ➝ (.atom p)) ∈ H.axioms := by tauto;

namespace Hilbert

variable {H : Hilbert α}

inductive Deduction (H : Hilbert α) : Formula α → Type _
  | eaxm {φ}      : φ ∈ H.axioms → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | subst {φ} (s) : Deduction H φ → Deduction H (φ⟦s⟧)
  | verum         : Deduction H $ ⊤
  | implyS φ ψ    : Deduction H $ φ ➝ ψ ➝ φ
  | implyK φ ψ χ  : Deduction H $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | andElimL φ ψ  : Deduction H $ φ ⋏ ψ ➝ φ
  | andElimR φ ψ  : Deduction H $ φ ⋏ ψ ➝ ψ
  | andIntro φ ψ  : Deduction H $ φ ➝ ψ ➝ φ ⋏ ψ
  | orIntroL φ ψ  : Deduction H $ φ ➝ φ ⋎ ψ
  | orIntroR φ ψ  : Deduction H $ ψ ➝ φ ⋎ ψ
  | orElim φ ψ χ  : Deduction H $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

open Deduction
open Hilbert

section

instance : System.ModusPonens H := ⟨mdp⟩

instance : System.HasAxiomImply₁ H := ⟨implyS⟩

instance : System.HasAxiomImply₂ H := ⟨implyK⟩

instance : System.HasAxiomAndInst H := ⟨andIntro⟩

instance : System.Minimal H where
  mdp := mdp
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  and₃ := andIntro
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

section

variable [DecidableEq α]

instance [efq : H.HasEFQ] : System.HasAxiomEFQ H where
  efq φ := by simpa using subst (s := λ b => if b = efq.p then φ else (.atom b)) $ eaxm efq.mem_efq;

instance [lem : H.HasLEM]  : System.HasAxiomLEM H where
  lem φ := by simpa using subst (s := λ b => if b = lem.p then φ else (.atom b)) $ eaxm lem.mem_lem;

instance [dne : H.HasDNE] : System.HasAxiomDNE H where
  dne φ := by simpa using subst (s := λ b => if b = dne.p then φ else (.atom b)) $ eaxm dne.mem_dne;

instance [wlem : H.HasWeakLEM] : System.HasAxiomWeakLEM H where
  wlem φ := by simpa using subst (s := λ b => if b = wlem.p then φ else (.atom b)) $ eaxm wlem.mem_wlem;

instance [dummet : H.HasDummett] : System.HasAxiomDummett H where
  dummett φ ψ := by
    simpa [dummet.ne_pq, bne_iff_ne, ne_eq] using
      subst
        (s := λ b =>
          if dummet.p = b then φ
          else if dummet.q = b then ψ
          else (.atom b)
        )
        $ eaxm dummet.mem_dummet;

instance [H.HasEFQ] : System.Intuitionistic H where

instance [H.HasDNE] : System.Classical H where

end

end


abbrev theorems (H : Hilbert α) : Set (Formula α) := System.theory H


section systems

variable (α) [DecidableEq α]

protected abbrev Minimal : Hilbert α := ⟨∅⟩

section

variable [hα : HasElements 1 α]

protected abbrev Int : Hilbert α := ⟨{⊥ ➝ (.atom (hα.fn 0))}⟩

instance : (Hilbert.Int α).HasEFQ where p := (hα.fn 0)

instance : System.Intuitionistic (Hilbert.Int α) where

instance : (Hilbert.Int α).FiniteAxiomatizable where axioms_fin := by simp

end



section

variable [hα : HasElements 1 α]

protected abbrev Cl : Hilbert α := ⟨{⊥ ➝ (.atom (hα.fn 0)), (.atom (hα.fn 0) ⋎ ∼(.atom (hα.fn 0)))}⟩
instance : (Hilbert.Cl α).HasLEM where p := (hα.fn 0);
instance : (Hilbert.Cl α).HasEFQ where p := (hα.fn 0);

end


section

variable [hα : HasElements 1 α]

/--
  `KC` from Chagrov & Zakharyaschev (1997)
-/
protected abbrev KC : Hilbert α := ⟨{⊥ ➝ (.atom (hα.fn 0)), ∼(.atom (hα.fn 0)) ⋎ ∼∼(.atom (hα.fn 0))}⟩
instance : (Hilbert.KC α).HasEFQ where p := (hα.fn 0)
instance : (Hilbert.KC α).HasWeakLEM where p := (hα.fn 0)

end


section

variable [hα : HasElements 2 α]

/--
  `LC` from Chagrov & Zakharyaschev (1997)
-/
protected abbrev LC : Hilbert α := ⟨{⊥ ➝ (.atom (hα.fn 0)), ((.atom (hα.map 0) ➝ .atom (hα.map 1)) ⋎ (.atom (hα.map 1) ➝ .atom (hα.map 0)))}⟩
instance : (Hilbert.LC α).HasEFQ where p := (hα.fn 0)
instance : (Hilbert.LC α).HasDummett where
  p := (hα.fn 0);
  q := (hα.fn 1);
  ne_pq := hα.distinct (by trivial)

end

end systems


abbrev Consistent (H : Hilbert α) := System.Consistent H


namespace Deduction

open System

variable {H : Hilbert α} {φ ψ : Formula α}

lemma eaxm! (h : φ ∈ H.axioms) : H ⊢! φ := ⟨eaxm h⟩

lemma mdp! (hpq : H ⊢! (φ ➝ ψ)) (hp : H ⊢! φ) : H ⊢! ψ := ⟨mdp hpq.some hp.some⟩

lemma subst! (hp : H ⊢! φ) (s : Substitution α) : H ⊢! (φ⟦s⟧) := ⟨subst s hp.some⟩

noncomputable def rec! {α : Type u} {H : Hilbert α}
  {motive : (a : Formula α) → H ⊢! a → Sort u_1}
  (hAxm   : ∀ {φ}, (a : φ ∈ H.axioms) → motive φ ⟨eaxm a⟩)
  (hMdp    : ∀ {φ ψ}, {hpq : H ⊢! (φ ➝ ψ)} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (hSubst  : ∀ {φ s}, {hp : H ⊢! φ} → motive φ hp → motive (φ⟦s⟧) (subst! hp s))
  (hVerum  : motive ⊤ verum!)
  (hImply₁ : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ) imply₁!)
  (hImply₂ : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) imply₂!)
  (hAnd₁   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) and₁!)
  (hAnd₂   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) and₂!)
  (hAnd₃   : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) and₃!)
  (hOr₁    : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) or₁!)
  (hOr₂    : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) or₂!)
  (hOr₃    : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) or₃!) :
  {a : Formula α} → (t : H ⊢! a) → motive a t := by
  intro φ d;
  induction d.some with
  | eaxm h => exact hAxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | subst s hp ihp => exact hSubst (ihp ⟨hp⟩);
  | _ => aesop

end Deduction


open System

section

lemma weaker_than_of_subset_axiomset' {H₁ H₂ : Hilbert α} (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ)
  : H₁ ≤ₛ H₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.rec! with
  | hAxm hp => apply hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hSubst hp => exact subst! hp _;
  | _ => simp;

lemma weaker_than_of_subset_axiomset {H₁ H₂ : Hilbert α} (hSubset : H₁.axioms ⊆ H₂.axioms := by aesop) : H₁ ≤ₛ H₂ := by
  apply weaker_than_of_subset_axiomset';
  intro φ hp;
  apply eaxm! $ hSubset hp;

lemma Int_weaker_than_Cl [HasElements 1 α]: (Hilbert.Int α) ≤ₛ (Hilbert.Cl α) := weaker_than_of_subset_axiomset

lemma Int_weaker_than_KC [HasElements 1 α] : (Hilbert.Int α) ≤ₛ (Hilbert.KC α) := weaker_than_of_subset_axiomset

/-
lemma Int_weaker_than_LC [HasElements 1 α] [HasElements 2 α] : (Hilbert.Int α) ≤ₛ (Hilbert.LC α) := weaker_than_of_subset_axiomset

lemma KC_weaker_than_Cl [HasElements 1 α] : (Hilbert.KC α) ≤ₛ (Hilbert.Cl α) := weaker_than_of_subset_axiomset' $ by
  rintro φ (⟨_, rfl⟩ | ⟨_, rfl⟩);
  . sorry;
  . sorry;

lemma LC_weaker_than_Cl [DecidableEq α] [HasElements 2 α] : (Hilbert.LC α) ≤ₛ (Hilbert.Cl α) := by
  apply weaker_than_of_subset_axiomset';
  rintro φ (⟨_, rfl⟩ | ⟨_, _, rfl⟩);
  . sorry;
  . sorry;

lemma KC_weaker_than_LC [DecidableEq α] [HasElements 2 α] : (Hilbert.KC α) ≤ₛ (Hilbert.LC α) := by
  apply weaker_than_of_subset_axiomset';
  rintro φ (⟨_, rfl⟩ | ⟨_, rfl⟩)
  . sorry;
  . sorry;
-/

end


end Hilbert

end LO.IntProp
