import Logic.Logic.HilbertStyle.Basic
import Logic.Logic.HilbertStyle.Supplemental
import Logic.Propositional.Superintuitionistic.Formula

namespace LO.Propositional.Superintuitionistic

variable {α : Type u} [DecidableEq α]

structure DeductionParameter (α) where
  axiomSet : AxiomSet α
notation "Ax(" 𝓓 ")" => DeductionParameter.axiomSet 𝓓

namespace DeductionParameter

class IncludeEFQ (𝓓 : DeductionParameter α) where
  include_EFQ : 𝗘𝗙𝗤 ⊆ Ax(𝓓) := by simp

class IncludeLEM (𝓓 : DeductionParameter α) where
  include_LEM : 𝗟𝗘𝗠 ⊆ Ax(𝓓) := by simp

class IncludeDNE (𝓓 : DeductionParameter α) where
  include_DNE : 𝗗𝗡𝗘 ⊆ Ax(𝓓) := by simp

end DeductionParameter

inductive Deduction (𝓓 : DeductionParameter α) : Formula α → Type _
  | eaxm {p}     : p ∈ Ax(𝓓) → Deduction 𝓓 p
  | mdp {p q}    : Deduction 𝓓 (p ⟶ q) → Deduction 𝓓 p → Deduction 𝓓 q
  | verum        : Deduction 𝓓 $ ⊤
  | imply₁ p q   : Deduction 𝓓 $ p ⟶ q ⟶ p
  | imply₂ p q r : Deduction 𝓓 $ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  | and₁ p q     : Deduction 𝓓 $ p ⋏ q ⟶ p
  | and₂ p q     : Deduction 𝓓 $ p ⋏ q ⟶ q
  | and₃ p q     : Deduction 𝓓 $ p ⟶ q ⟶ p ⋏ q
  | or₁ p q      : Deduction 𝓓 $ p ⟶ p ⋎ q
  | or₂ p q      : Deduction 𝓓 $ q ⟶ p ⋎ q
  | or₃ p q r    : Deduction 𝓓 $ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)
  | neg_equiv p  : Deduction 𝓓 $ Axioms.NegEquiv p

instance : System (Formula α) (DeductionParameter α) := ⟨Deduction⟩

open Deduction
open DeductionParameter

variable {𝓓 : DeductionParameter α}

instance : System.Minimal 𝓓 where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  neg_equiv := neg_equiv

instance [𝓓.IncludeEFQ] : System.HasAxiomEFQ 𝓓 where
  efq _ := eaxm $ Set.mem_of_subset_of_mem IncludeEFQ.include_EFQ (by simp);

instance [𝓓.IncludeLEM] : System.HasAxiomLEM 𝓓 where
  lem _ := eaxm $ Set.mem_of_subset_of_mem IncludeLEM.include_LEM (by simp);

instance [𝓓.IncludeDNE] : System.HasAxiomDNE 𝓓 where
  dne _ := eaxm $ Set.mem_of_subset_of_mem IncludeDNE.include_DNE (by simp);

instance [𝓓.IncludeEFQ] : System.Intuitionistic 𝓓 where

instance [𝓓.IncludeDNE] : System.Classical 𝓓 where

instance [𝓓.IncludeEFQ] [𝓓.IncludeLEM] : System.Classical 𝓓 where


namespace DeductionParameter

lemma eaxm! {𝓓 : DeductionParameter α} {p : Formula α} (h : p ∈ Ax(𝓓)) : 𝓓 ⊢! p := ⟨eaxm h⟩

protected abbrev Minimal : DeductionParameter α := { axiomSet := ∅ }

protected abbrev Intuitionistic : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 }
notation "𝐈𝐧𝐭" => DeductionParameter.Intuitionistic
instance : IncludeEFQ (α := α) 𝐈𝐧𝐭 where
instance : System.Intuitionistic (𝐈𝐧𝐭 : DeductionParameter α) where

protected abbrev Classical : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠 }
notation "𝐂𝐥" => DeductionParameter.Classical
instance : IncludeLEM (α := α) 𝐂𝐥 where
instance : IncludeEFQ (α := α) 𝐂𝐥 where

-- `𝐊𝐂` from chagrov & zakharyaschev (1997)
protected abbrev KC : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 ∪ 𝗪𝗟𝗘𝗠 }
notation "𝐊𝐂" => DeductionParameter.KC
instance : IncludeEFQ (α := α) 𝐊𝐂 where

-- `𝐋𝐂` from chagrov & zakharyaschev (1997)
protected abbrev LC : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 ∪ 𝗗𝘂𝗺 }
notation "𝐋𝐂" => DeductionParameter.LC
instance : IncludeEFQ (α := α) 𝐋𝐂 where

/- MEMO:
  Term `WeakMinimal` and `WeakClassical` are from Ariola (2007)
  Minimal <ₛ WeakMinimal <ₛ WeakClassical <ₛ Classical
-/

protected abbrev WeakMinimal : DeductionParameter α := { axiomSet := 𝗟𝗘𝗠 }

protected abbrev WeakClassical : DeductionParameter α := { axiomSet := 𝗣𝗲 }


end DeductionParameter


namespace Deduction

variable {Λ : DeductionParameter α}

open System

noncomputable def rec! {α : Type u} {𝓓 : DeductionParameter α}
  {motive : (a : Formula α) → 𝓓 ⊢! a → Sort u_1}
  (eaxm   : ∀ {p}, (a : p ∈ Ax(𝓓)) → motive p ⟨eaxm a⟩)
  (mdp    : ∀ {p q}, {hpq : 𝓓 ⊢! (p ⟶ q)} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (verum  : motive ⊤ verum!)
  (imply₁ : ∀ {p q},   motive (p ⟶ q ⟶ p) imply₁!)
  (imply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) imply₂!)
  (and₁   : ∀ {p q},   motive (p ⋏ q ⟶ p) and₁!)
  (and₂   : ∀ {p q},   motive (p ⋏ q ⟶ q) and₂!)
  (and₃   : ∀ {p q},   motive (p ⟶ q ⟶ p ⋏ q) and₃!)
  (or₁    : ∀ {p q},   motive (p ⟶ p ⋎ q) or₁!)
  (or₂    : ∀ {p q},   motive (q ⟶ p ⋎ q) or₂!)
  (or₃    : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r) or₃!)
  (neg_equiv : ∀ {p}, motive (Axioms.NegEquiv p) neg_equiv!) :
  {a : Formula α} → (t : 𝓓 ⊢! a) → motive a t := by
  intro p d;
  induction d.some with
  | eaxm h => exact eaxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop

end Deduction


open System

variable {Λ₁ Λ₂ : DeductionParameter α}

lemma weaker_than_of_subset_axiomset' (hMaxm : ∀ {p : Formula α}, p ∈ Ax(Λ₁) → Λ₂ ⊢! p)
  : Λ₁ ≤ₛ Λ₂ := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  induction h using Deduction.rec! with
  | eaxm hp => apply hMaxm hp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => simp;

lemma weaker_than_of_subset_axiomset (hSubset : Ax(Λ₁) ⊆ Ax(Λ₂) := by aesop) : Λ₁ ≤ₛ Λ₂ := by
  apply weaker_than_of_subset_axiomset';
  intro p hp;
  apply eaxm! $ hSubset hp;

lemma Int_weaker_than_Cl : (𝐈𝐧𝐭 : DeductionParameter α) ≤ₛ 𝐂𝐥 := weaker_than_of_subset_axiomset

lemma Int_weaker_than_KC : (𝐈𝐧𝐭 : DeductionParameter α) ≤ₛ 𝐊𝐂 := weaker_than_of_subset_axiomset

lemma Int_weaker_than_LC : (𝐈𝐧𝐭 : DeductionParameter α) ≤ₛ 𝐋𝐂 := weaker_than_of_subset_axiomset

lemma KC_weaker_than_Cl : (𝐊𝐂 : DeductionParameter α) ≤ₛ 𝐂𝐥 := by
  apply weaker_than_of_subset_axiomset';
  intro p hp;
  rcases hp with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma LC_weaker_than_Cl : (𝐋𝐂 : DeductionParameter α) ≤ₛ 𝐂𝐥 := by
  apply weaker_than_of_subset_axiomset';
  intro p hp;
  rcases hp with (⟨_, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

variable {p : Formula α}

theorem iff_provable_dn_efq_dne_provable: 𝐈𝐧𝐭 ⊢! ~~p ↔ 𝐂𝐥 ⊢! p := by
  constructor;
  . intro d; exact dne'! $ Int_weaker_than_Cl d;
  . intro d;
    induction d.some with
    | eaxm h =>
      simp at h;
      rcases h with (hEFQ | hLEM);
      . obtain ⟨q, hq⟩ := by simpa using hEFQ;
        subst hq;
        exact dni'! efq!;
      . obtain ⟨q, hq⟩ := by simpa using hLEM;
        subst hq;
        apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [~(q ⋎ ~q)] ⊢[𝐈𝐧𝐭]! ~q ⋏ ~~q := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | @mdp p q h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : 𝐈𝐧𝐭 ⊢! ~p ↔ 𝐂𝐥 ⊢! ~p := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end LO.Propositional.Superintuitionistic
