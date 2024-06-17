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

instance [𝓓.IncludeEFQ] : System.HasEFQ 𝓓 where
  efq _ := eaxm $ Set.mem_of_subset_of_mem IncludeEFQ.include_EFQ (by simp);

instance [𝓓.IncludeLEM] : System.HasLEM 𝓓 where
  lem _ := eaxm $ Set.mem_of_subset_of_mem IncludeLEM.include_LEM (by simp);

instance [𝓓.IncludeDNE] : System.HasDNE 𝓓 where
  dne _ := eaxm $ Set.mem_of_subset_of_mem IncludeDNE.include_DNE (by simp);

instance [𝓓.IncludeEFQ] : System.Intuitionistic 𝓓 where

instance [𝓓.IncludeDNE] : System.Classical 𝓓 where

instance [𝓓.IncludeEFQ] [𝓓.IncludeLEM] : System.Classical 𝓓 where


namespace DeductionParameter

protected abbrev Minimal : DeductionParameter α := { axiomSet := ∅ }

protected abbrev Intuitionistic : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 }
notation "𝐈𝐧𝐭" => DeductionParameter.Intuitionistic
instance : IncludeEFQ (α := α) 𝐈𝐧𝐭 where
instance : System.Intuitionistic (𝐈𝐧𝐭 : DeductionParameter α) where

protected abbrev Classical : DeductionParameter α := { axiomSet := 𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠 }
notation "𝐂𝐥" => DeductionParameter.Classical
instance : IncludeLEM (α := α) 𝐂𝐥 where
instance : IncludeEFQ (α := α) 𝐂𝐥 where

/- MEMO:
  Term `WeakMinimal` and `WeakClassical` are from Ariola (2007)
  Minimal <ₛ WeakMinimal <ₛ WeakClassical <ₛ Classical
-/

protected abbrev WeakMinimal : DeductionParameter α := { axiomSet := 𝗟𝗘𝗠 }

protected abbrev WeakClassical : DeductionParameter α := { axiomSet := 𝗣𝗲 }


end DeductionParameter


open System

lemma reducible_efq_dne : (𝐈𝐧𝐭 : DeductionParameter α) ≤ₛ 𝐂𝐥 := by
  rintro p hp;
  simp [System.theory];
  induction hp.some with
  | eaxm h =>
    obtain ⟨q, hq⟩ := by simpa using h;
    subst hq;
    apply efq!;
  | mdp h₁ h₂ ih₁ ih₂ => exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ => simp;

variable {p : Formula α}

theorem iff_provable_dn_efq_dne_provable: 𝐈𝐧𝐭 ⊢! ~~p ↔ 𝐂𝐥 ⊢! p := by
  constructor;
  . intro d; exact dne'! $ reducible_efq_dne d;
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
        apply FiniteContext.deduct'!;
        have : [~(q ⋎ ~q)] ⊢[𝐈𝐧𝐭]! ~q ⋏ ~~q := demorgan₃'! $ FiniteContext.id!;
        exact (and₂'! this) ⨀ (and₁'! this);
    | @mdp p q h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : 𝐈𝐧𝐭 ⊢! ~p ↔ 𝐂𝐥 ⊢! ~p := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end LO.Propositional.Superintuitionistic
