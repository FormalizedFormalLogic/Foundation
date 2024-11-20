import Foundation.Modal.Formula
import Foundation.Modal.System
import Foundation.Logic.HilbertStyle.Lukasiewicz

namespace LO.Modal

variable {α : Type*}


section

/-- instance of inference rule -/
structure Hilbert.InferenceRule (α : Type*) where
  antecedents : List (Formula α)
  consequence : Formula α
  /--
  Empty antecedent rule can be simply regarded as axiom rule.
  However, union of all these rules including to `Hilbert.rules` would be too complex for implementation and induction,
  so more than one antecedent is required.
  -/
  antecedents_nonempty : antecedents ≠ [] := by simp

namespace Hilbert.InferenceRule

abbrev Necessitation (φ : Formula α) : InferenceRule α := ⟨[φ], □φ, by simp⟩
abbrev Necessitation.set : Set (InferenceRule α) := { Necessitation φ | φ }
notation "⟮Nec⟯" => Necessitation.set

abbrev LoebRule (φ : Formula α) : InferenceRule α := ⟨[□φ ➝ φ], φ, by simp⟩
abbrev LoebRule.set : Set (InferenceRule α) := { LoebRule φ | φ }
notation "⟮Loeb⟯" => LoebRule.set

abbrev HenkinRule (φ : Formula α) : InferenceRule α := ⟨[□φ ⭤ φ], φ, by simp⟩
abbrev HenkinRule.set : Set (InferenceRule α) := { HenkinRule φ | φ }
notation "⟮Henkin⟯" => HenkinRule.set

end Hilbert.InferenceRule

end


structure Hilbert (α : Type*) where
  axioms : Theory α
  rules : Set (Hilbert.InferenceRule α)


inductive Hilbert.Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}     : φ ∈ H.axioms → Deduction H φ
  | rule {rl}    : rl ∈ H.rules → (∀ {φ}, φ ∈ rl.antecedents → Deduction H φ) → Deduction H rl.consequence
  | mdp {φ ψ}    : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | imply₁ φ ψ   : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ       : Deduction H $ Axioms.ElimContra φ ψ

namespace Hilbert.Deduction

variable {H H₁ H₂ : Hilbert α}

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : System.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elim_contra := ec

instance : System.Classical H where

instance : System.HasDiaDuality H := inferInstance

lemma maxm! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := ⟨maxm h⟩

end Hilbert.Deduction


namespace Hilbert

open Deduction

class HasNecessitation (H : Hilbert α) where
  has_necessitation : ⟮Nec⟯ ⊆ H.rules := by aesop

instance [HasNecessitation H] : System.Necessitation H where
  nec := @λ φ d => rule (show { antecedents := [φ], consequence := □φ } ∈ H.rules by apply HasNecessitation.has_necessitation; simp_all) (by aesop);


class HasLoebRule (H : Hilbert α) where
  has_loeb : ⟮Loeb⟯ ⊆ H.rules := by aesop

instance [HasLoebRule H] : System.LoebRule H where
  loeb := @λ φ d => rule (show { antecedents := [□φ ➝ φ], consequence := φ } ∈ H.rules by apply HasLoebRule.has_loeb; simp_all) (by aesop);


class HasHenkinRule (H : Hilbert α) where
  has_henkin : ⟮Henkin⟯ ⊆ H.rules := by aesop

instance [HasHenkinRule H] : System.HenkinRule H where
  henkin := @λ φ d => rule (show { antecedents := [□φ ⭤ φ], consequence := φ } ∈ H.rules by apply HasHenkinRule.has_henkin; simp_all) (by aesop);


class HasNecOnly (H : Hilbert α) where
  has_necessitation_only : H.rules = ⟮Nec⟯ := by rfl

instance [h : HasNecOnly H] : H.HasNecessitation where
  has_necessitation := by rw [h.has_necessitation_only]


class HasAxiomK (H : Hilbert α) where
  has_axiomK : 𝗞 ⊆ H.axioms := by aesop

instance [HasAxiomK H] : System.HasAxiomK H where
  K _ _ := maxm (by apply HasAxiomK.has_axiomK; simp_all)

class IsNormal (H : Hilbert α) extends H.HasNecOnly, H.HasAxiomK where

instance {H : Hilbert α} [H.IsNormal] : System.K H where

end Hilbert


namespace Hilbert.Deduction

open Hilbert

variable {H : Hilbert α}

noncomputable def inducition!
  {motive  : (φ : Formula α) → H ⊢! φ → Sort*}
  (hRules  : (r : InferenceRule α) → (hr : r ∈ H.rules) →
             (hant : ∀ {φ}, φ ∈ r.antecedents → H ⊢! φ) →
             (ih : ∀ {φ}, (hp : φ ∈ r.antecedents) →
             motive φ (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  (hMaxm     : ∀ {φ}, (h : φ ∈ H.axioms) → motive φ ⟨maxm h⟩)
  (hMdp      : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ ⟨mdp hpq.some hp.some⟩)
  (hImply₁     : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | rule hr h ih => apply hRules _ hr; intro φ hp; exact ih hp ⟨h hp⟩;
  | imply₁ => exact hImply₁
  | imply₂ => exact hImply₂
  | ec => exact hElimContra

/-- Useful induction for normal modal logic. -/
noncomputable def inducition_with_necOnly! [H.HasNecOnly]
  {motive  : (φ : Formula α) → H ⊢! φ → Prop}
  (hMaxm   : ∀ {φ}, (h : φ ∈ H.axioms) → motive φ ⟨maxm h⟩)
  (hMdp    : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (hpq ⨀ hp))
  (hNec    : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (System.nec! hp))
  (hImply₁   : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂   : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp (ihpq) (ihp);
  | hRules rl hrl hant ih =>
    rw [HasNecOnly.has_necessitation_only] at hrl;
    obtain ⟨φ, rfl⟩ := hrl;
    exact @hNec φ (hant (by simp)) $ ih (by simp);
  | hImply₁ => exact hImply₁
  | hImply₂ => exact hImply₂
  | hElimContra => exact hElimContra

end Hilbert.Deduction


namespace Hilbert

abbrev theorems (H : Hilbert α) := System.theory H

abbrev Consistent (H : Hilbert α) := System.Consistent H

section K

variable (α)

protected abbrev K : Hilbert α := ⟨𝗞, ⟮Nec⟯⟩
instance : (Hilbert.K α).IsNormal where

end K


section K_extension

protected abbrev ExtK (Ax : Theory α) : Hilbert α := ⟨𝗞 ∪ Ax, ⟮Nec⟯⟩
instance : (Hilbert.ExtK Ax).IsNormal where

namespace ExtK

lemma K_is_extK_of_empty : (Hilbert.K α) = (Hilbert.ExtK ∅) := by aesop;

lemma K_is_extK_of_AxiomK : (Hilbert.K α) = (Hilbert.ExtK 𝗞) := by aesop;

lemma def_ax : (Hilbert.ExtK Ax).axioms = (𝗞 ∪ Ax) := rfl

lemma maxm! (h : φ ∈ Ax) : (Hilbert.ExtK Ax) ⊢! φ := ⟨Deduction.maxm (by simp [Hilbert.ExtK]; tauto)⟩

end ExtK

end K_extension


section S4_extension

protected abbrev ExtS4 (Ax : Theory α) : Hilbert α := Hilbert.ExtK (𝗧 ∪ 𝟰 ∪ Ax)
instance : System.S4 (Hilbert.ExtS4 Ax) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

@[simp] lemma ExtS4.def_ax : (Hilbert.ExtS4 Ax).axioms = (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ Ax) := by aesop;

end S4_extension


section systems

variable (α)

protected abbrev KT : Hilbert α := Hilbert.ExtK $ 𝗧
instance : System.KT (Hilbert.KT α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KB : Hilbert α := Hilbert.ExtK $ 𝗕
instance : System.KB (Hilbert.KB α) where
  B _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KD : Hilbert α := Hilbert.ExtK $ 𝗗
instance : System.KD (Hilbert.KD α) where
  D _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KP : Hilbert α := Hilbert.ExtK $ 𝗣
instance : System.KP (Hilbert.KP α) where
  P := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KTB : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝗕

protected abbrev K4 : Hilbert α := Hilbert.ExtK $ 𝟰
instance : System.K4 (Hilbert.K4 α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K5 : Hilbert α := Hilbert.ExtK $ 𝟱
instance : System.K5 (Hilbert.K5 α) where
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S4 : Hilbert α := Hilbert.ExtS4 $ ∅
instance : System.S4 (Hilbert.S4 α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S4Dot2 : Hilbert α := Hilbert.ExtS4 $ .𝟮

protected abbrev S4Dot3 : Hilbert α := Hilbert.ExtS4 $ .𝟯

protected abbrev S4Grz : Hilbert α := Hilbert.ExtS4 $ 𝗚𝗿𝘇

protected abbrev KT4B : Hilbert α := Hilbert.ExtS4 $ 𝗕

protected abbrev S5 : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝟱
instance : System.S5 (Hilbert.S5 α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S5Grz : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝟱 ∪ 𝗚𝗿𝘇
instance : System.S5Grz (Hilbert.S5Grz α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Grz _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Triv : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝗧𝗰
instance : System.Triv (Hilbert.Triv α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Tc _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Ver : Hilbert α := Hilbert.ExtK $ 𝗩𝗲𝗿
instance : System.Ver (Hilbert.Ver α) where
  Ver _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev GL : Hilbert α := Hilbert.ExtK $ 𝗟
instance : System.GL (Hilbert.GL α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Grz : Hilbert α := Hilbert.ExtK $ 𝗚𝗿𝘇
instance : System.Grz (Hilbert.Grz α) where
  Grz _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KH : Hilbert α := Hilbert.ExtK $ 𝗛
instance : System.KH (Hilbert.KH α) where
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4H : Hilbert α := Hilbert.ExtK $ 𝟰 ∪ 𝗛
instance : System.K4H (Hilbert.K4H α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Loeb : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Loeb⟯⟩
instance : (Hilbert.K4Loeb α).HasAxiomK where
instance : (Hilbert.K4Loeb α).HasNecessitation where
instance : (Hilbert.K4Loeb α).HasLoebRule where
instance : System.K4Loeb (Hilbert.K4Loeb α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Henkin : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Henkin⟯⟩
instance : (Hilbert.K4Henkin α).HasAxiomK  where
instance : (Hilbert.K4Henkin α).HasNecessitation where
instance : (Hilbert.K4Henkin α).HasHenkinRule where
instance : System.K4Henkin (Hilbert.K4Henkin α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

/--
  Solovey's Provability Logic of True Arithmetic.
  Remark necessitation is *not* permitted.
-/
protected abbrev GLS : Hilbert α := ⟨(Hilbert.GL α).theorems ∪ 𝗧, ∅⟩
instance : System.HasAxiomK (Hilbert.GLS α) where
  K _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomL (Hilbert.GLS α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomT (Hilbert.GLS α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

/-- Logic of Pure Necessitation -/
protected abbrev N : Hilbert α := ⟨∅, ⟮Nec⟯⟩
instance : (Hilbert.N α).HasNecOnly where

end systems


section

variable [DecidableEq α]
open System
open Formula (atom)

lemma normal_weakerThan_of_maxm {H₁ H₂ : Hilbert α} [H₁.IsNormal] [H₂.IsNormal]
  (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ)
  : H₁ ≤ₛ H₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra!

lemma normal_weakerThan_of_subset {H₁ H₂ : Hilbert α} [H₁.IsNormal] [H₂.IsNormal] (hSubset : H₁.axioms ⊆ H₂.axioms)
  : H₁ ≤ₛ H₂ := by
  apply normal_weakerThan_of_maxm;
  intro φ hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;


lemma K_weakerThan_KD : (Hilbert.K α) ≤ₛ (Hilbert.KD α) := normal_weakerThan_of_subset $ by aesop;

lemma K_weakerThan_KB : (Hilbert.K α) ≤ₛ (Hilbert.KB α) := normal_weakerThan_of_subset $ by aesop;

lemma K_weakerThan_KT : (Hilbert.K α) ≤ₛ (Hilbert.KT α) := normal_weakerThan_of_subset $ by aesop;

lemma K_weakerThan_K4 : (Hilbert.K α) ≤ₛ (Hilbert.K4 α) := normal_weakerThan_of_subset $ by aesop;

lemma K_weakerThan_K5 : (Hilbert.K α) ≤ₛ (Hilbert.K5 α) := normal_weakerThan_of_subset $ by aesop;

lemma KT_weakerThan_S4 : (Hilbert.KT α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma K4_weakerThan_S4 : (Hilbert.K4 α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma S4_weakerThan_S4Dot2 : (Hilbert.S4 α) ≤ₛ (Hilbert.S4Dot2 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma S4_weakerThan_S4Dot3 : (Hilbert.S4 α) ≤ₛ (Hilbert.S4Dot3 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma S4_weakerThan_S4Grz : (Hilbert.S4 α) ≤ₛ (Hilbert.S4Grz α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma K_weakerThan_GL : (Hilbert.K α) ≤ₛ (Hilbert.GL α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma K4_weakerThan_Triv : (Hilbert.K4 α) ≤ₛ (Hilbert.Triv α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

lemma K4_weakerThan_GL : (Hilbert.K4 α) ≤ₛ (Hilbert.GL α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

lemma KT_weakerThan_Grz : (Hilbert.KT α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

lemma K4_weakerThan_Grz : (Hilbert.K4 α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

lemma KD_weakerThan_KP : (Hilbert.KD α) ≤ₛ (Hilbert.KP α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma KP_weakerThan_KD : (Hilbert.KP α) ≤ₛ (Hilbert.KD α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma KD_equiv_KP : (Hilbert.KD α) =ₛ (Hilbert.KP α) := Equiv.antisymm_iff.mpr ⟨KD_weakerThan_KP, KP_weakerThan_KD⟩

lemma GL_weakerThan_K4Loeb : (Hilbert.GL α) ≤ₛ (Hilbert.K4Loeb α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (hK | hL)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hL; exact axiomL!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra!

lemma K4Loeb_weakerThan_K4Henkin : (Hilbert.K4Loeb α) ≤ₛ (Hilbert.K4Henkin α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hFour; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hLoeb);
    . obtain ⟨φ, rfl⟩ := hNec; exact nec! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
    . obtain ⟨φ, rfl⟩ := hLoeb; exact loeb! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra!

lemma K4Henkin_weakerThan_K4H : (Hilbert.K4Henkin α) ≤ₛ (Hilbert.K4H α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hFour; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hHenkin);
    . obtain ⟨φ, rfl⟩ := hNec; exact nec! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
    . obtain ⟨φ, rfl⟩ := hHenkin; exact henkin! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra!

lemma K4Henkin_weakerThan_GL : (Hilbert.K4H α) ≤ₛ (Hilbert.GL α) := by
  apply normal_weakerThan_of_maxm;
  intro φ hp;
  rcases hp with hK | hFour | hH
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hFour; exact axiomFour!;
  . obtain ⟨_, _, rfl⟩ := hH; exact axiomH!;

lemma GL_equiv_K4Loeb : (Hilbert.GL α) =ₛ (Hilbert.K4Loeb α) := by
  apply Equiv.antisymm_iff.mpr;
  constructor;
  . exact GL_weakerThan_K4Loeb;
  . exact WeakerThan.trans (K4Loeb_weakerThan_K4Henkin) $ WeakerThan.trans K4Henkin_weakerThan_K4H K4Henkin_weakerThan_GL

omit [DecidableEq α] in
lemma GL_weakerThan_GLS : (Hilbert.GL α) ≤ₛ (Hilbert.GLS α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  exact Deduction.maxm! (by left; simpa);

lemma S5Grz_weakerThan_Triv : (Hilbert.S5Grz α) ≤ₛ (Hilbert.Triv α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp;

lemma Triv_weakerThan_S5Grz : (Hilbert.Triv α) ≤ₛ (Hilbert.S5Grz α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma S5Grz_equiv_Triv : (Hilbert.S5Grz α) =ₛ (Hilbert.Triv α)
  := Equiv.antisymm_iff.mpr ⟨S5Grz_weakerThan_Triv, Triv_weakerThan_S5Grz⟩

end


section

open System

variable [DecidableEq α]
variable {H : Hilbert α} [H.IsNormal]
variable {φ : Formula α} {σ : α → Formula α}

lemma admissible_subst! [H.axioms.SubstClosed] (d : H ⊢! φ) : H ⊢! φ.subst σ := by
  induction d using Deduction.inducition_with_necOnly! with
  | hImply₁ => simp;
  | hImply₂ => simp;
  | hElimContra => simp;
  | hMdp ihφ ihψ => exact System.mdp! ihφ ihψ;
  | hNec ih => exact nec! ih;
  | @hMaxm φ h =>
    apply Deduction.maxm!;
    induction φ using Formula.rec' with
    | hfalsum => exact h;
    | hatom a => exact Theory.SubstClosed.mem_atom h;
    | himp φ ψ => exact Theory.SubstClosed.mem_imp h;
    | hbox φ => exact Theory.SubstClosed.mem_box h;

instance : Theory.SubstClosed (α := α) 𝗞 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗟 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗚𝗿𝘇 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗛 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : (Hilbert.K α).axioms.SubstClosed := inferInstance

instance : (Hilbert.GL α).axioms.SubstClosed := inferInstance

instance : (Hilbert.Grz α).axioms.SubstClosed := inferInstance


end


end Hilbert

end LO.Modal
