import Foundation.Modal.Hilbert.WeakerThan.K4_GL


namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S}

protected class K4Loeb (𝓢 : S) extends System.K4 𝓢, LoebRule 𝓢

namespace K4Loeb

variable [System.K4Loeb 𝓢]

protected def axiomL : 𝓢 ⊢ Axioms.L φ := by
  dsimp [Axioms.L];
  generalize e : □(□φ ➝ φ) ➝ □φ = ψ;
  have d₁ : [□(□φ ➝ φ), □ψ] ⊢[𝓢] □□(□φ ➝ φ) ➝ □□φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₂ : [□(□φ ➝ φ), □ψ] ⊢[𝓢] □□φ ➝ □φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₃ : 𝓢 ⊢ □(□φ ➝ φ) ➝ □□(□φ ➝ φ) := axiomFour;
  have : 𝓢 ⊢ □ψ ➝ ψ := by
    nth_rw 2 [←e]; apply deduct'; apply deduct;
    exact d₂ ⨀ (d₁ ⨀ ((of d₃) ⨀ (FiniteContext.byAxm)));
  exact loeb this;
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ K4Loeb.axiomL⟩

end K4Loeb


protected class K4Henkin (𝓢 : S) extends System.K4 𝓢, HenkinRule 𝓢

namespace K4Henkin

variable [System.K4Henkin 𝓢]

instance : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ iffIntro (axiomK' $ nec h) axiomFour);

end K4Henkin


protected class K4H (𝓢 : S) extends System.K4 𝓢, HasAxiomH 𝓢

namespace K4H

variable [System.K4H 𝓢]

instance : HenkinRule 𝓢 where
  henkin h := (and₁' h) ⨀ (axiomH ⨀ nec h);

end K4H

end LO.System


namespace LO.Modal.Hilbert

open System

section

protected abbrev K4H (α) : Hilbert α := Hilbert.ExtK $ 𝟰 ∪ 𝗛
instance : System.K4H (Hilbert.K4H α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Loeb (α) : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Loeb⟯⟩
instance : (Hilbert.K4Loeb α).HasAxiomK where
instance : (Hilbert.K4Loeb α).HasNecessitation where
instance : (Hilbert.K4Loeb α).HasLoebRule where
instance : System.K4Loeb (Hilbert.K4Loeb α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Henkin (α) : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Henkin⟯⟩
instance : (Hilbert.K4Henkin α).HasAxiomK  where
instance : (Hilbert.K4Henkin α).HasNecessitation where
instance : (Hilbert.K4Henkin α).HasHenkinRule where
instance : System.K4Henkin (Hilbert.K4Henkin α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end

variable [DecidableEq α]

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


theorem GL_equiv_K4Loeb : (Hilbert.GL α) =ₛ (Hilbert.K4Loeb α) := by
  apply Equiv.antisymm_iff.mpr;
  constructor;
  . exact GL_weakerThan_K4Loeb;
  . exact WeakerThan.trans (K4Loeb_weakerThan_K4Henkin) $ WeakerThan.trans K4Henkin_weakerThan_K4H K4Henkin_weakerThan_GL


end LO.Modal.Hilbert
