import Foundation.Propositional.Entailment.Minimal.Basic


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev EFQ := ⊥ ➝ φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} {𝓢 : S} {φ ψ χ : F}


section

variable [LogicalConnective F] [Entailment F S]

class HasAxiomEFQ (𝓢 : S) where
  efq {φ : F} : 𝓢 ⊢! Axioms.EFQ φ

export HasAxiomEFQ (efq)
@[simp] lemma efq! [Entailment.HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := ⟨efq⟩

def of_O [ModusPonens 𝓢] [Entailment.HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := efq ⨀ b
@[grind] lemma of_O! [ModusPonens 𝓢]  [Entailment.HasAxiomEFQ 𝓢] (h : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := ⟨of_O h.some⟩

instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩

protected class Int (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomEFQ 𝓢

end


section

variable [LogicalConnective F] [Entailment F S] [Entailment.Minimal 𝓢]

namespace FiniteContext

variable {Γ Δ E : List F}

instance [Entailment.HasAxiomEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomEFQ Γ := ⟨of efq⟩

instance  [Entailment.HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance
instance [Entailment.Int 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Int Γ where

end FiniteContext


namespace Context

instance [Entailment.HasAxiomEFQ 𝓢] (Γ : Context F 𝓢) : HasAxiomEFQ Γ := ⟨of efq⟩

instance [Entailment.HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

instance [DecidableEq F] [Entailment.Int 𝓢] (Γ : Context F 𝓢) : Entailment.Int Γ where

end Context

end


section

variable {F : Type*} [LogicalConnective F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Int 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

def efq_of_mem_either [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ψ := of_O $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ψ := ⟨efq_of_mem_either h₁ h₂⟩

def CNC [DecidableEq F] : 𝓢 ⊢! ∼φ ➝ φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma CNC! [DecidableEq F] : 𝓢 ⊢ ∼φ ➝ φ ➝ ψ := ⟨CNC⟩

def CCN [DecidableEq F] : 𝓢 ⊢! φ ➝ ∼φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma CCN! [DecidableEq F] : 𝓢 ⊢ φ ➝ ∼φ ➝ ψ := ⟨CCN⟩

lemma C_of_N [DecidableEq F] (h : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ φ ➝ ψ := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [φ] ⊢[𝓢] φ ➝ ⊥ := of'! $ N!_iff_CO!.mp h;
  exact of_O! (dnp ⨀ FiniteContext.id!);

lemma CN!_of_! [DecidableEq F] (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼φ ➝ ψ := CCN! ⨀ h

def CANC [DecidableEq F] : 𝓢 ⊢! (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := left_A_intro (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (φ := φ) (by simp) (by simp)
  ) imply₁
@[simp] lemma CANC! [DecidableEq F] : 𝓢 ⊢ (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := ⟨CANC⟩

def C_of_AN [DecidableEq F] (b : 𝓢 ⊢! ∼φ ⋎ ψ) : 𝓢 ⊢! φ ➝ ψ := CANC ⨀ b
lemma C!_of_AN! [DecidableEq F] (b : 𝓢 ⊢ ∼φ ⋎ ψ) : 𝓢 ⊢ φ ➝ ψ := ⟨C_of_AN b.some⟩

def CCNNNNNNC [DecidableEq F] : 𝓢 ⊢! (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := by
  apply deduct';
  apply N_of_CO;
  exact C_trans
    (by
      apply deductInv;
      apply CC_of_CK;
      apply deduct;
      have d₁ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢]! ∼∼φ ➝ ∼∼ψ := K_left (ψ := ∼(φ ➝ ψ)) $ FiniteContext.id;
      have d₂ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢]! ∼∼φ ⋏ ∼ψ := KNN_of_NA $ (contra CANC) ⨀ (K_right (φ := (∼∼φ ➝ ∼∼ψ)) $ FiniteContext.id)
      exact K_intro (K_right d₂) (d₁ ⨀ (K_left d₂))
    )
    (CKNO (φ := ∼ψ));

@[simp] lemma CCNNNNNNC! [DecidableEq F] : 𝓢 ⊢ (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := ⟨CCNNNNNNC⟩

def NNC_of_CNNNN [DecidableEq F] (b : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢! ∼∼(φ ➝ ψ) := CCNNNNNNC ⨀ b
lemma NNC!_of_CNNNN! [DecidableEq F] (b : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢ ∼∼(φ ➝ ψ) := ⟨NNC_of_CNNNN b.some⟩

section Conjunction

end Conjunction

section disjunction

def left_Disj_intro [DecidableEq F] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! Γ.disj ➝ φ :=
  match Γ with
  |     [] => efq
  | ψ :: Γ => left_A_intro (b ψ (by simp)) <| left_Disj_intro Γ fun ψ h ↦ b ψ (by simp [h])
def left_Disj!_intro [DecidableEq F] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ Γ.disj ➝ φ :=
  ⟨left_Disj_intro Γ fun ψ h ↦ (b ψ h).get⟩

def left_Disj₂_intro (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! ⋁Γ ➝ φ :=
  match Γ with
  |     [] => efq
  |    [ψ] => b _ (by simp)
  | ψ :: χ :: Γ => left_A_intro (b ψ (by simp)) <| left_Disj₂_intro _ fun ψ h ↦ b ψ (by simp [h])

lemma left_Disj₂!_intro (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ ⋁Γ ➝ φ :=
  ⟨left_Disj₂_intro Γ fun ψ h ↦ (b ψ h).get⟩

def left_Disj'_intro [DecidableEq F] (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢! ψ i ➝ φ) : 𝓢 ⊢! l.disj' ψ ➝ φ :=
  left_Disj₂_intro _ fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (ψ · = χ) (by simpa using h);
    haveI := b i hi;
    e ▸ this
lemma left_Disj'!_intro [DecidableEq F] (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ ψ i ➝ φ) : 𝓢 ⊢ l.disj' ψ ➝ φ :=
  ⟨left_Disj'_intro l ψ fun i hi ↦ (b i hi).get⟩

lemma left_Fdisj!_intro (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ s.disj ➝ φ :=
  left_Disj₂!_intro _ fun ψ h ↦ b ψ (by simpa using h)

lemma left_Fdisj'!_intro [DecidableEq F] (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢ ψ i ➝ φ) : 𝓢 ⊢ (⩖ i ∈ s, ψ i) ➝ φ :=
  left_Disj'!_intro _ _ (by simpa)

lemma left_Udisj!_intro [DecidableEq F] [Fintype ι] (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢ ψ i ➝ φ) : 𝓢 ⊢ (⩖ i, ψ i) ➝ φ :=
  left_Fdisj'!_intro _ _ (by simpa)

lemma EDisj₂AppendADisj₂Disj₂! : 𝓢 ⊢ ⋁(Γ ++ Δ) ⭤ ⋁Γ ⋎ ⋁Δ := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! efq!;
  case hnil.hsingle =>
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! C!_id;
  case hsingle.hnil =>
    apply E!_intro;
    . simp;
    . exact left_A!_intro C!_id efq!;
  case hcons.hnil =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro C!_id efq!;
  case hnil.hcons =>
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! C!_id;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp ψ =>
    simp_all;
    apply E!_trans (by
      apply EAA!_of_E!_right;
      simpa using @ihp [ψ];
    ) EAAAA!;
  case hcons.hcons φ ps hps ihp ψ qs hqs ihq =>
    simp_all;
    exact E!_trans (by
      apply EAA!_of_E!_right;
      exact E!_trans (@ihp (ψ :: qs)) (by
        apply EAA!_of_E!_right;
        simp_all;
      )
    ) EAAAA!;


lemma Disj₂Append!_iff_ADisj₂Disj₂! : 𝓢 ⊢ ⋁(Γ ++ Δ) ↔ 𝓢 ⊢ ⋁Γ ⋎ ⋁Δ := by
  constructor;
  . intro h; exact (K!_left EDisj₂AppendADisj₂Disj₂!) ⨀ h;
  . intro h; exact (K!_right EDisj₂AppendADisj₂Disj₂!) ⨀ h;


lemma CDisj₂!_iff_CADisj₂! : 𝓢 ⊢ φ ➝ ⋁(ψ :: Γ) ↔ 𝓢 ⊢ φ ➝ ψ ⋎ ⋁Γ := by
  induction Γ with
  | nil =>
    simp;
    constructor;
    . intro h; exact C!_trans h or₁!;
    . intro h; exact C!_trans h $ left_A!_intro C!_id efq!;
  | cons ψ ih => simp;

@[simp]
lemma CDisj₂ADisj₂Remove! [DecidableEq F] : 𝓢 ⊢ ⋁Γ ➝ φ ⋎ ⋁(Γ.remove φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp;
    by_cases h: ψ = φ;
    . subst_vars; simp;
    . simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all;
    by_cases hpq : ψ = φ;
    . simp_all only [ne_eq, List.remove_cons_self]; exact left_A!_intro or₁! ih;
    . simp_all [(List.remove_cons_of_ne Γ hpq)];
      by_cases hqΓ : Γ.remove φ = [];
      . simp_all;
        exact left_A!_intro or₂! (C!_trans ih $ CAA!_of_C!_right efq!);
      . simp_all;
        exact left_A!_intro (C!_trans or₁! or₂!) (C!_trans ih (CAA!_of_C!_right or₂!));

lemma left_Disj₂!_intro' [DecidableEq F] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢ ⋁Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ ih =>
    simp_all;
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact of_C!_of_C!_of_A! (by simp) (weakening! (by simp) $ provable_iff_provable.mp $ ih) id!
  | _ => simp_all;

lemma of_Disj₂!_of_mem_eq [DecidableEq F] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : 𝓢 ⊢ ⋁Γ) : 𝓢 ⊢ φ := (left_Disj₂!_intro' hd) ⨀ h


@[simp] lemma CFDisjDisj₂ [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ ⋁Γ.toList ➝ Γ.disj := by
  apply left_Disj₂!_intro;
  intro ψ hψ;
  apply right_Fdisj!_intro;
  simpa using hψ;

@[simp] lemma CDisj₂Disj [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ Γ.disj ➝ ⋁Γ.toList := by
  apply left_Fdisj!_intro;
  intro ψ hψ;
  apply right_Disj₂!_intro;
  simpa;

lemma CDisj₂Disj₂_of_subset [DecidableEq F] {Γ Δ : List F} (h : ∀ φ ∈ Γ, φ ∈ Δ) : 𝓢 ⊢ ⋁Γ ➝ ⋁Δ := by
  match Δ with
  | [] =>
    have : Γ = [] := List.iff_nil_forall.mpr h;
    subst this;
    simp;
  | [φ] =>
    apply left_Disj₂!_intro;
    intro ψ hψ;
    have := h ψ hψ;
    simp_all;
  | φ :: Δ =>
    apply left_Disj₂!_intro;
    intro ψ hψ;
    apply right_Disj₂!_intro;
    apply h;
    exact hψ;

lemma CFDisjFDisj_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Γ ⊆ Δ) : 𝓢 ⊢ Γ.disj ➝ Δ.disj := by
  refine C!_trans (C!_trans ?_ (CDisj₂Disj₂_of_subset (Γ := Γ.toList) (Δ := Δ.toList) (by simpa))) ?_ <;> simp;

lemma EDisj₂FDisj [DecidableEq F] {Γ : List F} : 𝓢 ⊢ ⋁Γ ⭤ Γ.toFinset.disj := by
  match Γ with
  | [] => simp;
  | φ :: Γ =>
    apply E!_intro;
    . apply left_Disj₂!_intro;
      simp only [List.mem_cons, List.toFinset_cons, forall_eq_or_imp];
      constructor;
      . apply right_Fdisj!_intro;
        simp_all;
      . intro ψ hψ;
        apply right_Fdisj!_intro;
        simp_all;
    . apply left_Fdisj!_intro;
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, forall_eq_or_imp];
      constructor;
      . apply right_Disj₂!_intro;
        tauto;
      . intro ψ hψ;
        apply right_Disj₂!_intro;
        tauto;

lemma EDisj₂FDisj!_doubleton [DecidableEq F] : 𝓢 ⊢ ⋁[φ, ψ] ⭤ Finset.disj {φ, ψ} := by
  convert EDisj₂FDisj (𝓢 := 𝓢) (Γ := [φ, ψ]);
  simp;

lemma EConj₂_FConj!_doubleton [DecidableEq F] : 𝓢 ⊢ ⋁[φ, ψ] ↔ 𝓢 ⊢ Finset.disj {φ, ψ} := by
  constructor;
  . intro h; exact (C_of_E_mp! $ EDisj₂FDisj!_doubleton) ⨀ h;
  . intro h; exact (C_of_E_mpr! $ EDisj₂FDisj!_doubleton) ⨀ h;

@[simp]
lemma CAFDisjinsertFDisj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ φ ⋎ Γ.disj ➝ (insert φ Γ).disj := by
  apply left_A!_intro;
  . apply right_Fdisj!_intro; simp;
  . apply CFDisjFDisj_of_subset; simp;

@[simp]
lemma CinsertFDisjAFDisj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ (insert φ Γ).disj ➝ φ ⋎ Γ.disj := by
  apply left_Fdisj!_intro;
  simp only [Finset.mem_insert, forall_eq_or_imp, or₁!, true_and];
  intro ψ hψ;
  apply right_A!_intro_right;
  apply right_Fdisj!_intro;
  assumption;

@[simp] lemma CAFdisjFdisjUnion [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ Γ.disj ⋎ Δ.disj ➝ (Γ ∪ Δ).disj := by
  apply left_A!_intro <;>
  . apply CFDisjFDisj_of_subset;
    simp;

@[simp]
lemma CFdisjUnionAFdisj [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢ (Γ ∪ Δ).disj ➝ Γ.disj ⋎ Δ.disj := by
  apply left_Fdisj!_intro;
  simp only [Finset.mem_union];
  rintro ψ (hψ | hψ);
  . apply C!_trans (ψ := Γ.disj) ?_ or₁!;
    apply right_Fdisj!_intro;
    assumption;
  . apply C!_trans (ψ := Δ.disj) ?_ or₂!;
    apply right_Fdisj!_intro;
    assumption;

lemma left_Fdisj!_intro' [DecidableEq F] {Γ : Finset _} (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢ Γ.disj ➝ φ := by
  apply C!_trans ?_ $ left_Disj₂!_intro' (Γ := Γ.toList) (by simpa);
  simp;

end disjunction


section

variable {Γ Δ : Finset F}

lemma CFConj_CDisj!_of_A [DecidableEq F] (hφψ : φ ⋎ ψ ∈ Γ) (hφ : φ ∈ Δ) (hψ : ψ ∈ Δ) : 𝓢 ⊢ Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {φ, ψ});
  . apply C!_trans (ψ := Finset.conj {φ ⋎ ψ}) ?_;
    . apply FConj_DT.mpr;
      suffices ↑{φ ⋎ ψ} *⊢[𝓢] [φ, ψ].disj₂ by simpa using EConj₂_FConj!_doubleton.mp this;
      apply Context.by_axm!;
      simp;
    . apply CFConj_FConj!_of_subset;
      simpa;
  . apply left_Fdisj!_intro;
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq];
    constructor <;>
    . apply right_Fdisj!_intro;
      assumption;

end


section

/-- List version of `CNAKNN!` -/
@[simp]
lemma CNDisj₁Conj₂! [DecidableEq F] : 𝓢 ⊢ ∼⋁Γ ➝ ⋀(Γ.map (∼·)) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    refine C!_trans CNAKNN! ?_;
    apply CKK!_of_C!' ih;

/--- Finset version of `CNAKNN!` -/
@[simp]
lemma CNFdisjFconj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ ∼Γ.disj ➝ (Γ.image (∼·)).conj := by
  apply C!_replace ?_ ?_ $ CNDisj₁Conj₂! (Γ := Γ.toList);
  . apply contra!;
    exact CFDisjDisj₂;
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CConj₂NNDisj₂! [DecidableEq F] : 𝓢 ⊢ ⋀Γ.map (∼·) ➝ ∼⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    apply C!_trans ?_ CKNNNA!;
    apply CKK!_of_C!' ih;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CFconjNNFconj! [DecidableEq F] {Γ : Finset F} : 𝓢 ⊢ (Γ.image (∼·)).conj ➝ ∼Γ.disj := by
  apply C!_replace ?_ ?_ $ CConj₂NNDisj₂! (Γ := Γ.toList);
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;
  . apply contra!;
    simp;

end

namespace Context

end Context

section consistency

lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢ φ) (hn : 𝓢 ⊢ ∼φ) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢ φ ➝ ⊥ := N!_iff_CO!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end consistency

end


end LO.Entailment
