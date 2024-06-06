import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Deduction
import Logic.Propositional.Superintuitionistic.Classical.Deduction

/-!
  # Maximality of `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫`

  `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫` are maximal in normal modal logic.
-/

namespace LO.Propositional.Superintuitionistic

def toModalFormula : Formula α → Modal.Normal.Formula α
  | .atom a => Modal.Normal.Formula.atom a
  | ⊥ => ⊥
  | ⊤ => ⊤
  | p ⟶ q => (toModalFormula p) ⟶ (toModalFormula q)
  | p ⋏ q => (toModalFormula p) ⋏ (toModalFormula q)
  | p ⋎ q => (toModalFormula p) ⋎ (toModalFormula q)
postfix:75 "ᴹ" => toModalFormula

namespace toModalFormula

variable {p q : Formula α}

@[simp] lemma atom_def (a : α) : (.atom a)ᴹ = Modal.Normal.Formula.atom a := by simp [toModalFormula]
@[simp] lemma bot_def : (⊥ : Formula α)ᴹ = ⊥ := by simp [toModalFormula]
@[simp] lemma top_def : (⊤ : Formula α)ᴹ = ⊤ := by simp [toModalFormula]
@[simp] lemma imp_def : (p ⟶ q)ᴹ = (pᴹ ⟶ qᴹ) := by simp [toModalFormula]
@[simp] lemma conj_def : (p ⋏ q)ᴹ = (pᴹ ⋏ qᴹ) := by simp [toModalFormula]
@[simp] lemma disj_def : (p ⋎ q)ᴹ = (pᴹ ⋎ qᴹ) := by simp [toModalFormula]

end toModalFormula

end LO.Propositional.Superintuitionistic


namespace LO.Modal.Normal

open LO.Propositional

variable {α} [DecidableEq α]

namespace Formula

def toPropFormula (p : Formula α) (_ : p.degree = 0) : Superintuitionistic.Formula α :=
  match p with
  | atom a => Superintuitionistic.Formula.atom a
  | ⊥ => ⊥
  | p ⋏ q => (p.toPropFormula (by simp_all [degree])) ⋏ (q.toPropFormula (by simp_all [degree]))
  | p ⋎ q => (p.toPropFormula (by simp_all [degree])) ⋎ (q.toPropFormula (by simp_all [degree]))
  | p ⟶ q => (p.toPropFormula (by simp_all [degree])) ⟶ (q.toPropFormula (by simp_all [degree]))

@[simp] lemma atom_degree {a : α} : (atom a).degree = 0 := by simp [degree]
@[simp] lemma bot_degree : (⊥ : Formula α).degree = 0 := by simp [degree]
@[simp] lemma top_degree : (⊤ : Formula α).degree = 0 := by simp [degree]

namespace toPropFormula

@[simp] lemma atom_def (a : α) : (atom a).toPropFormula atom_degree = Superintuitionistic.Formula.atom a := by simp [toPropFormula]
@[simp] lemma bot_def : (⊥ : Formula α).toPropFormula bot_degree = ⊥ := by simp [toPropFormula];

end toPropFormula

def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | box p => p.TrivTranslation
  | ⊥ => ⊥
  | p ⟶ q => (p.TrivTranslation) ⟶ (q.TrivTranslation)
  | p ⋏ q => (p.TrivTranslation) ⋏ (q.TrivTranslation)
  | p ⋎ q => (p.TrivTranslation) ⋎ (q.TrivTranslation)
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

@[simp]
lemma degree_zero : pᵀ.degree = 0 := by induction p <;> simp [TrivTranslation, degree, *];

@[simp] lemma atom_def (a : α) : (.atom a)ᵀ = atom a := by simp [TrivTranslation];
@[simp] lemma box_def : (□p)ᵀ = pᵀ := by simp [TrivTranslation];
@[simp] lemma bot_def : (⊥ : Formula α)ᵀ = ⊥ := by simp [TrivTranslation];
@[simp] lemma imp_def : (p ⟶ q)ᵀ = (pᵀ ⟶ qᵀ) := by simp [TrivTranslation];
@[simp] lemma conj_def : (p ⋏ q)ᵀ = (pᵀ ⋏ qᵀ) := by simp [TrivTranslation];
@[simp] lemma disj_def : (p ⋎ q)ᵀ = (pᵀ ⋎ qᵀ) := by simp [TrivTranslation];

def toPropFormula (p : Formula α) : Superintuitionistic.Formula α := pᵀ.toPropFormula (by simp)
postfix:75 "ᵀᴾ" => TrivTranslation.toPropFormula

namespace toPropFormula

variable {p q : Formula α}

@[simp] lemma atom_def : (.atom a)ᵀᴾ = Superintuitionistic.Formula.atom a := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma bot_def : (⊥ : Formula α)ᵀᴾ = ⊥ := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma conj_def : (p ⋏ q)ᵀᴾ = (pᵀᴾ ⋏ qᵀᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma disj_def : (p ⋎ q)ᵀᴾ = (pᵀᴾ ⋎ qᵀᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma imp_def : (p ⟶ q)ᵀᴾ = (pᵀᴾ ⟶ qᵀᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma box_def : (□p)ᵀᴾ = pᵀᴾ := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma neg_def : (~p)ᵀᴾ = ~(pᵀᴾ) := by simp [toPropFormula, Formula.toPropFormula, NegDefinition.neg]

@[simp] lemma back : pᵀᴾᴹ = pᵀ := by induction p using rec' <;> simp [*];

end toPropFormula

end TrivTranslation

@[simp]
def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | box _ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (p.VerTranslation) ⟶ (q.VerTranslation)
  | p ⋏ q => (p.VerTranslation) ⋏ (q.VerTranslation)
  | p ⋎ q => (p.VerTranslation) ⋎ (q.VerTranslation)
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

@[simp] lemma degree_zero : pⱽ.degree = 0 := by induction p <;> simp [VerTranslation, degree, *];

@[simp] lemma atom_def (a : α) : (.atom a)ⱽ = atom a := by simp [TrivTranslation];
@[simp] lemma box_def : (□p)ⱽ = ⊤ := by simp [TrivTranslation];
@[simp] lemma bot_def : (⊥ : Formula α)ⱽ = ⊥ := by simp [TrivTranslation];
@[simp] lemma top_def : (⊤ : Formula α)ⱽ = (~⊥) := by simp [TrivTranslation, NegDefinition.neg];
@[simp] lemma imp_def : (p ⟶ q)ⱽ = (pⱽ ⟶ qⱽ) := by simp [TrivTranslation];
@[simp] lemma conj_def : (p ⋏ q)ⱽ = (pⱽ ⋏ qⱽ) := by simp [TrivTranslation];
@[simp] lemma disj_def : (p ⋎ q)ⱽ = (pⱽ ⋎ qⱽ) := by simp [TrivTranslation];

@[simp] def toPropFormula (p : Formula α) : Superintuitionistic.Formula α := pⱽ.toPropFormula (by simp)
postfix:75 "ⱽᴾ" => VerTranslation.toPropFormula

namespace toPropFormula

variable {p q : Formula α}

@[simp] lemma atom_def : (.atom a)ⱽᴾ = Superintuitionistic.Formula.atom a := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma bot_def : (⊥ : Formula α)ⱽᴾ = ⊥ := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma top_def : (⊤ : Formula α)ⱽᴾ = (~⊥) := by simp [toPropFormula, Formula.toPropFormula, NegDefinition.neg]
@[simp] lemma conj_def : (p ⋏ q)ⱽᴾ = (pⱽᴾ ⋏ qⱽᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma disj_def : (p ⋎ q)ⱽᴾ = (pⱽᴾ ⋎ qⱽᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma imp_def : (p ⟶ q)ⱽᴾ = (pⱽᴾ ⟶ qⱽᴾ) := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma box_def : (□p)ⱽᴾ = ⊤ⱽᴾ := by simp [toPropFormula, Formula.toPropFormula]
@[simp] lemma neg_def : (~p)ⱽᴾ = ~(pⱽᴾ) := by simp [toPropFormula, Formula.toPropFormula, NegDefinition.neg]

end toPropFormula
end VerTranslation

end Formula

open Hilbert

variable {Λ : AxiomSet α} {Γ} {p : Formula α}

def Deduction.ofTriv : Hilbert.Triv (· ⊢ᴹ[(𝐓𝐫𝐢𝐯 : AxiomSet α)] ·) where
  K _ _ _ := Deduction.maxm $ (by simp);
  T _ _ := Deduction.maxm $ (by simp);
  Tc _ _ := Deduction.maxm $ (by simp);

def Deduction.ofVer : Hilbert.Ver (· ⊢ᴹ[(𝐕𝐞𝐫 : AxiomSet α)] ·) where
  K _ _ _ := Deduction.maxm $ (by simp);
  Verum _ _ := Deduction.maxm $ (by simp);

lemma deducible_iff_trivTranslation : Γ ⊢ᴹ[𝐓𝐫𝐢𝐯]! p ⟷ pᵀ := by
  have := @Deduction.ofTriv;
  induction p using Formula.rec' with
  | hbox p ih => exact iff_trans'! (iff_symm'! $ boxtriv!) ih;
  | hatom _ => apply iff_id!
  | hfalsum => apply iff_id!
  | himp _ _ ih₁ ih₂ => exact imp_iff'! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact conj_iff'! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact disj_iff'! ih₁ ih₂

lemma deducible_iff_verTranslation : Γ ⊢ᴹ[𝐕𝐞𝐫]! p ⟷ pⱽ := by
  have := @Deduction.ofVer;
  induction p using Formula.rec' with
  | hbox =>
    apply iff_intro'!;
    . exact imply₁'! verum!
    . exact imply₁'! boxarbitary!;
  | hatom _ => apply iff_id!
  | hfalsum => apply iff_id!
  | himp _ _ ih₁ ih₂ => exact imp_iff'! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact conj_iff'! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact disj_iff'! ih₁ ih₂

private lemma of_classical_aux (hΓ : Γ = ∅) {p : Superintuitionistic.Formula α} : (Γ ⊢ᶜ! p) → (∅ ⊢ᴹ[Λ]! pᴹ) := by
  intro h;
  induction h.some with
  | axm h => simp_all;
  | eaxm ih =>
    simp_all;
    obtain ⟨p, e⟩ := ih;
    subst e;
    apply dne!;
  | modusPonens h₁ h₂ ih₁ ih₂ =>
    subst hΓ;
    simp_all;
    replace h₁ := ih₁ h₁;
    replace h₂ := ih₂ h₂;
    simpa using modus_ponens'! h₁ h₂;
  | _ =>
    simp;
    try first
    | apply verum!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply imply₁!;
    | apply imply₂!;

lemma of_classical {p : Superintuitionistic.Formula α} : (∅ ⊢ᶜ! p) → (∅ ⊢ᴹ[Λ]! pᴹ) := of_classical_aux rfl

private lemma iff_Triv_classical_aux (hΓ : Γ = ∅) : (Γ ⊢ᴹ[𝐓𝐫𝐢𝐯]! p) ↔ (∅ ⊢ᶜ! pᵀᴾ) := by
  constructor;
  . intro h;
    induction h.some with
    | axm h => simp_all;
    | maxm a =>
      rcases a with (hK | hT) | hTr;
      . obtain ⟨p, q, h⟩ := hK; subst h;
        simp [axiomK, Formula.TrivTranslation.toPropFormula, Formula.toPropFormula];
        apply imp_id!;
      . obtain ⟨p, h⟩ := hT; subst h;
        simp [axiomT, Formula.TrivTranslation.toPropFormula, Formula.toPropFormula];
        apply imp_id!;
      . obtain ⟨p, h⟩ := hTr; subst h;
        simp [axiomK, Formula.TrivTranslation.toPropFormula, Formula.toPropFormula];
        apply imp_id!;
    | modus_ponens h₁ h₂ ih₁ ih₂ =>
      simp_all;
      have ⟨hΓ₁, hΓ₂⟩ := hΓ;
      subst hΓ₁ hΓ₂;
      simpa using modus_ponens'! (ih₁ h₁) (ih₂ h₂);
    | necessitation h ih =>
      simp_all;
      apply ih;
      assumption;
    | _ =>
      simp_all;
      try first
      | apply imp_id!;
      | apply imply₁!;
      | apply imply₂!;
      | apply conj₁!;
      | apply conj₂!;
      | apply conj₃!;
      | apply disj₁!;
      | apply disj₂!;
      | apply disj₃!;
      | apply dne!;
  . intro h;
    subst hΓ;
    have d₁ : ∅ ⊢ᴹ[𝐓𝐫𝐢𝐯]! pᵀ ⟶ p := iff_mpr'! deducible_iff_trivTranslation;
    have d₂ : ∅ ⊢ᴹ[𝐓𝐫𝐢𝐯]! pᵀ := by simpa using of_classical h;
    simpa using modus_ponens'! d₁ d₂;

theorem iff_Triv_classical : (∅ ⊢ᴹ[𝐓𝐫𝐢𝐯]! p) ↔ (∅ ⊢ᶜ! pᵀᴾ) := iff_Triv_classical_aux rfl

lemma iff_Ver_classical_aux (hΓ : Γ = ∅) : (Γ ⊢ᴹ[𝐕𝐞𝐫]! p) ↔ (∅ ⊢ᶜ! pⱽᴾ) := by
  constructor;
  . intro h;
    induction h.some with
    | axm h => simp_all;
    | maxm a =>
      rcases a with (hK | hVer)
      . obtain ⟨p, q, h⟩ := hK; subst h;
        simp [axiomK];
        apply imply₁!;
      . obtain ⟨p, h⟩ := hVer; subst h;
        simp [axiomVerum];
        exact imp_id!;
    | modus_ponens h₁ h₂ ih₁ ih₂ =>
      simp_all;
      have ⟨hΓ₁, hΓ₂⟩ := hΓ;
      subst hΓ₁ hΓ₂;
      simpa using modus_ponens'! (ih₁ h₁) (ih₂ h₂);
    | necessitation =>
      simp_all [Formula.toPropFormula];
      exact imp_id!;
    | _ =>
      simp_all;
      try first
      | apply imp_id!;
      | apply imply₁!;
      | apply imply₂!;
      | apply conj₁!;
      | apply conj₂!;
      | apply conj₃!;
      | apply disj₁!;
      | apply disj₂!;
      | apply disj₃!;
      | apply dne!;
  . intro h;
    subst hΓ;
    have d₁ : ∅ ⊢ᴹ[𝐕𝐞𝐫]! pⱽ ⟶ p := iff_mpr'! deducible_iff_verTranslation;
    have d₂ : ∅ ⊢ᴹ[𝐕𝐞𝐫]! pⱽ := by sorry; -- simpa using of_classical h;
    simpa using modus_ponens'! d₁ d₂;

theorem iff_Ver_classical : (∅ ⊢ᴹ[𝐕𝐞𝐫]! p) ↔ (∅ ⊢ᶜ! pⱽᴾ) := iff_Ver_classical_aux rfl

example : (∅ ⊢ᴹ[𝐓𝐫𝐢𝐯]! axiomL p) := by
  apply iff_Triv_classical.mpr;
  simp;
  sorry;

example : (∅ ⊢ᴹ[𝐕𝐞𝐫]! (~(□⊥) : Formula α)) := by
  apply iff_Ver_classical.mpr;
  simp;
  sorry;


end LO.Modal.Normal
