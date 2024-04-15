import Logic.Propositional.Intuitionistic
import Logic.Modal.Normal.Strength

namespace LO.Modal.Normal

open LO.Hilbert
open LO.Propositional
open LO.Modal.Normal

variable {α} [DecidableEq α]

/-- Gödel Translation -/
def GTranslation : Intuitionistic.Formula α → Formula α
  | Intuitionistic.Formula.atom a  => □(Formula.atom a)
  | Intuitionistic.Formula.falsum  => ⊥
  | Intuitionistic.Formula.and p q => (GTranslation p) ⋏ (GTranslation q)
  | Intuitionistic.Formula.or p q  => (GTranslation p) ⋎ (GTranslation q)
  | Intuitionistic.Formula.imp p q => □((GTranslation p) ⟶ (GTranslation q))

postfix:75 "ᵍ" => GTranslation

namespace GTranslation

variable {p q : Intuitionistic.Formula α}

@[simp] lemma atom_def : (Intuitionistic.Formula.atom a)ᵍ = □(Formula.atom a) := by simp [GTranslation];
@[simp] lemma falsum_def : (⊥ : Intuitionistic.Formula α)ᵍ = ⊥ := by simp [GTranslation];
@[simp] lemma and_def : (p ⋏ q)ᵍ = pᵍ ⋏ qᵍ := by simp [GTranslation];
@[simp] lemma or_def : (p ⋎ q)ᵍ = pᵍ ⋎ qᵍ := by simp [GTranslation];
@[simp] lemma imp_def : (p ⟶ q)ᵍ = □(pᵍ ⟶ qᵍ) := by simp [GTranslation];
@[simp] lemma neg_def' : (~p)ᵍ = □~(p)ᵍ := by simp [GTranslation, NegDefinition.neg];

end GTranslation

lemma intAxiom4 {p : Intuitionistic.Formula α} : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □pᵍ := by
  induction p using Intuitionistic.Formula.rec' with
  | hatom => simp; apply axiom4!;
  | hfalsum => apply dtr'!; apply efq'!; apply axm!; simp;
  | himp => simp; apply axiom4!;
  | hand p q ihp ihq =>
    apply dtr'!;
    have : {pᵍ ⋏ qᵍ} ⊢ᴹ[𝐊𝟒]! pᵍ ⋏ qᵍ := axm! (by simp);
    have : {pᵍ ⋏ qᵍ} ⊢ᴹ[𝐊𝟒]! □pᵍ := by simpa using modus_ponens'! ihp $ conj₁'! (by assumption);
    have : {pᵍ ⋏ qᵍ} ⊢ᴹ[𝐊𝟒]! □qᵍ := by simpa using modus_ponens'! ihq $ conj₂'! (by assumption);
    have : {pᵍ ⋏ qᵍ} ⊢ᴹ[𝐊𝟒]! □pᵍ ⋏  □qᵍ := conj₃'! (by assumption) (by assumption);
    have : {pᵍ ⋏ qᵍ} ⊢ᴹ[𝐊𝟒]! □(pᵍ ⋏  qᵍ) := collect_box_conj'! (by assumption);
    simpa;
  | hor p q ihp ihq =>
    apply dtr'!;
    have hp : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □(pᵍ ⋎ qᵍ) := dtr'! $ collect_box_disj'! $ disj₁'! $ by simpa using dtl'! ihp;
    have hq : ∅ ⊢ᴹ[𝐊𝟒]! qᵍ ⟶ □(pᵍ ⋎ qᵍ) := dtr'! $ collect_box_disj'! $ disj₂'! $ by simpa using dtl'! ihq;
    have h : {pᵍ ⋎ qᵍ} ⊢ᴹ[𝐊𝟒]! pᵍ ⋎ qᵍ := axm! (by simp);
    simpa using disj₃'! (weakening! (by simp) hp) (weakening! (by simp) hq) h;

variable [Inhabited α] {p q r : Intuitionistic.Formula α}

private lemma embed_Int_S4.case_imply₁ : ∅ ⊢ᴹ[𝐒𝟒]! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GTranslation];
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □pᵍ := by apply intAxiom4;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ qᵍ ⟶ pᵍ) := necessitation! $ by apply imply₁!;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □pᵍ ⟶ □(qᵍ ⟶ pᵍ) := modus_ponens₂'! (by deduct) (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □(qᵍ ⟶ pᵍ) := imp_trans'! (by assumption) (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ □(qᵍ ⟶ pᵍ)) := necessitation! (by assumption);
  exact strong_K4_S4 (by assumption)

/-- TODO: prove syntactically -/
private lemma embed_Int_S4.case_imply₂ : ∅ ⊢ᴹ[𝐒𝟒]! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GTranslation];
  apply AxiomSet.S4.kripkeCompletes;
  simp [GTranslation, Formula.FrameClassConsequence, Formula.FrameConsequence];
  intro F hF _ w₁ w₂ _ hpqr w₃ hw₂w₃ hpq w₄ hw₃w₄ hp;
  replace hF := by simpa using AxiomSet.S4.frameClassDefinability.mpr (by assumption);
  exact hpqr w₄ (hF.right hw₂w₃ hw₃w₄) hp w₄ (hF.left _) (hpq w₄ (by assumption) hp);

private lemma embed_Int_S4.case_conj₃ : ∅ ⊢ᴹ[𝐒𝟒]! ((p ⟶ q ⟶ p ⋏ q))ᵍ := by
  simp only [GTranslation];
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ qᵍ ⟶ pᵍ ⋏ qᵍ) := necessitation! $ by deduct;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ) := (by deduct) ⨀ (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ) := imp_trans'! (by apply intAxiom4) (by assumption)
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ)) := necessitation! (by assumption)
  exact strong_K4_S4 (by assumption)

/-- TODO: prove syntactically -/
private lemma embed_Int_S4.case_disj₃ : ∅ ⊢ᴹ[𝐒𝟒]! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  apply AxiomSet.S4.kripkeCompletes;
  simp [GTranslation, Formula.FrameClassConsequence, Formula.FrameConsequence];
  intro F hF _ w₁ w₂ _ hp w₃ hw₂₃ hq w₄ hw₃₄ h;
  replace hF := by simpa using AxiomSet.S4.frameClassDefinability.mpr hF;
  cases h with
  | inl h => exact hp _ (hF.right hw₂₃ hw₃₄) h;
  | inr h => exact hq _ (by assumption) h;

open embed_Int_S4 in
lemma embed_Int_S4 (h : ∅ ⊢! p) : ∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! pᵍ := by
  induction h.some with
  | axm => contradiction;
  | imply₁ p q => exact case_imply₁;
  | imply₂ p q r => exact case_imply₂;
  | conj₃ p q => exact case_conj₃;
  | disj₃ p q r => exact case_disj₃;
  | @modusPonens p q hpq hp ihpq ihp =>
    have h₁ := by simpa using ihpq ⟨hpq⟩;
    have h₂ := by simpa using ihp ⟨hp⟩;
    exact axiomT'! $ axiomK'! h₁ (necessitation! h₂);
  | _ =>
    simp [GTranslation];
    apply necessitation!;
    try first
    | apply conj₁!;
    | apply conj₂!;
    | apply disj₁!;
    | apply disj₂!;
    | apply efq!;

variable [Encodable α]

lemma embed_S4_Int : (∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! pᵍ) → (∅ ⊢! p) := by
  contrapose;
  intro h;
  obtain ⟨γ, MI, w, h⟩ := by simpa [Intuitionistic.Formula.KripkeConsequence] using not_imp_not.mpr Intuitionistic.Kripke.completes h;
  have : Inhabited γ := ⟨w⟩;
  let M : Modal.Normal.Model γ α := {
    frame := MI.frame,
    val := MI.val
  };
  have MRefl : Reflexive M.frame := by apply MI.refl;
  have MTrans : Transitive M.frame := by apply MI.trans;
  have h₁ : ∀ (q : Intuitionistic.Formula α) (v), (v ⊩[MI] q) ↔ (v ⊩ᴹ[M] qᵍ) := by
    intro q v;
    induction q using Intuitionistic.Formula.rec' generalizing v with
    | hatom a =>
      constructor;
      . intro _ _ h;
        have := MI.herditary h;
        simp_all;
      . intro h;
        have := h v (MRefl v);
        simp_all;
    | _ => simp_all;
  have : ¬(w ⊩ᴹ[M] pᵍ) := (h₁ p w).not.mp h;

  by_contra hC;
  have : ∅ ⊨ᴹ[(𝔽(𝐒𝟒) : FrameClass γ)] pᵍ := AxiomSet.sounds hC;
  simp [Formula.FrameConsequence, Formula.FrameClassConsequence] at this;
  have : w ⊩ᴹ[M] pᵍ := this M.frame (by
    apply AxiomSet.S4.frameClassDefinability.mp;
    constructor <;> assumption;
  ) M.val w;

  contradiction;

/-- a.k.a. Gödel-McKinsey-Tarski Theorem -/
theorem companion_Int_S4 {p : Intuitionistic.Formula α} : (∅ ⊢! p) ↔ (∅ ⊢ᴹ[𝐒𝟒]! pᵍ) := by
  constructor;
  . apply embed_Int_S4;
  . apply embed_S4_Int;

end LO.Modal.Normal
