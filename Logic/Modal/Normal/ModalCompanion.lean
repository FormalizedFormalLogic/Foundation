import Logic.Propositional.Superintuitionistic
import Logic.Modal.Normal.Geach
import Logic.Modal.Normal.Strength.Init

namespace LO.Modal.Normal

open LO.Hilbert
open LO.Propositional
open LO.Modal.Normal

variable {α}

/-- Gödel Translation -/
def GTranslation : Superintuitionistic.Formula α → Formula α
  | .atom a  => □(Formula.atom a)
  | .verum   => ⊤
  | .falsum  => ⊥
  | .and p q => (GTranslation p) ⋏ (GTranslation q)
  | .or p q  => (GTranslation p) ⋎ (GTranslation q)
  | .imp p q => □((GTranslation p) ⟶ (GTranslation q))

postfix:75 "ᵍ" => GTranslation

namespace GTranslation

variable {p q : Superintuitionistic.Formula α}

@[simp] lemma atom_def : (Superintuitionistic.Formula.atom a)ᵍ = □(Formula.atom a) := by simp [GTranslation];
@[simp] lemma falsum_def : (⊥ : Superintuitionistic.Formula α)ᵍ = ⊥ := by simp [GTranslation];
@[simp] lemma verum_def : (⊤ : Superintuitionistic.Formula α)ᵍ = ⊤ := by simp [GTranslation];
@[simp] lemma and_def : (p ⋏ q)ᵍ = pᵍ ⋏ qᵍ := by simp [GTranslation];
@[simp] lemma or_def : (p ⋎ q)ᵍ = pᵍ ⋎ qᵍ := by simp [GTranslation];
@[simp] lemma imp_def : (p ⟶ q)ᵍ = □(pᵍ ⟶ qᵍ) := by simp [GTranslation];
@[simp] lemma neg_def' : (~p)ᵍ = □~(p)ᵍ := by simp [GTranslation, NegDefinition.neg];

end GTranslation

def ModalCompanion (pΛ : Propositional.Superintuitionistic.AxiomSet α) (mΛ : AxiomSet α) : Prop := ∀ {p : Superintuitionistic.Formula α}, (∅ ⊢ᴾ[pΛ]! p) ↔ (∅ ⊢ᴹ[mΛ]! pᵍ)

def AxiomSet.ModalDisjunctive (Λ : AxiomSet α) : Prop := ∀ {p q : Formula α}, (∅ ⊢ᴹ[Λ]! □p ⋎ □q) → (∅ ⊢ᴹ[Λ]! p) ∨ (∅ ⊢ᴹ[Λ]! q)

namespace ModalCompanion

variable [Inhabited α] [DecidableEq α] [Encodable α] {p q r : Superintuitionistic.Formula α}

lemma int_axiomFour : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □pᵍ := by
  induction p using Superintuitionistic.Formula.rec' with
  | hatom => simp; apply axiomFour!;
  | hverum => apply dtr'!; apply necessitation!; apply verum!;
  | hfalsum => apply dtr'!; apply efq'!; apply axm!; simp;
  | himp => simp; apply axiomFour!;
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

private lemma embed_int_S4.case_imply₁ : ∅ ⊢ᴹ[𝐒𝟒]! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GTranslation];
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □pᵍ := by apply int_axiomFour;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ qᵍ ⟶ pᵍ) := necessitation! $ by apply imply₁!;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □pᵍ ⟶ □(qᵍ ⟶ pᵍ) := modus_ponens₂'! (by deduct) (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □(qᵍ ⟶ pᵍ) := imp_trans'! (by assumption) (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ □(qᵍ ⟶ pᵍ)) := necessitation! (by assumption);
  exact LogicalStrong.K4_S4 (by assumption)

/-- TODO: prove syntactically -/
private lemma embed_int_S4.case_imply₂ : ∅ ⊢ᴹ[𝐒𝟒]! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GTranslation];
  apply AxiomSet.S4.kripkeCompletes;
  simp [GTranslation, Formula.FrameClassConsequence, Formula.FrameConsequence];
  intro F hF _ w₁ w₂ _ hpqr w₃ hw₂w₃ hpq w₄ hw₃w₄ hp;
  replace hF := by simpa using AxiomSet.S4.frameClassDefinability.mpr (by assumption);
  exact hpqr w₄ (hF.right hw₂w₃ hw₃w₄) hp w₄ (hF.left _) (hpq w₄ (by assumption) hp);

private lemma embed_int_S4.case_conj₃ : ∅ ⊢ᴹ[𝐒𝟒]! ((p ⟶ q ⟶ p ⋏ q))ᵍ := by
  simp only [GTranslation];
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ qᵍ ⟶ pᵍ ⋏ qᵍ) := necessitation! $ by deduct;
  have : ∅ ⊢ᴹ[𝐊𝟒]! □pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ) := (by deduct) ⨀ (by assumption);
  have : ∅ ⊢ᴹ[𝐊𝟒]! pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ) := imp_trans'! (by apply int_axiomFour) (by assumption)
  have : ∅ ⊢ᴹ[𝐊𝟒]! □(pᵍ ⟶ □(qᵍ ⟶ pᵍ ⋏ qᵍ)) := necessitation! (by assumption)
  exact LogicalStrong.K4_S4 (by assumption)

/-- TODO: prove syntactically -/
private lemma embed_int_S4.case_disj₃ : ∅ ⊢ᴹ[𝐒𝟒]! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  apply AxiomSet.S4.kripkeCompletes;
  simp [GTranslation, Formula.FrameClassConsequence, Formula.FrameConsequence];
  intro F hF _ w₁ w₂ _ hp w₃ hw₂₃ hq w₄ hw₃₄ h;
  replace hF := by simpa using AxiomSet.S4.frameClassDefinability.mpr hF;
  cases h with
  | inl h => exact hp _ (hF.right hw₂₃ hw₃₄) h;
  | inr h => exact hq _ (by assumption) h;

open embed_int_S4 in
lemma embed_int_S4 (h : ∅ ⊢ⁱ! p) : ∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! pᵍ := by
  induction h.some with
  | axm => contradiction;
  | eaxm ih =>
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply necessitation!;
    apply efq!;
  | imply₁ p q => exact case_imply₁;
  | imply₂ p q r => exact case_imply₂;
  | conj₃ p q => exact case_conj₃;
  | disj₃ p q r => exact case_disj₃;
  | @modusPonens p q hpq hp ihpq ihp =>
    have h₁ := by simpa using ihpq ⟨hpq⟩;
    have h₂ := by simpa using ihp ⟨hp⟩;
    exact axiomT'! $ axiomK'! h₁ (necessitation! h₂);
  | verum => apply verum!;
  | _ =>
    simp [GTranslation];
    apply necessitation!;
    try first
    | apply conj₁!;
    | apply conj₂!;
    | apply disj₁!;
    | apply disj₂!;

lemma embed_S4_int : (∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! pᵍ) → (∅ ⊢ⁱ! p) := by
  contrapose;
  intro h;
  obtain ⟨γ, MI, w, h⟩ := by simpa [Superintuitionistic.Formula.Intuitionistic.Kripke.Consequence] using not_imp_not.mpr Superintuitionistic.Intuitionistic.Kripke.completes h;
  have : Inhabited γ := ⟨w⟩;
  let M : Modal.Normal.Model γ α := {
    frame := MI.frame,
    val := MI.val
  };
  have MRefl : Reflexive M.frame := by apply MI.refl;
  have MTrans : Transitive M.frame := by apply MI.trans;
  have h₁ : ∀ (q : Superintuitionistic.Formula α) (v), (v ⊩ⁱ[MI] q) ↔ (v ⊩ᴹ[M] qᵍ) := by
    intro q v;
    induction q using Superintuitionistic.Formula.rec' generalizing v with
    | hatom a =>
      constructor;
      . intro _ _ h;
        have := MI.hereditary h;
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

theorem efq_S4 : @ModalCompanion α 𝐄𝐅𝐐 𝐒𝟒 := by
  intro p;
  constructor;
  . apply embed_int_S4;
  . apply embed_S4_int;

theorem int_S4 : (∅ ⊢ⁱ! p) ↔ (∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! pᵍ) := efq_S4

open LO.Propositional.Superintuitionistic.Deduction (glivenko)

lemma embed_Classical_S4 {p : Superintuitionistic.Formula α} : (∅ ⊢ᶜ! p) ↔ (∅ ⊢ᴹ[(𝐒𝟒 : AxiomSet α)]! ◇pᵍ) := by
  constructor;
  . intro h;
    have := glivenko.mpr h;
    have := ModalCompanion.efq_S4.mp this;
    simp only [GTranslation.neg_def'] at this;
    simpa using axiomT'! this;
  . intro h;
    have : ∅ ⊢ᴹ[𝐒𝟒]! □~(□~pᵍ) := by simpa using necessitation! h;
    rw [←GTranslation.neg_def'] at this;
    rw [←GTranslation.neg_def'] at this;
    have := ModalCompanion.efq_S4.mpr this;
    exact glivenko.mp this;

lemma disjunctive_of_modalDisjunctive
  {pΛ : Propositional.Superintuitionistic.AxiomSet α}
  {mΛ : AxiomSet α}
  (hK4 : 𝐊𝟒 ≤ᴸ mΛ)
  (hComp : ModalCompanion pΛ mΛ)
  (hMDisj : mΛ.ModalDisjunctive)
  : pΛ.Disjunctive := by
  simp only [AxiomSet.ModalDisjunctive, Propositional.Superintuitionistic.AxiomSet.Disjunctive];
  intro p q hpq;
  have : ∅ ⊢ᴹ[mΛ]! pᵍ ⋎ qᵍ := by simpa [GTranslation] using hComp.mp hpq;
  have : ∅ ⊢ᴹ[mΛ]! □pᵍ ⋎ □qᵍ := by
    have dp : ∅ ⊢ᴹ[mΛ]! pᵍ ⟶ (□pᵍ ⋎ □qᵍ) := LogicalStrong.deducible hK4 $ imp_trans'! (by apply int_axiomFour) (by apply disj₁!);
    have dq : ∅ ⊢ᴹ[mΛ]! qᵍ ⟶ (□pᵍ ⋎ □qᵍ) := LogicalStrong.deducible hK4 $ imp_trans'! (by apply int_axiomFour) (by apply disj₂!);
    exact disj₃'! dp dq (by assumption);
  cases hMDisj this with
  | inl h => left; exact hComp.mpr h;
  | inr h => right; exact hComp.mpr h;

end ModalCompanion

end LO.Modal.Normal
