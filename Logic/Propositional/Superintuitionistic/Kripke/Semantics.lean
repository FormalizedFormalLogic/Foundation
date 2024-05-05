import Logic.Vorspiel.BinaryRelations
import Logic.Logic.Semantics
import Logic.Propositional.Superintuitionistic.Formula

namespace LO.Propositional.Superintuitionistic

namespace Kripke

set_option linter.unusedVariables false in
abbrev Frame (W α : Type*) := W → W → Prop

abbrev FrameClass (W α) := Set (Frame W α)

abbrev Valuation (W α) := W → α → Prop

structure Model (𝔽 : FrameClass W α) where
  frame : Frame W α
  frame_prop : frame ∈ 𝔽
  valuation : Valuation W α
  hereditary : ∀ {w₁ w₂}, (frame w₁ w₂) → ∀ a, (valuation w₁ a) → (valuation w₂ a)

section

variable (W α : Type*)

@[simp] def FrameClass.Intuitionistic := { F : Frame W α | Transitive F ∧ Reflexive F }
notation "𝐈𝐧𝐭" => FrameClass.Intuitionistic

-- @[simp] def FrameClass.Classical := { F : Frame W α | Euclidean F ∧ Reflexive F }
@[simp] def FrameClass.Classical := { F : Frame W α | Extensive F }
notation "𝐂𝐥" => FrameClass.Classical

open FrameClass
variable {W α}

/-
example : Classical W α ⊆ Intuitionistic W α := by
  simp [FrameClass.Intuitionistic, FrameClass.Classical];
  intro F hEucl hRefl;
  exact ⟨
    trans_of_refl_eucl hRefl hEucl,
    by simpa;
  ⟩;
-/

end

end Kripke

open Kripke

def Formula.Kripke.Satisfies (𝔽 : FrameClass W α) (M : Model 𝔽) (w : W) : Formula α → Prop
  | atom a => M.valuation w a
  | ⊤      => True
  | ⊥      => False
  | p ⋏ q  => Satisfies 𝔽 M w p ∧ Satisfies 𝔽 M w q
  | p ⋎ q  => Satisfies 𝔽 M w p ∨ Satisfies 𝔽 M w q
  | p ⟶ q => ∀ {w'}, (M.frame w w') → (¬Satisfies 𝔽 M w' p ∨ Satisfies 𝔽 M w' q)

instance {𝔽 : FrameClass W α} : Semantics (Formula α) ((Model 𝔽) × W) := ⟨fun ⟨M, w⟩ ↦ Formula.Kripke.Satisfies 𝔽 M w⟩

open Formula.Kripke

namespace Formula.Kripke.Satisfies

variable {𝔽 : FrameClass W α} {M : Model 𝔽}

lemma iff_models : (M, w) ⊧ p ↔ Formula.Kripke.Satisfies 𝔽 M w p := iff_of_eq rfl

instance : Semantics.Top ((Model 𝔽) × W) where
  realize_top := by simp [iff_models, Satisfies];

instance : Semantics.Bot ((Model 𝔽) × W) where
  realize_bot := by simp [iff_models, Satisfies];

instance : Semantics.And ((Model 𝔽) × W) where
  realize_and := by simp [iff_models, Satisfies];

instance : Semantics.Or ((Model 𝔽) × W) where
  realize_or := by simp [iff_models, Satisfies];

@[simp] lemma imp_def : ((M, w) ⊧ p ⟶ q) ↔ ∀ {w'}, (M.frame w w') → ((M, w') ⊧ p) → ((M, w') ⊧ q) := by simp [iff_models, Satisfies, imp_iff_not_or];

@[simp] lemma neg_def : ((M, w) ⊧ ~p) ↔ ∀ {w'}, (M.frame w w') → ¬((M, w') ⊧ p) := by simp [NegDefinition.neg];

lemma hereditary (hTrans : 𝔽 ⊆ { F : Frame W α | Transitive F }) (hw : M.frame w w') : (M, w) ⊧ p → (M, w') ⊧ p := by
  induction p using Formula.rec' with
  | hatom => apply M.hereditary hw;
  | himp =>
    simp_all [Satisfies];
    intro hpq v hv;
    have hTrans : Transitive M.frame := by simpa using hTrans M.frame_prop;
    exact hpq $ hTrans hw hv;
  | hor => simp_all [Satisfies]; tauto;
  | _ => simp_all [Satisfies];

lemma hereditary_int {M : Model (𝐈𝐧𝐭 W α)} {w w' : W} {p : Formula α} (hw : M.frame w w') : (M, w) ⊧ p → (M, w') ⊧ p := by
  apply hereditary (by simp_all) hw;

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel {𝔽 : FrameClass W α} (M : Model 𝔽) (p : Formula α) := ∀ w : W, (M, w) ⊧ p

instance {𝔽 : FrameClass W α} : Semantics (Formula α) (Model 𝔽) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace Formula.Kripke.ValidOnModel

lemma iff_models : M ⊧ p ↔ Formula.Kripke.ValidOnModel M p := iff_of_eq rfl

variable {𝔽 : FrameClass W α} (hTrans : 𝔽 ⊆ { F | Transitive F }) (hRefl : 𝔽 ⊆ { F | Reflexive F })
variable {M : Model 𝔽} {p q r : Formula α}

lemma verum : M ⊧ ⊤ := by simp_all [iff_models, ValidOnModel];

lemma conj₁ : M ⊧ p ⋏ q ⟶ p := by simp_all [iff_models, ValidOnModel];

lemma conj₂ : M ⊧ p ⋏ q ⟶ q := by simp_all [iff_models, ValidOnModel];

lemma conj₃ : M ⊧ p ⟶ q ⟶ p ⋏ q := by
  simp_all [iff_models, ValidOnModel];
  intro w₁ w₂ _ hp w₃ hw₂₃ _;
  exact Kripke.Satisfies.hereditary hTrans hw₂₃ hp;

lemma disj₁ : M ⊧ p ⟶ p ⋎ q := by simp_all [iff_models, ValidOnModel];

lemma disj₂ : M ⊧ q ⟶ p ⋎ q := by simp_all [iff_models, ValidOnModel];

lemma disj₃ : M ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by
  simp_all only [iff_models, ValidOnModel, Satisfies.imp_def, Semantics.Or.realize_or];
  intro w₁ w₂ _ hpr w₃ hw₂₃ hqr w₄ hw₃₄ hpq;
  cases hpq with
  | inl hp => exact hpr (hTrans M.frame_prop hw₂₃ hw₃₄) hp;
  | inr hq => exact hqr hw₃₄ hq;

lemma imply₁ : M ⊧ p ⟶ q ⟶ p := by
  simp_all [iff_models, ValidOnModel];
  intro w₁ w₂ _ hp w₃ hw₂₃ _;
  exact Kripke.Satisfies.hereditary hTrans hw₂₃ hp;

lemma imply₂ : M ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by
  simp_all only [iff_models, ValidOnModel, Satisfies.imp_def];
  intro w₁ w₂ _ hpqr w₃ hw₂₃ hpq w₄ hw₃₄ hp;
  exact hpqr (hTrans M.frame_prop hw₂₃ hw₃₄) hp (hRefl M.frame_prop w₄) (hpq hw₃₄ hp);

lemma mdp (hpq : M ⊧ p ⟶ q) (hp : M ⊧ p) : M ⊧ q := by
  simp_all [iff_models, ValidOnModel];
  intro w;
  exact hpq w (hRefl M.frame_prop w);

section Axioms

lemma efq : M ⊧ ⊥ ⟶ p := by simp_all [iff_models, ValidOnModel];

lemma lem (hExt : 𝔽 ⊆ { F | Extensive F }) : M ⊧ p ⋎ ~p := by
  simp_all [iff_models, ValidOnModel];
  intro w;
  by_cases h : (M, w) ⊧ p
  . left; assumption;
  . right;
    intro w' hww';
    rw [←hExt M.frame_prop hww'];
    assumption;

end Axioms

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass W α) (p : Formula α) := ∀ {M : Model 𝔽}, M ⊧ p

instance : Semantics (Formula α) (FrameClass W α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFrameClass

lemma iff_models : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl

variable {𝔽 : FrameClass W α} (hTrans : 𝔽 ⊆ { F : Frame W α | Transitive F }) (hRefl : 𝔽 ⊆ { F : Frame W α | Reflexive F })

@[simp] lemma verum : 𝔽 ⊧ ⊤ := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.verum;

@[simp] lemma conj₁ : 𝔽 ⊧ p ⋏ q ⟶ p := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.conj₁;

@[simp] lemma conj₂ : 𝔽 ⊧ p ⋏ q ⟶ q := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.conj₂;

lemma conj₃ : 𝔽 ⊧ p ⟶ q ⟶ p ⋏ q := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.conj₃ (by simp_all);

@[simp] lemma disj₁ : 𝔽 ⊧ p ⟶ p ⋎ q := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.disj₁;

@[simp] lemma disj₂ : 𝔽 ⊧ q ⟶ p ⋎ q := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.disj₂;

lemma disj₃ : 𝔽 ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.disj₃ (by simp_all);

lemma imply₁ : 𝔽 ⊧ p ⟶ q ⟶ p := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.imply₁ (by simp_all);

lemma imply₂ : 𝔽 ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.imply₂ (by simp_all) (by simp_all);

@[simp] lemma efq : 𝔽 ⊧ ⊥ ⟶ p := by simp_all [ValidOnFrameClass, iff_models]; intros; apply ValidOnModel.efq;

lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  simp_all [ValidOnFrameClass, iff_models];
  intros;
  exact ValidOnModel.mdp hRefl hpq hp;

end Formula.Kripke.ValidOnFrameClass

end LO.Propositional.Superintuitionistic
