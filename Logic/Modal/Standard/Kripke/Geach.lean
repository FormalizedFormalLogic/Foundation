import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Reducible

namespace LO.Modal.Standard


open System
open System.Axioms (Geach)

variable {α : Type u}

def GeachConfluent (t : Geach.Taple) (R : α → α → Prop) := ∀ {x y z : α}, (RelItr R t.i x y) ∧ (RelItr R t.j x z) → ∃ u, (RelItr R t.m y u) ∧ (RelItr R t.n z u)

namespace GeachConfluent

variable {R : α → α → Prop}

@[simp]
lemma serial_def : (GeachConfluent ⟨0, 0, 1, 1⟩ R) ↔ Serial R := by simp [GeachConfluent, Symmetric]; aesop;

@[simp]
lemma reflexive_def : (GeachConfluent ⟨0, 0, 1, 0⟩ R) ↔ Reflexive R := by simp [GeachConfluent, Reflexive];

@[simp]
lemma symmetric_def : (GeachConfluent ⟨0, 1, 0, 1⟩ R) ↔ Symmetric R := by simp [GeachConfluent, Symmetric]; aesop;

@[simp]
lemma transitive_def : (GeachConfluent ⟨0, 2, 1, 0⟩ R) ↔ Transitive R := by simp [GeachConfluent, Transitive]; aesop;

@[simp]
lemma euclidean_def : (GeachConfluent ⟨1, 1, 0, 1⟩ R) ↔ Euclidean R := by simp [GeachConfluent, Euclidean];

@[simp]
lemma confluent_def : (GeachConfluent ⟨1, 1, 1, 1⟩ R) ↔ Confluent R := by simp [GeachConfluent, Confluent];

@[simp]
lemma extensive_def : (GeachConfluent ⟨0, 1, 0, 0⟩ R) ↔ Extensive R := by
  simp [GeachConfluent, Extensive];
  constructor;
  . intro h x y Rxy;
    have := h rfl Rxy;
    subst_vars;
    trivial;
  . intro h x y z Exy Rxz;
    have := h Rxz;
    subst_vars;
    trivial;

@[simp]
lemma functional_def : (GeachConfluent ⟨1, 1, 0, 0⟩ R) ↔ Functional R := by simp [GeachConfluent, Functional]; aesop

@[simp]
lemma dense_def : (GeachConfluent ⟨0, 1, 2, 0⟩ R)  ↔ Dense R := by simp [GeachConfluent, Dense]; aesop;

@[simp]
lemma satisfies_eq : GeachConfluent (α := α) t (· = ·) := by simp [GeachConfluent];

end GeachConfluent


def MultiGeachConfluent (ts : List Geach.Taple) (R : α → α → Prop) : Prop :=
  match ts with
  | [] => True
  | t :: ts => (GeachConfluent t R) ∧ (MultiGeachConfluent ts R)

namespace MultiGeachConfluent

@[simp]
lemma satisfies_eq : MultiGeachConfluent (α := α) ts (· = ·) := by
  induction ts <;> simp_all [MultiGeachConfluent];

end MultiGeachConfluent


namespace Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]


section

lemma TerminalFrame.geach_confluent : GeachConfluent t (terminalFrame.Rel') := by
  simp [GeachConfluent];
  intro x y z Rxy Rxz;
  replace Rxy := terminalFrame.iff_relItr'.mp Rxy;
  replace Rxz := terminalFrame.iff_relItr'.mp Rxz;
  use x; subst_vars;
  constructor <;> { apply terminalFrame.iff_relItr'.mpr; rfl };

lemma TerminalFrame.multi_geach_confluent : MultiGeachConfluent ts (terminalFrame.Rel') := by
  induction ts with
  | nil => simp [MultiGeachConfluent];
  | cons t ts ih =>
    simp [MultiGeachConfluent];
    constructor;
    . exact TerminalFrame.geach_confluent;
    . exact ih;

abbrev GeachConfluentFrameClass (t : Geach.Taple) : FrameClass := { F | (GeachConfluent t) F }

lemma GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass.{0} t).Nonempty := by
  use terminalFrame
  exact TerminalFrame.geach_confluent;


abbrev MultiGeachConfluentFrameClass (ts : List Geach.Taple) : FrameClass := { F | (MultiGeachConfluent ts) F }

lemma MultiGeachConfluentFrameClass.nonempty : (MultiGeachConfluentFrameClass.{0} ts).Nonempty := by
  use terminalFrame
  exact TerminalFrame.multi_geach_confluent;


abbrev ReflexiveFrameClass : FrameClass := { F | Reflexive F }

abbrev SerialFrameClass : FrameClass := { F | Serial F }

abbrev TransitiveFrameClass : FrameClass := { F | Transitive F }

abbrev ReflexiveEuclideanFrameClass : FrameClass := { F | Reflexive F ∧ Euclidean F }

abbrev EquivalenceFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }

abbrev PreorderFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }

abbrev ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }

end

section Definability

@[simp]
lemma MultiGeachConfluentFrameClass.def_nil : MultiGeachConfluentFrameClass [] = AllFrameClass := by rfl;


open Formula (atom Kripke.Satisfies)
open Formula.Kripke.Satisfies (multibox_def multidia_def)

variable [Inhabited α]

lemma axiomGeach_defines : 𝗴𝗲(t).DefinesKripkeFrameClass (α := α) (GeachConfluentFrameClass t) := by
  intro F;
  constructor;
  . rintro h x y z ⟨hi, hj⟩;
    let M : Model α := { Frame := F, Valuation := λ v _ => y ≺^[t.m] v };
    simp at h;
    have him_x : Kripke.Satisfies M x (◇^[t.i](□^[t.m](atom default))) := by
      apply Kripke.Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . exact hi;
      . apply Kripke.Satisfies.multibox_def.mpr; aesop;
    have hjn_x : Kripke.Satisfies M x (□^[t.j](◇^[t.n](atom default))) := h (Formula.atom default) M.Valuation x him_x;
    have hn_z : Kripke.Satisfies M z (◇^[t.n](atom default)) := Kripke.Satisfies.multibox_def.mp hjn_x hj;
    obtain ⟨u, hzu, hyu⟩ := Kripke.Satisfies.multidia_def.mp hn_z;
    use u;
    exact ⟨hyu, hzu⟩;
  . simp [AxiomSet.Geach, Axioms.Geach, Kripke.Satisfies];
    intro h p V x him;
    apply multibox_def.mpr;
    intro z rxz;
    apply multidia_def.mpr;
    obtain ⟨y, rxy, hbp⟩ := multidia_def.mp him;
    obtain ⟨u, ryu, rzu⟩ := h ⟨rxy, rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (multibox_def.mp hbp) ryu;


instance : System.Consistent (𝝂𝗴𝗲(t) : DeductionParameter α) := consistent_of_defines axiomGeach_defines GeachConfluentFrameClass.nonempty


lemma axiomMultiGeach_defines : 𝗚𝗲(ts).DefinesKripkeFrameClass (α := α) (MultiGeachConfluentFrameClass ts) := by
  induction ts with
  | nil => simp [AxiomSet.DefinesKripkeFrameClass];
  | cons t ts ih =>
    intro F;
    simp_all only [Semantics.RealizeSet.union_iff, AxiomSet.MultiGeach.iff_cons];
    constructor;
    . rintro ⟨ht, hts⟩;
      constructor;
      . exact axiomGeach_defines.mp ht;
      . exact ih.mp hts;
    . rintro ⟨ht, hts⟩;
      constructor;
      . exact axiomGeach_defines.mpr ht;
      . exact ih.mpr hts;

private def instGeachLogicDefinability
  {Λ : DeductionParameter α} [geach : Λ.IsGeach]
  (𝔽 : FrameClass) (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Λ.DefinesKripkeFrameClass 𝔽 := by
  simp [DeductionParameter.DefinesKripkeFrameClass];
  nth_rw 1 [geach.char];
  rw [←(Set.univ_inter 𝔽)];
  rw [h𝔽];
  exact AxiomSet.DefinesKripkeFrameClass.union axiomK_defines axiomMultiGeach_defines;

lemma S4_defines : 𝐒𝟒.DefinesKripkeFrameClass (α := α) PreorderFrameClass := instGeachLogicDefinability PreorderFrameClass (by
  simp_all [PreorderFrameClass, PreorderFrameClass];
  apply Set.eq_of_subset_of_subset <;> simp [MultiGeachConfluent];
)


instance : System.Consistent (𝐆𝐞(ts) : DeductionParameter α) := consistent_of_defines axiomMultiGeach_defines MultiGeachConfluentFrameClass.nonempty

instance {Λ : DeductionParameter α} [geach : Λ.IsGeach] : System.Consistent Λ := by rw [geach.char]; infer_instance;

instance : System.Consistent (𝐒𝟒 : DeductionParameter α) := inferInstance

instance : System.Consistent (𝐒𝟓 : DeductionParameter α) := inferInstance

end Definability


section Soundness

private lemma instGeachLogicSoundAux
  {Λ : DeductionParameter α} [geach : Λ.IsGeach] {𝔽 : FrameClass}
  (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Sound Λ 𝔽# := by
    rw [geach.char, h𝔽];
    apply sound_of_defines (α := α) (Ax := 𝗚𝗲(geach.taples));
    exact axiomMultiGeach_defines;

instance sound_KD : Sound (𝐊𝐃 : DeductionParameter α) SerialFrameClass# := instGeachLogicSoundAux

instance sound_KT : Sound (𝐊𝐓 : DeductionParameter α) ReflexiveFrameClass# := instGeachLogicSoundAux

instance sound_KTB : Sound (𝐊𝐓𝐁 : DeductionParameter α) ReflexiveSymmetricFrameClass# := instGeachLogicSoundAux

instance sound_K4 : Sound (𝐊𝟒 : DeductionParameter α) TransitiveFrameClass# := instGeachLogicSoundAux

instance sound_S4 : Sound (𝐒𝟒 : DeductionParameter α) PreorderFrameClass# := instGeachLogicSoundAux

instance sound_S5 : Sound (𝐒𝟓 : DeductionParameter α) ReflexiveEuclideanFrameClass# := instGeachLogicSoundAux

instance sound_KT4B : Sound (𝐊𝐓𝟒𝐁  : DeductionParameter α) EquivalenceFrameClass# := instGeachLogicSoundAux

end Soundness


section Completeness

open Theory MaximalConsistentTheory CanonicalFrame
open DeductionParameter (Normal)

variable {Ax : AxiomSet α} [System.Consistent (𝝂Ax)]

lemma geachConfluent_CanonicalFrame (h : 𝗴𝗲(t) ⊆ Ax) : GeachConfluent t (CanonicalFrame 𝝂Ax):= by
  rintro Ω₁ Ω₂ Ω₃ h;
  have ⟨r₁₂, r₁₃⟩ := h; clear h;
  have ⟨Ω, hΩ⟩ := lindenbaum (Λ := 𝝂Ax) (T := □''⁻¹^[t.m]Ω₂.theory ∪ □''⁻¹^[t.n]Ω₃.theory) $ by
    apply intro_union_consistent;
    intro Γ Δ hΓ hΔ hC;

    replace hΓ : ∀ p ∈ Γ, □^[t.m]p ∈ Ω₂.theory := by simpa using hΓ;
    have hΓconj : □^[t.m]⋀Γ ∈ Ω₂.theory := iff_mem_multibox_conj.mpr hΓ;

    replace hΔ : ∀ p ∈ Δ, □^[t.n]p ∈ Ω₃.theory := by simpa using hΔ;
    have : □^[t.n]⋀Δ ∈ Ω₃.theory := iff_mem_multibox_conj.mpr hΔ;

    have : □^[t.j](◇^[t.n]⋀Γ) ∈ Ω₁.theory := iff_mem_imp.mp
      (membership_iff.mpr $ Context.of! $ Normal.maxm! (by aesop))
      (multiframe_def_multidia.mp r₁₂ hΓconj)
    have : ◇^[t.n]⋀Γ ∈ Ω₃.theory := multiframe_def_multibox.mp r₁₃ this;

    have : 𝝂Ax ⊢! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ⟶ ⊥ := by {
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show 𝝂Ax ⊢! □^[t.n]⋀Δ ⟶ □^[t.n](~⋀Γ) by exact imply_multibox_distribute'! $ contra₁'! $ imp_trans''! (and_imply_iff_imply_imply'!.mp hC) (and₂'! neg_equiv!))
        (show 𝝂Ax ⊢! □^[t.n](~⋀Γ) ⟶ (◇^[t.n]⋀Γ) ⟶ ⊥ by exact imp_trans''! (contra₁'! $ and₁'! $ multidia_duality!) (and₁'! neg_equiv!));
    }
    have : 𝝂Ax ⊬! □^[t.n]⋀Δ ⋏ ◇^[t.n]⋀Γ ⟶ ⊥ := by simpa using (def_consistent.mp Ω₃.consistent) (Γ := [□^[t.n]⋀Δ, ◇^[t.n]⋀Γ]) (by simp_all)

    contradiction;

  use Ω; simp only [Set.union_subset_iff] at hΩ;
  constructor;
  . apply multiframe_def_multibox.mpr; apply hΩ.1;
  . apply multiframe_def_multibox.mpr; apply hΩ.2;

lemma multiGeachConfluent_CanonicalFrame (h : 𝗚𝗲(ts) ⊆ Ax) : MultiGeachConfluent ts (CanonicalFrame 𝝂Ax) := by
  induction ts with
  | nil => simp [MultiGeachConfluent];
  | cons t ts ih =>
    dsimp only [MultiGeachConfluent];
    constructor;
    . apply geachConfluent_CanonicalFrame;
      simp_all;
    . apply ih;
      simp_all;

private instance instMultiGeachComplete : Complete (𝝂𝗚𝗲(ts) : DeductionParameter.{u} α) (MultiGeachConfluentFrameClass.{u} ts)# :=
  instComplete_of_mem_canonicalFrame $ multiGeachConfluent_CanonicalFrame (by rfl)

instance {Λ : DeductionParameter α} [g : Λ.IsGeach] : Complete Λ (MultiGeachConfluentFrameClass.{u} g.taples)# := by
  convert instMultiGeachComplete (α := α);
  exact g.char;

private def instGeachLogicCompleteAux {Λ : DeductionParameter α} [geach : Λ.IsGeach]
  {𝔽 : FrameClass.Dep.{u, u} α} (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Complete Λ 𝔽 := by
    convert instMultiGeachComplete.{u} (α := α);
    exact geach.char;

instance : Complete (𝐊𝐓 : DeductionParameter α) ReflexiveFrameClass.{u}# := instGeachLogicCompleteAux

instance KT_complete : Complete (𝐊𝐓 : DeductionParameter α) ReflexiveFrameClass.{u}# := instGeachLogicCompleteAux

instance KTB_complete : Complete (𝐊𝐓𝐁 : DeductionParameter α) ReflexiveSymmetricFrameClass.{u}# := instGeachLogicCompleteAux

instance S4_complete : Complete (𝐒𝟒 : DeductionParameter α) PreorderFrameClass.{u}# := instGeachLogicCompleteAux

instance S5_complete : Complete (𝐒𝟓 : DeductionParameter α) ReflexiveEuclideanFrameClass.{u}# := instGeachLogicCompleteAux

instance KT4B_complete : Complete (𝐊𝐓𝟒𝐁 : DeductionParameter α) EquivalenceFrameClass.{u}# := instGeachLogicCompleteAux

end Completeness

end Kripke


section Reducible

variable [Inhabited α] [DecidableEq α]

open Kripke
open Formula (atom)
open Formula.Kripke


theorem KD_weakerThan_KT : (𝐊𝐃 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by
  apply reducible_of_subset_FrameClass (α := α) SerialFrameClass ReflexiveFrameClass;
  simp_all [serial_of_refl];

theorem KD_strictlyWeakerThan_KT : (𝐊𝐃 : DeductionParameter α) <ₛ 𝐊𝐓 := by
  constructor;
  . apply KD_weakerThan_KT;
  . simp [weakerThan_iff];
    use (□(atom default) ⟶ (atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply sound_KD.not_provable_of_countermodel;
      simp [FrameClass];
      use { World := Fin 2, Rel := λ _ y => y = 1 };
      constructor;
      . simp [Serial];
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 1), 0;
        simp [Satisfies];


example : (𝐊 : DeductionParameter α) <ₛ 𝐊𝐓 := strictlyWeakerThan.trans K_strictlyWeakerThan_KD KD_strictlyWeakerThan_KT


theorem K4_weakerThan_S4 : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by
  apply reducible_of_subset_FrameClass (α := α) TransitiveFrameClass PreorderFrameClass;
  simp;

theorem K4_strictlyWeakerThan_S4 : (𝐊𝟒 : DeductionParameter α) <ₛ 𝐒𝟒 := by
  constructor;
  . apply K4_weakerThan_S4;
  . simp [weakerThan_iff]
    use (□(atom default) ⟶ (atom default));
    constructor;
    . exact Deduction.maxm! (by simp)
    . apply sound_K4.not_provable_of_countermodel;
      simp [FrameClass];
      use { World := Fin 3, Rel := λ _ y => y = 1 };
      constructor;
      . simp [Transitive];
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 1), 0;
        simp [Satisfies];


theorem S4_weakerThan_S5 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟓 := by
  apply reducible_of_subset_FrameClass PreorderFrameClass ReflexiveEuclideanFrameClass;
  simp_all [trans_of_refl_eucl];

theorem S4_strictlyWeakerThan_S5 : (𝐒𝟒 : DeductionParameter α) <ₛ 𝐒𝟓 := by
  constructor;
  . apply S4_weakerThan_S5;
  . simp [weakerThan_iff];
    use (◇(atom default) ⟶  □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply sound_S4.not_provable_of_countermodel;
      simp [FrameClass];
      use { World := Fin 3, Rel := λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2) };
      refine ⟨?_, ?_, ?_⟩;
      . simp [Reflexive];
      . simp [Transitive]; aesop;
      . simp [ValidOnFrame, ValidOnModel];
        use (λ w _ => w = 2), 0;
        simp [Satisfies];
        constructor;
        . omega;
        . use 1; omega;


theorem equiv_S5_KT4B : (𝐒𝟓 : DeductionParameter α) =ₛ 𝐊𝐓𝟒𝐁 := by
  apply equiv_of_eq_FrameClass ReflexiveEuclideanFrameClass EquivalenceFrameClass;
  apply Set.eq_of_subset_of_subset;
  . simp_all [symm_of_refl_eucl, trans_of_refl_eucl];
  . simp_all [eucl_of_symm_trans];

end Reducible

end LO.Modal.Standard
