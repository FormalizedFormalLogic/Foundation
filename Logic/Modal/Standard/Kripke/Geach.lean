import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Reducible

namespace LO.Modal.Standard

open System
open System.Axioms (Geach)

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

variable [Inhabited α] [DecidableEq α]


section

abbrev GeachConfluentFrameClass (α) (t : Geach.Taple) : FrameClass α := { F | (GeachConfluent t) F }

lemma GeachConfluentFrameClass.nonempty : (GeachConfluentFrameClass α t).Nonempty := by
  use (TerminalFrame α);
  exact GeachConfluent.satisfies_eq;


abbrev MultiGeachConfluentFrameClass (α) (ts : List Geach.Taple) : FrameClass α := { F | MultiGeachConfluent ts F }

lemma MultiGeachConfluentFrameClass.nonempty : (MultiGeachConfluentFrameClass α ts).Nonempty := by
  use (TerminalFrame α);
  exact MultiGeachConfluent.satisfies_eq;


abbrev ReflexiveFrameClass (α) : FrameClass α := { F | Reflexive F }

abbrev SerialFrameClass (α) : FrameClass α := { F | Serial F }

abbrev PreorderFrameClass (α) : FrameClass α := { F | Reflexive F ∧ Transitive F }

abbrev ReflexiveEuclideanFrameClass (α) : FrameClass α := { F | Reflexive F ∧ Euclidean F }

abbrev EquivalenceFrameClass (α) : FrameClass α := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }

end

section Definability

@[simp]
lemma MultiGeachConfluentFrameClass.def_nil : MultiGeachConfluentFrameClass α [] = AllFrameClass α := by
  simp [MultiGeachConfluentFrameClass, MultiGeachConfluent]

open Formula (atom kripke_satisfies)
open Formula.kripke_satisfies (multibox_def multidia_def)

lemma axiomGeach_defines : 𝗴𝗲(t).DefinesKripkeFrameClass (GeachConfluentFrameClass α t) := by
  intro F;
  constructor;
  . rintro h x y z ⟨hi, hj⟩;
    simp at h;
    let M : Model α := { Frame := F, Valuation := λ v _ => y ≺^[t.m] v }
    have him_x : kripke_satisfies M x (◇^[t.i](□^[t.m](atom default))) := by
      apply kripke_satisfies.multidia_def.mpr;
      existsi y;
      constructor;
      . simpa;
      . apply kripke_satisfies.multibox_def.mpr; aesop;
    have hjn_x : kripke_satisfies M x (□^[t.j](◇^[t.n](atom default))) := h (Formula.atom default) M.Valuation x him_x;
    have hn_z : kripke_satisfies M z (◇^[t.n](atom default)) := kripke_satisfies.multibox_def.mp hjn_x z hj;
    obtain ⟨u, hzu, hyu⟩ := kripke_satisfies.multidia_def.mp hn_z;
    existsi u;
    exact ⟨hyu, hzu⟩;
  . simp [AxiomSet.Geach, Axioms.Geach, kripke_satisfies];
    intro h p V x him;
    apply multibox_def.mpr;
    intro z rxz;
    apply multidia_def.mpr;
    obtain ⟨y, rxy, hbp⟩ := multidia_def.mp him;
    obtain ⟨u, ryu, rzu⟩ := h ⟨rxy, rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (multibox_def.mp hbp) _ ryu;


instance : System.Consistent (𝗴𝗲(t)ᴺ : DeductionParameter α) := consistent_of_defines axiomGeach_defines GeachConfluentFrameClass.nonempty


lemma axiomMultiGeach_defines : 𝗚𝗲(ts).DefinesKripkeFrameClass (MultiGeachConfluentFrameClass α ts) := by
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
  (𝔽 : FrameClass α) (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass α geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Λ.DefinesKripkeFrameClass 𝔽 := by
  simp [DeductionParameter.DefinesKripkeFrameClass];
  nth_rw 1 [geach.char];
  rw [←(Set.univ_inter 𝔽)];
  rw [h𝔽];
  exact AxiomSet.DefinesKripkeFrameClass.union axiomK_defines axiomMultiGeach_defines;

lemma S4_defines : 𝐒𝟒.DefinesKripkeFrameClass (PreorderFrameClass α) := instGeachLogicDefinability (PreorderFrameClass α)


instance : System.Consistent (𝐆𝐞(ts) : DeductionParameter α) := consistent_of_defines axiomMultiGeach_defines MultiGeachConfluentFrameClass.nonempty

instance {Λ : DeductionParameter α} [geach : Λ.IsGeach] : System.Consistent Λ := by rw [geach.char]; infer_instance;

instance : System.Consistent (𝐒𝟒 : DeductionParameter α) := inferInstance

instance : System.Consistent (𝐒𝟓 : DeductionParameter α) := inferInstance

end Definability


section Soundness

private lemma instGeachLogicSoundAux
  {Λ : DeductionParameter α} [geach : Λ.IsGeach]
  {𝔽 : FrameClass α}
  (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass α geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Sound Λ 𝔽 := by
    convert sound_of_defines (α := α) axiomMultiGeach_defines;
    exact geach.char;

instance sound_KD : Sound 𝐊𝐃 (SerialFrameClass α) := instGeachLogicSoundAux

instance sound_KT : Sound 𝐊𝐓 (ReflexiveFrameClass α) := instGeachLogicSoundAux

instance sound_S4 : Sound 𝐒𝟒 (PreorderFrameClass α) := instGeachLogicSoundAux

instance sound_S5 : Sound 𝐒𝟓 (ReflexiveEuclideanFrameClass α) := instGeachLogicSoundAux

instance sound_KT4B : Sound 𝐊𝐓𝟒𝐁 (EquivalenceFrameClass α) := instGeachLogicSoundAux

end Soundness


section Completeness

open Theory MaximalConsistentTheory CanonicalFrame
open DeductionParameter (Normal)

variable {Ax : AxiomSet α} [System.Consistent Axᴺ]

lemma geachConfluent_CanonicalFrame (h : 𝗴𝗲(t) ⊆ Ax) : GeachConfluent t (CanonicalFrame Ax):= by
  intro Ω₁ Ω₂ Ω₃ h;
  have ⟨r₁₂, r₁₃⟩ := h; clear h;
  have ⟨Ω, hΩ⟩ := lindenbaum (𝓓 := Axᴺ) (T := ((□''⁻¹^[t.m]Ω₂.theory) ∪ (□''⁻¹^[t.n]Ω₃.theory))) $ by
    apply intro_union_Consistent;
    intro Γ Δ hΓ hΔ hC;

    replace hΓ : ∀ p ∈ Γ, □^[t.m]p ∈ Ω₂.theory := by simpa using hΓ;
    have hΓconj : □^[t.m](Γ.conj') ∈ Ω₂.theory := iff_mem_multibox_conj'.mpr hΓ;

    replace hΔ : ∀ p ∈ Δ, □^[t.n]p ∈ Ω₃.theory := by simpa using hΔ;
    have : □^[t.n](Δ.conj') ∈ Ω₃.theory := iff_mem_multibox_conj'.mpr hΔ;

    have : □^[t.j](◇^[t.n](Γ.conj')) ∈ Ω₁.theory := iff_mem_imp.mp
      (membership_iff.mpr $ Context.of! $ Normal.maxm_ax! (by aesop))
      (multiframe_def_multidia.mp r₁₂ hΓconj)
    have : ◇^[t.n]Γ.conj' ∈ Ω₃.theory := multiframe_def_multibox.mp r₁₃ this;

    have : Axᴺ ⊢! □^[t.n](Δ.conj') ⋏ ◇^[t.n](Γ.conj') ⟶ ⊥ := by
      apply and_imply_iff_imply_imply'!.mpr;
      exact imp_trans''!
        (show Axᴺ ⊢! □^[t.n](Δ.conj') ⟶ □^[t.n](~Γ.conj') by exact imply_multibox_distribute'! $ contra₁'! $ and_imply_iff_imply_imply'!.mp hC)
        (show Axᴺ ⊢! □^[t.n](~Γ.conj') ⟶ ~(◇^[t.n]Γ.conj') by exact contra₁'! $ and₁'! $ multidia_duality!);
    have : Axᴺ ⊬! □^[t.n](Δ.conj') ⋏ ◇^[t.n](Γ.conj') ⟶ ⊥ := by simpa using Ω₃.consistent (Γ := [□^[t.n](Δ.conj'), ◇^[t.n](Γ.conj')]) (by simp_all)

    contradiction;

  use Ω; simp only [Set.union_subset_iff] at hΩ;
  constructor;
  . apply multiframe_def_multibox.mpr; apply hΩ.1;
  . apply multiframe_def_multibox.mpr; apply hΩ.2;

lemma multiGeachConfluent_CanonicalFrame (h : 𝗚𝗲(ts) ⊆ Ax) : MultiGeachConfluent ts (CanonicalFrame Ax) := by
  induction ts with
  | nil => simp [MultiGeachConfluent];
  | cons t ts ih =>
    dsimp only [MultiGeachConfluent];
    constructor;
    . apply geachConfluent_CanonicalFrame;
      simp_all;
    . apply ih;
      simp_all;

private instance instMultiGeachComplete : Complete (𝗚𝗲(ts)ᴺ : DeductionParameter α) (MultiGeachConfluentFrameClass α ts) :=
  instComplete_of_mem_canonicalFrame $ multiGeachConfluent_CanonicalFrame (by rfl)

instance {Λ : DeductionParameter α} [g : Λ.IsGeach] : Complete Λ (MultiGeachConfluentFrameClass α g.taples) := by
  convert instMultiGeachComplete (α := α);
  exact g.char;

private def instGeachLogicCompleteAux {Λ : DeductionParameter α} [geach : Λ.IsGeach]
  {𝔽 : FrameClass α} (h𝔽 : 𝔽 = MultiGeachConfluentFrameClass α geach.taples := by simp_all [MultiGeachConfluentFrameClass, MultiGeachConfluent])
  : Complete Λ 𝔽 := by
    convert instMultiGeachComplete (α := α);
    exact geach.char;

instance : Complete 𝐊𝐓 (ReflexiveFrameClass α) := instGeachLogicCompleteAux

instance : Complete 𝐒𝟒 (PreorderFrameClass α) := instGeachLogicCompleteAux

instance : Complete 𝐒𝟓 (ReflexiveEuclideanFrameClass α) := instGeachLogicCompleteAux

instance : Complete 𝐊𝐓𝟒𝐁 (EquivalenceFrameClass α) := instGeachLogicCompleteAux

end Completeness


section Reducible

theorem reducible_KD_KT : (𝐊𝐃 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by
  apply reducible_of_subset_FrameClass (SerialFrameClass α) (ReflexiveFrameClass α);
  simp_all [serial_of_refl];

theorem reducible_S4_S5 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟓 := by
  apply reducible_of_subset_FrameClass (PreorderFrameClass α) (ReflexiveEuclideanFrameClass α);
  simp_all [trans_of_refl_eucl];

theorem equiv_S5_KT4B : (𝐒𝟓 : DeductionParameter α) =ₛ 𝐊𝐓𝟒𝐁 := by
  apply equiv_of_eq_FrameClass (ReflexiveEuclideanFrameClass α) (EquivalenceFrameClass α);
  apply Set.eq_of_subset_of_subset;
  . simp_all [symm_of_refl_eucl, trans_of_refl_eucl];
  . simp_all [eucl_of_symm_trans];


/- TODO: strict reducible
theorem LogicalStrictStrong.KD_KT [hβ : Nontrivial β] : (𝐊𝐃 : AxiomSet β) <ᴸ 𝐊𝐓 := by
  constructor;
  . simp;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Serial];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

theorem LogicalStrictStrong.K4_S4 [hβ : Nontrivial β] : (𝐊𝟒 : AxiomSet β) <ᴸ 𝐒𝟒 := by
  constructor;
  . apply LogicalStrong.of_subset; simp;
  . obtain ⟨x, y, hxy⟩ := hβ.exists_pair_ne;
    simp only [LogicalStrong, not_forall];
    use (□(Formula.atom default) ⟶ (Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ _ w₂ => w₂ = y);
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Transitive];
    . simp [Formula.FrameConsequence];
      use (λ w _ => w = y);
      simp;
      use x;

theorem LogicalStrictStrong.S4_S5 : (𝐒𝟒 : AxiomSet (Fin 3)) <ᴸ 𝐒𝟓 := by
  constructor;
  . simp;
  . simp only [LogicalStrong, not_forall];
    existsi (◇(Formula.atom default) ⟶ □◇(Formula.atom default));
    use ⟨Deduction.maxm (by simp)⟩;
    apply not_imp_not.mpr $ AxiomSet.sounds;
    simp [Formula.FrameClassConsequence];
    existsi (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
    constructor;
    . simp only [AxiomSetFrameClass.geach];
      apply GeachLogic.frameClassDefinability_aux.mp;
      simp [Reflexive, Transitive];
      aesop;
    . simp [Formula.FrameConsequence];
      use (λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0 ∧ w₂ = 1) ∨ (w₁ = 0 ∧ w₂ = 2));
      aesop;
-/

end Reducible


end Kripke

end LO.Modal.Standard
