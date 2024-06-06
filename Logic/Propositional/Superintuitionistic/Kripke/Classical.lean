import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Kripke.Soundness


namespace LO.Propositional.Superintuitionistic

variable [Inhabited α]

open Formula

namespace Kripke

abbrev ClassicalFrame : Frame := { World := PUnit, Rel := λ _ _ => True }

abbrev ClassicalValuation (α : Type*) := α → Prop

abbrev ClassicalModel (V : ClassicalValuation α) : Model α where
  Frame := ClassicalFrame
  Valuation := λ _ a => V a
  hereditary := by simp;

end Kripke


open Kripke

instance AxiomSet.LEM.definability : Definability (α := α) 𝗟𝗘𝗠 (λ F => Euclidean F.Rel) where
  defines F := by
    simp;
    constructor;
    . intro h x y z hxy hyz;
      let V : Valuation F.World α := (λ v _ => z ≺ v);
      let M := Model.mk F V (by
        simp [V];
        intros _ _ hvu hzv;
        exact F.Rel_trans hzv hvu;
      );
      let p : Formula α := Formula.atom default;

      have : Satisfies M z p := by simp [p, V]; exact F.Rel_refl _;
      have : ¬(Satisfies M x (~p)) := by simp; existsi z; simp_all;
      have : Satisfies M x p := by
        have := Formula.Kripke.Satisfies.or_def.mp $ h p V M.hereditary x;
        aesop;
      have : Satisfies M y p := Formula.Kripke.Satisfies.formula_hereditary hxy this;
      simpa [Satisfies, V] using this;
    . intros hEucl _;
      apply ValidOnFrame.lem;
      intro x y hxy;
      exact F.Rel_antisymm hxy $ hEucl (F.Rel_refl x) hxy;

instance : FrameClass.IsNonempty (𝔽(𝗟𝗘𝗠) : FrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ x y => x ≤ y };
    apply iff_definability_memAxiomSetFrameClass AxiomSet.LEM.definability |>.mpr;
    simp [Euclidean];

instance : FrameClass.IsNonempty (𝔽(𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠) : FrameClass' α) := AxiomSet.EFQ.instUnionNonempty AxiomSet.LEM.definability

instance instClassicalDefinability : Definability (α := α) Ax(𝐂𝐥) (λ F => Euclidean F.Rel) := AxiomSet.EFQ.instDefinabilityUnion AxiomSet.LEM.definability

instance instClassicalDefinability' : Definability (α := α) Ax(𝐂𝐥) (λ F => Identifiable F.Rel) where
  defines F := by
    have hE := instClassicalDefinability.defines F;
    constructor;
    . intro h;
      have := hE.mp h;
      exact ident_of_reflex_antisymm_eucl F.Rel_refl F.Rel_antisymm this;
    . intro h;
      sorry;

instance : System.Consistent (𝐂𝐥 : DeductionParameter α) := inferInstance


instance instClassicalKripkeSemantics : Semantics (Formula α) (ClassicalValuation α) := ⟨fun V ↦ Formula.Kripke.Satisfies (ClassicalModel V) ()⟩

namespace Formula.Kripke.ClassicalSatisfies

variable {V : ClassicalValuation α}

@[simp] protected lemma iff_models : V ⊧ p ↔ Formula.Kripke.Satisfies (ClassicalModel V) () p := iff_of_eq rfl

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp
@[simp] lemma top_def  : V ⊧ ⊤ ↔ True := by simp
@[simp] lemma bot_def  : V ⊧ ⊥ ↔ False := by simp
@[simp] lemma and_def  : V ⊧ p ⋏ q ↔ V ⊧ p ∧ V ⊧ q := by simp
@[simp] lemma or_def   : V ⊧ p ⋎ q ↔ V ⊧ p ∨ V ⊧ q := by simp
@[simp] lemma imp_def  : V ⊧ p ⟶ q ↔ V ⊧ p → V ⊧ q := by simp; tauto;
@[simp] lemma neg_def  : V ⊧ ~p ↔ ¬V ⊧ p := by simp only [NegDefinition.neg, imp_def, bot_def];

end Formula.Kripke.ClassicalSatisfies

variable {p q : Formula α}

lemma Formula.Kripke.ValidOnModel.classical_iff {V : ClassicalValuation α} : (ClassicalModel V) ⊧ p ↔ V ⊧ p := by simp [ValidOnModel]; tauto;

lemma Formula.Kripke.ValidOnClassicalFrame_iff : 𝔽(Ax(𝐂𝐥)) ⊧ p ↔ ∀ (V : ClassicalValuation α), V ⊧ p := by
  constructor;
  . intro h V;
    exact ValidOnModel.classical_iff.mp $ h (by
      apply iff_definability_memAxiomSetFrameClass instClassicalDefinability' |>.mpr;
      simp [Identifiable];
    ) (ClassicalModel V).Valuation (ClassicalModel V).hereditary;
  . sorry;
    -- intro h F hF V hV x;
    -- obtain ⟨N⟩ := F.World_nonempty;
    -- have := h (λ a => V N a);
    -- have := ValidOnModel.classical_iff.mpr this;
--
    -- have := iff_definability_memAxiomSetFrameClass instClassicalDefinability' |>.mp hF;
    -- have := @this x x;
    -- have := @hV x x (by apply this.mpr; trivial);
--
    -- apply instClassicalDefinability.defines.mp;

end LO.Propositional.Superintuitionistic
