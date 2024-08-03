import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

universe u v

namespace LO.Kripke

abbrev ClassicalFrame : Kripke.Frame where
  World := Unit
  Rel _ _ := True

abbrev ClassicalValuation (α : Type*) := α → Prop

abbrev ClassicalModel (V : ClassicalValuation α) : Kripke.Model α where
  Frame := ClassicalFrame
  Valuation _ a := V a
  -- hereditary := by simp only [imp_self, forall_const, forall_true_left];

end LO.Kripke


namespace LO.Propositional.Superintuitionistic

variable {α : Type u} [Inhabited α]

open LO.Kripke

namespace Formula.Kripke


--

instance cla : Semantics (Formula α) (ClassicalValuation α) := ⟨λ V => Satisfies (ClassicalModel.{u} V) ()⟩

namespace ClassicalSatisfies

variable {V : ClassicalValuation α}

set_option pp.universes true
@[simp] protected lemma iff_models : V ⊧ p ↔ Satisfies (ClassicalModel V) () p := by rfl

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp [Satisfies]

instance : Semantics.Tarski (ClassicalValuation α) where
  realize_top := by simp [Satisfies];
  realize_bot := by simp [Satisfies];
  realize_or  := by simp [Satisfies];
  realize_and := by simp [Satisfies];
  realize_imp := by simp [Satisfies]; tauto;
  realize_not := by simp [Satisfies]; tauto;

end ClassicalSatisfies


lemma ValidOnModel.classical_iff {V : ClassicalValuation α} : (ClassicalModel V) ⊧ p ↔ V ⊧ p := by tauto;

end Formula.Kripke


namespace Kripke

lemma ValidOnClassicalFrame_iff : 𝔽(𝐂𝐥 of α) ⊧ p → ∀ (V : ClassicalValuation α), V ⊧ p := by
  intro h V;
  apply Formula.Kripke.ValidOnModel.classical_iff.mp;
  intro w;

  sorry;
  /-
  exact h (by
    apply iff_definability_memAxiomSetFrameClass instClassicalDefinabilityExtensive |>.mpr;
    simp [Extensive];
  ) (ClassicalModel V).Valuation (ClassicalModel V).hereditary;
  -/

lemma notClassicalValid_of_exists_ClassicalValuation : (∃ (V : ClassicalValuation α), ¬(V ⊧ p)) → ¬𝔽(𝐂𝐥 of α) ⊧ p := by
  contrapose; push_neg;
  apply ValidOnClassicalFrame_iff;

/-
set_option pp.universes true
lemma unprovable_classical_of_exists_ClassicalValuation (h : ∃ (V : ClassicalValuation α), ¬(V ⊧ p)) : 𝐂𝐥 ⊬! p := by
  apply not_imp_not.mpr $ Kripke.sound;
  apply notClassicalValid_of_exists_ClassicalValuation;
  assumption;
-/

end Kripke

/-
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

instance : System.Consistent (𝐂𝐥 : DeductionParameter α) := inferInstance


instance instClassicalDefinabilityEuclidean : Definability (α := α) Ax(𝐂𝐥) (λ F => Euclidean F.Rel) := AxiomSet.EFQ.instDefinabilityUnion AxiomSet.LEM.definability

instance instClassicalDefinabilityExtensive : Definability (α := α) Ax(𝐂𝐥) (λ F => Extensive F.Rel) where
  defines F := by
    have hE := instClassicalDefinabilityEuclidean.defines F;
    constructor;
    . intro h;
      exact extensive_of_reflex_antisymm_eucl F.Rel_refl F.Rel_antisymm $ hE.mp h;
    . intro h;
      apply hE.mpr;
      intro x y z rxy ryz;
      have := h rxy;
      have := h ryz;
      subst_vars;
      apply F.Rel_refl;

instance : System.Consistent (𝐂𝐥 : DeductionParameter α) := inferInstance


instance instClassicalKripkeSemantics : Semantics (Formula α) (ClassicalValuation α) := ⟨fun V ↦ Formula.Kripke.Satisfies (ClassicalModel V) PUnit.unit⟩

namespace Formula.Kripke.ClassicalSatisfies

variable {V : ClassicalValuation α}

@[simp] protected lemma iff_models : V ⊧ p ↔ Formula.Kripke.Satisfies (ClassicalModel V) PUnit.unit p := iff_of_eq rfl

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp
@[simp] lemma top_def  : V ⊧ ⊤ ↔ True := by simp
@[simp] lemma bot_def  : V ⊧ ⊥ ↔ False := by simp
@[simp] lemma and_def  : V ⊧ p ⋏ q ↔ V ⊧ p ∧ V ⊧ q := by simp
@[simp] lemma or_def   : V ⊧ p ⋎ q ↔ V ⊧ p ∨ V ⊧ q := by simp
@[simp] lemma imp_def  : V ⊧ p ⟶ q ↔ V ⊧ p → V ⊧ q := by simp; tauto;
-- @[simp] lemma neg_def  : V ⊧ ~p ↔ ¬V ⊧ p := by simp;

end Formula.Kripke.ClassicalSatisfies

variable {p q : Formula α}

lemma Formula.Kripke.ValidOnModel.classical_iff {V : ClassicalValuation α} : (ClassicalModel V) ⊧ p ↔ V ⊧ p := by simp [ValidOnModel]; tauto;

lemma Formula.Kripke.ValidOnClassicalFrame_iff : 𝔽(Ax(𝐂𝐥)) ⊧ p → ∀ (V : ClassicalValuation α), V ⊧ p := by
  intro h V;
  apply Formula.Kripke.ValidOnModel.classical_iff.mp;
  exact h (by
    apply iff_definability_memAxiomSetFrameClass instClassicalDefinabilityExtensive |>.mpr;
    simp [Extensive];
  ) (ClassicalModel V).Valuation (ClassicalModel V).hereditary;

lemma notClassicalValid_of_exists_ClassicalValuation : (∃ (V : ClassicalValuation α), ¬(V ⊧ p)) → (¬𝔽(Ax(𝐂𝐥)) ⊧ p) := by
  contrapose;
  push_neg;
  apply Formula.Kripke.ValidOnClassicalFrame_iff;

lemma unprovable_classical_of_exists_ClassicalValuation (h : ∃ (V : ClassicalValuation α), ¬(V ⊧ p)) : 𝐂𝐥 ⊬! p := by
  apply not_imp_not.mpr $ Kripke.sound!;
  apply notClassicalValid_of_exists_ClassicalValuation;
  assumption;
-/

end LO.Propositional.Superintuitionistic
