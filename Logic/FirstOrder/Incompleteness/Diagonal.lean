import Logic.FirstOrder.Arith.Representation
import Logic.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

namespace Diagonal

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

open Encodable Subformula

noncomputable def fsbs : Subsentence ℒₒᵣ 3 :=
  graphTotal₂ (fun (σ π : Subsentence ℒₒᵣ 1) => σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)])

lemma sbs_spec (σ π : Subsentence ℒₒᵣ 1) :
    T ⊢! ∀' (fsbs/[#0, ⸢σ⸣, ⸢π⸣] ⟷ “#0 = !!⸢σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)]⸣”) :=
  representation_computable₂ T (f := fun (σ π : Subsentence ℒₒᵣ 1) => σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)])
    (by sorry) σ π

noncomputable def diag (θ : Subsentence ℒₒᵣ 1) : Subsentence ℒₒᵣ 1 :=
  ∀' (fsbs/[#0, #1, #1] ⟶ θ/[#0])

noncomputable def fixpoint (θ : Subsentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  ∀' (fsbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])

lemma substs_diag (θ σ : Subsentence ℒₒᵣ 1) :
    (diag θ)/[(⸢σ⸣ : Subterm ℒₒᵣ Empty 0)] = ∀' (fsbs/[#0, ⸢σ⸣, ⸢σ⸣] ⟶ θ/[#0]) := by
  simp[diag, Rew.q_substs, ←Rew.hom_comp_app, Rew.substs_comp_substs]

theorem fixpoint_spec (θ : Subsentence ℒₒᵣ 1) :
    T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣] :=
  Complete.consequence_iff_provable.mp (consequence_of _ _ (fun M _ _ _ _ _ => by
    haveI : Theory.Mod M (Theory.PAminus ℒₒᵣ) :=
      Theory.Mod.of_subtheory (T₁ := T) M (Semantics.ofSystemSubtheory _ _)
    have hfsbs : ∀ σ π : Subsentence ℒₒᵣ 1, ∀ z,
        PVal! M ![z, encode σ, encode π] fsbs ↔ z = encode (σ/[(⸢π⸣ : Subterm ℒₒᵣ Empty 0)]) := by
      simpa[models_iff, Subformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      fun σ π => consequence_iff'.mp (Sound.sound' (sbs_spec (T := T) σ π)) M
    simp[models_iff, Subformula.eval_substs, Matrix.comp_vecCons']
    suffices : PVal! M ![] (fixpoint θ) ↔ PVal! M ![encode (fixpoint θ)] θ
    · simpa[Matrix.constant_eq_singleton] using this
    calc
      PVal! M ![] (fixpoint θ)
      ↔ ∀ z, PVal! M ![z, encode (diag θ), encode (diag θ)] fsbs → PVal! M ![z] θ := by simp[fixpoint, Subformula.eval_rew,
                                                                                            Function.comp, Matrix.comp_vecCons',
                                                                                            Matrix.constant_eq_vec₂,
                                                                                            Matrix.constant_eq_singleton]
    _ ↔ PVal! M ![encode $ (diag θ)/[(⸢diag θ⸣ : Subterm ℒₒᵣ Empty 0)]] θ         := by simp[hfsbs]
    _ ↔ PVal! M ![encode $ ∀' (fsbs/[#0, ⸢diag θ⸣, ⸢diag θ⸣] ⟶ θ/[#0])] θ         := by rw[substs_diag]
    _ ↔ PVal! M ![encode (fixpoint θ)] θ                                           := by rfl))

end Diagonal


end Arith

end FirstOrder

end LO
