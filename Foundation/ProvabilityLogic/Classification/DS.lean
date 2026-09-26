module

public import Foundation.ProvabilityLogic.A.Basic
public import Foundation.ProvabilityLogic.Kripke.AlmostDefiningFormula
public import Foundation.ProvabilityLogic.Classification.ProvabilityLogicTrace

/-!
# Provability logics between `𝐃` and `𝐒`

If `𝐃 ⊬ A`, there is a formula `B` over the atoms of `A` with `𝐒 ⊬ B` and
`𝐀 +ᴸ {A} ⊢ B ⋎ (□#p 🡒 #p)`. If the provability logic of `T` relative to `U` has trace `ω` and
contains a formula outside `𝐃`, then `U` proves the local reflection schema for `T`, so the logic
contains `𝐒`. Hence no provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`.

## References

- [AB05, Lemma 56, Lemma 57, Corollary 58]
- [Bek90, Theorem 1, Assertion 1, §5 Lemma 1, Lemma 1.1]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Model Model.World RootedModel

universe u

namespace Formula

variable {α β : Type*} [DecidableEq α]

/-- The substitution sending each atom `q ∈ S` to `#p 🡘 #q` and fixing the other atoms.

- [Bek90, §5 Lemma 1]
-/
def Substitution.pIffOn (p : α) (S : Finset α) : Substitution α α :=
  fun q ↦ if q ∈ S then #p 🡘 #q else #q

/-- The conjunction of the instances of `A` under `pIffOn p S` for all `S ⊆ A.atoms`.

- [Bek90, §5 Lemma 1]
-/
noncomputable def deltaPIff (A : Formula α) (p : α) : Formula α :=
  (A.atoms.powerset.image fun S ↦ A⟦Substitution.pIffOn p S⟧).conj

lemma atoms_subst_subset [DecidableEq β] {s : Substitution α β} {A : Formula α} :
    (A⟦s⟧).atoms ⊆ A.atoms.biUnion fun a ↦ (s a).atoms := by
  induction A <;> grind;

lemma atoms_pIffOn {p q : α} {S : Finset α} : (Substitution.pIffOn p S q).atoms ⊆ {p, q} := by
  grind [Substitution.pIffOn];

lemma atoms_deltaPIff_subset {A : Formula α} {p : α} :
    (A.deltaPIff p).atoms ⊆ insert p A.atoms := by
  intro q hq;
  obtain ⟨_, hB, hq⟩ := Finset.mem_biUnion.mp (FormulaFinset.atoms_conj_subset _ hq);
  obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hB;
  obtain ⟨b, hb, hq⟩ := Finset.mem_biUnion.mp (atoms_subst_subset hq);
  grind [atoms_pIffOn hq];

end Formula

namespace Logic.A

variable {α : Type*} [DecidableEq α] {A : Formula α} {p : α}

lemma provable_deltaPIff : 𝐀 +ᴸ {A} ⊢ A.deltaPIff p :=
  FConj_iff_forall_provable.mpr fun B hB ↦ by
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hB;
    exact sumQuasiNormal.subst (sumQuasiNormal.mem₂ rfl);

end Logic.A

namespace Kripke.RootedModel

variable {κ κ' α β : Type*} [Nonempty κ] [Nonempty κ']

/-- The rooted model on the frame and root of `K` in which an atom `a` holds where `s a` is
forced in `K`. -/
def subst (K : RootedModel κ α) (s : Substitution β α) : RootedModel κ β where
  toModel := K.toModel.subst s
  root := K.root
  root_rel := K.root_rel

instance {K : RootedModel κ α} {s : Substitution β α} [K.IsGL] : (K.subst s).IsGL :=
  inferInstanceAs (K.toModel.subst s).IsGL

section Transfer

variable [DecidableEq α] {K : RootedModel κ α} {p q : α} {γ : Finset α}

lemma val_subst_pIffOn_of_ne (hp : K.root ⊩[_] □#p) {z : K.World} (hz : z ≠ K.root) :
    (K.subst (Substitution.pIffOn p γ)).Val z q ↔ K.Val z q := by
  have := hp z (K.root_rel z hz);
  change z ⊩[_] (if q ∈ γ then #p 🡘 #q else #q) ↔ _;
  grind;

lemma val_subst_pIffOn_root (hnp : K.root ⊮[_] #p) :
    (K.subst (Substitution.pIffOn p γ)).Val K.root q ↔ (q ∈ γ ↔ ¬K.Val K.root q) := by
  change K.root ⊩[_] (if q ∈ γ then #p 🡘 #q else #q) ↔ _;
  grind;

end Transfer

variable [DecidableEq α] {M : RootedModel κ α} [M.IsFiniteGL] [Fintype M.World] {o : α → Prop}
  {A : Formula α}

lemma root_forces_deltaPIff_imp (hA : Sum.inr ⊤ ⊮[(M.toPseudoTail o).toModel] A) (p : α)
    {K : RootedModel κ' α} [K.IsGL] (hr : ∀ n, K.root ⊮[K.toModel] □^[n]⊥)
    (hK : ∀ z ≠ K.root, ∃ n, z ⊩[K.toModel] □^[n]⊥) :
    K.root ⊩[K.toModel] A.deltaPIff p 🡒 ∼almostDefiningFormula A.atoms M ⋎ (□#p 🡒 #p) := by
  classical
  intro hδ hΦ hp;
  by_contra hnp;
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : Finset α,
      γ ⊆ A.atoms ∧ ∀ q ∈ A.atoms, (q ∈ γ ↔ ¬(o q ↔ K.Val K.root q)) :=
    ⟨A.atoms.filter fun q ↦ ¬(o q ↔ K.Val K.root q), Finset.filter_subset _ _,
      fun q hq ↦ by simp [hq]⟩;
  have hbox (z : K.World) (n : ℕ) :
      z ⊩[K.toModel.subst (Substitution.pIffOn p γ)] □^[n]⊥ ↔ z ⊩[K.toModel] □^[n]⊥ := by
    simpa using forces_subst (A := □^[n]⊥);
  obtain ⟨Bi, hBi⟩ := exists_bisimulation_of_forces_almostDefiningFormula
    (K := K.subst (Substitution.pIffOn p γ))
    (fun n h ↦ hr n ((hbox _ n).mp h)) (fun z hz ↦ (hK z hz).imp fun n ↦ (hbox z n).mpr)
    ((forces_congr_of_modalized (K := K.toModel)
      (K' := K.toModel.subst (Substitution.pIffOn p γ)) rfl (fun _ ↦ not_rel_root)
      (fun z hz q ↦ (val_subst_pIffOn_of_ne hp hz).symm) modalized_almostDefiningFormula).mp
      (of_not_not hΦ))
    fun q hq ↦ by
      change o q ↔ (K.subst (Substitution.pIffOn p γ)).Val K.root q;
      grind [val_subst_pIffOn_root hnp];
  exact hA <| (Bi.forces_iff hBi subset_rfl).mpr <| forces_subst.mpr <|
    forces_conj.mp hδ _ <| Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr hγ₁);

end Kripke.RootedModel

namespace Logic.D

variable {α : Type u} {β : Type*} {A : Formula α}

lemma provable_subst {B : Formula β} {s : Substitution β α} (h : 𝐃 ⊢ B) : 𝐃 ⊢ B⟦s⟧ := by
  classical
  apply (provability_TFAE.out 1 3).mpr;
  intro κ _ M _ V;
  apply forces_subst.mp;
  apply (forces_congr (M := ((M.subst s).toFreeTail fun i a ↦
    Sum.inr i ⊩[(M.toFreeTail V).toModel] s a).toModel) _ _).mp (sound_freeTail h (M.subst s) _);
  · funext x y;
    rcases x <;> rcases y <;> rfl;
  · rintro (x | i) a;
    · exact toFreeTail.forces_inl.symm;
    · rfl;

lemma not_provable_subst_some (h : 𝐃 ⊬ A) : 𝐃 ⊬ A⟦fun a ↦ #(some a)⟧ := by
  have e (B : Formula α) : (B⟦fun a ↦ #(some a)⟧)⟦fun a : Option α ↦ a.elim ⊥ (#·)⟧ = B := by
    induction B <;> simp_all;
  exact fun h' ↦ h (e A ▸ provable_subst h');

variable [DecidableEq α]

/-- - [Bek90, §4 Lemma 4, Lemma 9, §5 Lemma 1] -/
lemma exists_A_provable_deltaPIff_imp (hA : 𝐃 ⊬ A) (p : α) :
    ∃ B : Formula α, B.atoms ⊆ A.atoms ∧ 𝐒 ⊬ B ∧ 𝐀 ⊢ A.deltaPIff p 🡒 B ⋎ (□#p 🡒 #p) := by
  have := iff_forces_pseudoTail.not.mp hA;
  push Not at this;
  obtain ⟨κ, _, M, _, o, hM⟩ := this;
  have : Fintype M.World := Fintype.ofFinite _;
  use ∼almostDefiningFormula A.atoms M;
  and_intros;
  · simpa using atoms_almostDefiningFormula;
  · exact S.not_provable_neg_of_forces_freeTail modalized_almostDefiningFormula
      (pseudoTail_forces_almostDefiningFormula o);
  · exact Logic.A.iff_forces_graft.mpr fun N _ a ↦ root_forces_deltaPIff_imp hM p
      graft.not_forces_boxItr_bot fun _ ↦ graft.exists_forces_boxItr_bot;

/--
- [AB05, Lemma 56]
- [Bek90, §5 Lemma 1]
-/
lemma exists_A_add_provable_or_boxImp (hA : 𝐃 ⊬ A) (p : α) :
    ∃ B : Formula α, 𝐒 ⊬ B ∧ B.atoms ⊆ A.atoms ∧ 𝐀 +ᴸ {A} ⊢ B ⋎ (□#p 🡒 #p) := by
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := exists_A_provable_deltaPIff_imp hA p;
  exact ⟨B, hB₂, hB₁, sumQuasiNormal.of_left hB₃ ⨀ Logic.A.provable_deltaPIff⟩;

end Logic.D

open FirstOrder LetterlessFormula

variable {α β : Type*} {T U : ArithmeticTheory} [T.Δ₁]
         {A : Formula α} {σ : ArithmeticSentence}

lemma LetterlessFormula.lift_mem_provabilityLogic_iff {A : LetterlessFormula} :
  ↑A ∈ T.provabilityLogicRelativeTo U (α := α) ↔ ↑A ∈ T.provabilityLogicRelativeTo U (α := β)
  := by
  constructor <;> intro h f <;> simpa only [standardInterpret, interpret_lift] using h ⟨fun _ ↦ ⊥⟩;

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma A_weakerThan_provabilityLogic_of_trace
  (h : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ) :
  𝐀 ⪯ T.provabilityLogicRelativeTo U (α := β) :=
  sumQuasiNormal_weakerThan_provabilityLogic <| by
    rintro _ ⟨i, -, rfl⟩;
    simpa using (lift_mem_provabilityLogic_iff (A := TBB i)).mp <| by
      simpa using TBB_mem_provabilityLogic_of_mem_trace (h ▸ Set.mem_univ i)

/-- If the provability logic of `T` relative to `U` has trace `ω` and contains a formula outside
`𝐃`, then `U` proves `Pr_T(σ) 🡒 σ` for every sentence `σ`.

- [Bek90, Theorem 1]
- [AB05, Lemma 57]
-/
theorem provable_reflection_of_not_D (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
  (hA : A ∈ T.provabilityLogicRelativeTo U) (hAD : 𝐃 ⊬ A)
  : U ⊢ T.standardProvability σ 🡒 σ := by
  classical
  have h₁ : (𝐀 +ᴸ {A⟦fun a ↦ #(some a)⟧}) ⊆ T.provabilityLogicRelativeTo U := by
    intro C hC;
    induction hC with
    | mem₁ hC => exact (A_weakerThan_provabilityLogic_of_trace hT).wk hC;
    | mem₂ hC =>
      obtain rfl := hC;
      intro g;
      simpa [interpret_subst, interpret] using hA ⟨fun a ↦ g.val (some a)⟩;
    | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
    | subst _ ih => exact provabilityLogic_subst ih;
  obtain ⟨B, hBS, hB, hB₂⟩ :=
    Logic.D.exists_A_add_provable_or_boxImp (Logic.D.not_provable_subst_some hAD) none;
  obtain ⟨n, f, hf⟩ := exists_realization_provable_neg_of_not_S (T := T) hBS;
  have h₂ : U ⊢ f T (lift (⩕ i ∈ Finset.range n, TBB i)) :=
    (lift_mem_provabilityLogic_iff (β := Empty)).mpr (by
      simpa [Logic.provable_iff_mem] using (A_weakerThan_provabilityLogic_of_trace hT).wk <|
        FConj'_iff_forall_provable.mpr fun _ _ ↦ Logic.A.provable_TBB) f;
  have h₃ : U ⊢ (⟨Function.update f.val none σ⟩ : Realization _ _) T (B ⋎ (□#none 🡒 #none)) :=
    h₁ hB₂ _;
  have e : (⟨Function.update f.val none σ⟩ : Realization _ _) T B = f T B :=
    interpret_congr_atoms fun a ha ↦
      Function.update_of_ne (by grind [atoms_subst_subset (hB ha)]) _ _;
  have h₄ : U ⊢ ∼f T (B ⋏ lift (⩕ i ∈ Finset.range n, TBB i)) := WeakerThan.pbl hf;
  simp only [standardInterpret, interpret, e] at h₃ h₄;
  cl_prover [h₂, h₃, h₄];

/-- A provability logic of trace `ω` strictly containing `𝐃` contains `𝐒`.

- [Bek90, Assertion 1]
- [AB05, Lemma 56, Lemma 57]
-/
theorem S_weakerThan_provabilityLogic
  (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ)
  (h : 𝐃 ⪱ T.provabilityLogicRelativeTo U (α := α)) :
  𝐒 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  obtain ⟨-, A, hAD, hA⟩ := strictlyWeakerThan_iff.mp h;
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ ⟨C, rfl⟩ _;
  exact provable_reflection_of_not_D hT hA hAD;

/-- No provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`.

- [AB05, Corollary 58]
-/
theorem not_D_strictlyWeakerThan_provabilityLogic_strictlyWeakerThan_S
  (hT : (T.provabilityLogicRelativeTo U (α := α)).trace = .univ) :
  ¬(𝐃 ⪱ T.provabilityLogicRelativeTo U (α := α) ∧ T.provabilityLogicRelativeTo U (α := α) ⪱ 𝐒) :=
  fun ⟨h₁, h₂⟩ ↦ h₂.notWT (S_weakerThan_provabilityLogic hT h₁)

end FFL.ProvabilityLogic

end
