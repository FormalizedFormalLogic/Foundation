module

public import Foundation.ProvabilityLogic.A.Basic
public import Foundation.ProvabilityLogic.Kripke.AlmostDefiningFormula

/-!
# Formulas outside `𝐃` yield formulas outside `𝐒`

If `𝐃 ⊬ A`, there is a formula `B` over the atoms of `A` with `𝐒 ⊬ B` and
`𝐀 +ᴸ {A} ⊢ B ⋎ (□#p 🡒 #p)`.

## References

- [AB05, Lemma 56]
- [Bek90, §5 Lemma 1, Lemma 1.1]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Formula Kripke Kripke.Model Kripke.Model.World Kripke.RootedModel

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
  unfold Substitution.pIffOn;
  grind;

lemma atoms_deltaPIff_subset {A : Formula α} {p : α} :
    (A.deltaPIff p).atoms ⊆ insert p A.atoms := by
  intro q hq;
  obtain ⟨_, hB, hq⟩ := Finset.mem_biUnion.mp (FormulaFinset.atoms_conj_subset _ hq);
  obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hB;
  obtain ⟨b, hb, hq⟩ := Finset.mem_biUnion.mp (atoms_subst_subset hq);
  have := atoms_pIffOn hq;
  grind;

end Formula

lemma Logic.A.provable_deltaPIff {α : Type*} [DecidableEq α] {A : Formula α} {p : α} :
    𝐀 +ᴸ {A} ⊢ A.deltaPIff p := by
  sorry

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
  (hp : K.root ⊩[K.toModel] □#p) (hnp : K.root ⊮[K.toModel] #p)
include hp hnp

lemma val_subst_pIffOn_of_ne {z : K.World} (hz : z ≠ K.root) :
    (K.subst (Substitution.pIffOn p γ)).Val z q ↔ K.Val z q := by
  sorry

lemma val_subst_pIffOn_root :
    (K.subst (Substitution.pIffOn p γ)).Val K.root q ↔ (q ∈ γ ↔ ¬K.Val K.root q) := by
  sorry

end Transfer

variable [DecidableEq α] {M : RootedModel κ α} [M.IsFiniteGL] [Fintype M.World] {o : α → Prop}
  {A : Formula α}

lemma graft_root_forces_deltaPIff_imp (hA : Sum.inr ⊤ ⊮[(M.toPseudoTail o).toModel] A) (p : α)
    (N : RootedModel κ' α) [N.IsFiniteGL] (a : N.NonRoot) :
    (N.graft a ℕ).root ⊩[(N.graft a ℕ).toModel]
      A.deltaPIff p 🡒 ∼almostDefiningFormula A.atoms M ⋎ (□#p 🡒 #p) := by
  sorry

end Kripke.RootedModel

namespace Logic.D

variable {α : Type u} [DecidableEq α] {A : Formula α}

/-- If `𝐃 ⊬ A`, there is a formula `B` over the atoms of `A` with `𝐒 ⊬ B` and
`𝐀 ⊢ A.deltaPIff p 🡒 B ⋎ (□#p 🡒 #p)`.

- [Bek90, §4 Lemma 4, Lemma 9, §5 Lemma 1]
-/
theorem exists_A_provable_deltaPIff_imp (hA : 𝐃 ⊬ A) (p : α) :
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
  · exact Logic.A.iff_forces_graft.mpr fun N _ a ↦ graft_root_forces_deltaPIff_imp hM p N a;

/-- If `𝐃 ⊬ A`, there is a formula `B` over the atoms of `A` with `𝐒 ⊬ B` and
`𝐀 +ᴸ {A} ⊢ B ⋎ (□#p 🡒 #p)`.

- [AB05, Lemma 56]
- [Bek90, §5 Lemma 1]
-/
theorem exists_A_add_provable_or_boxImp (hA : 𝐃 ⊬ A) (p : α) :
    ∃ B : Formula α, 𝐒 ⊬ B ∧ B.atoms ⊆ A.atoms ∧ 𝐀 +ᴸ {A} ⊢ B ⋎ (□#p 🡒 #p) := by
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := exists_A_provable_deltaPIff_imp hA p;
  exact ⟨B, hB₂, hB₁, sumQuasiNormal.of_left hB₃ ⨀ Logic.A.provable_deltaPIff⟩;

omit [DecidableEq α] in
lemma provable_subst {β : Type*} {A : Formula β} {s : Substitution β α} (h : 𝐃 ⊢ A) :
    𝐃 ⊢ A⟦s⟧ := by
  sorry

omit [DecidableEq α] in
lemma not_provable_subst_some (h : 𝐃 ⊬ A) : 𝐃 ⊬ A⟦fun a ↦ #(some a)⟧ := by
  sorry

end Logic.D

end FFL.ProvabilityLogic

end
