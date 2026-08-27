module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Auxiliary identities and atom theory for Boolean algebras

Elementary Boolean algebra identities and finite-atom-theory facts used to build the
back-and-forth isomorphism between countable atomless Boolean algebras
(`Foundation.Vorspiel.Order.BooleanAlgebra.Iso`).

Folklore Boolean algebra manipulations; there is no direct literature source.
-/

@[expose] public section

namespace BooleanAlgebra

variable {γ : Type*} [BooleanAlgebra γ]

lemma inf_le_iff_sdiff_disjoint {y₁ y₂ a : γ} : y₁ ⊓ a ≤ y₂ ⊓ a ↔ (y₁ \ y₂) ⊓ a = ⊥ := by
  rw [← sdiff_eq_bot_iff,
    show (y₁ ⊓ a) \ (y₂ ⊓ a) = y₁ \ y₂ ⊓ a by
      rw [sdiff_eq, sdiff_eq, compl_inf, inf_sup_left]; simp [inf_left_comm, inf_comm]]

/-- `(y ⊓ a) ⊔ (z ⊓ aᶜ)` is the normal form of an element of `closure (insert a A)`. -/
lemma insertRep_le_insertRep_iff {y₁ z₁ y₂ z₂ a : γ} :
    (y₁ ⊓ a) ⊔ (z₁ ⊓ aᶜ) ≤ (y₂ ⊓ a) ⊔ (z₂ ⊓ aᶜ) ↔
      (y₁ \ y₂) ⊓ a = ⊥ ∧ (z₁ \ z₂) ⊓ aᶜ = ⊥ := by
  have h₁ : y₁ ⊓ a ≤ y₂ ⊓ a ⊔ z₂ ⊓ aᶜ ↔ y₁ ⊓ a ≤ y₂ ⊓ a :=
    ⟨fun h => by simpa [inf_sup_right, inf_assoc] using inf_le_inf_right a h,
      fun h => h.trans le_sup_left⟩
  have h₂ : z₁ ⊓ aᶜ ≤ y₂ ⊓ a ⊔ z₂ ⊓ aᶜ ↔ z₁ ⊓ aᶜ ≤ z₂ ⊓ aᶜ :=
    ⟨fun h => by simpa [inf_sup_right, inf_assoc] using inf_le_inf_right aᶜ h,
      fun h => h.trans le_sup_right⟩
  rw [sup_le_iff, h₁, h₂, inf_le_iff_sdiff_disjoint, inf_le_iff_sdiff_disjoint]

lemma compl_insertRep (y z a : γ) : ((y ⊓ a) ⊔ (z ⊓ aᶜ))ᶜ = (yᶜ ⊓ a) ⊔ (zᶜ ⊓ aᶜ) := by
  have e1 : (y ⊓ a) ⊔ (yᶜ ⊓ a) = a := by rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
  have e2 : (z ⊓ aᶜ) ⊔ (zᶜ ⊓ aᶜ) = aᶜ := by rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
  have hsup : (y ⊓ a) ⊔ (z ⊓ aᶜ) ⊔ ((yᶜ ⊓ a) ⊔ (zᶜ ⊓ aᶜ)) = ⊤ := by
    have hperm : (y ⊓ a) ⊔ (z ⊓ aᶜ) ⊔ ((yᶜ ⊓ a) ⊔ (zᶜ ⊓ aᶜ)) =
        (y ⊓ a) ⊔ (yᶜ ⊓ a) ⊔ ((z ⊓ aᶜ) ⊔ (zᶜ ⊓ aᶜ)) := by ac_rfl
    rw [hperm, e1, e2, sup_compl_eq_top]
  have hac : aᶜ ⊓ a = ⊥ := by rw [inf_comm]; exact inf_compl_eq_bot
  have h1 : (y ⊓ a) ⊓ (yᶜ ⊓ a) = ⊥ :=
    le_bot_iff.mp <| (inf_le_inf inf_le_left inf_le_left).trans_eq inf_compl_eq_bot
  have h2 : (y ⊓ a) ⊓ (zᶜ ⊓ aᶜ) = ⊥ :=
    le_bot_iff.mp <| (inf_le_inf inf_le_right inf_le_right).trans_eq inf_compl_eq_bot
  have h3 : (z ⊓ aᶜ) ⊓ (yᶜ ⊓ a) = ⊥ :=
    le_bot_iff.mp <| (inf_le_inf inf_le_right inf_le_right).trans_eq hac
  have h4 : (z ⊓ aᶜ) ⊓ (zᶜ ⊓ aᶜ) = ⊥ :=
    le_bot_iff.mp <| (inf_le_inf inf_le_left inf_le_left).trans_eq inf_compl_eq_bot
  have hinf : ((y ⊓ a) ⊔ (z ⊓ aᶜ)) ⊓ ((yᶜ ⊓ a) ⊔ (zᶜ ⊓ aᶜ)) = ⊥ := by
    rw [inf_sup_right, inf_sup_left, inf_sup_left, h1, h2, h3, h4]; simp
  exact (IsCompl.mk (disjoint_iff.mpr hinf) (codisjoint_iff.mpr hsup)).compl_eq

lemma IsAtom.le_or_disjoint {p : γ} (hp : IsAtom p) (w : γ) : p ≤ w ∨ p ⊓ w = ⊥ :=
  (em (p ≤ w)).imp_right fun h => disjoint_iff.mp (hp.not_le_iff_disjoint.mp h)

open Classical in
noncomputable def atomsBelow [Fintype γ] (w : γ) : Finset γ :=
  {p | IsAtom p ∧ p ≤ w}

lemma sup_atomsBelow_eq [Finite γ] (w : γ) :
    haveI := Fintype.ofFinite γ
    (atomsBelow w).sup id = w := by
  sorry

lemma inf_eq_bot_iff_atomsBelow [Finite γ] {w a' : γ} :
    haveI := Fintype.ofFinite γ
    w ⊓ a' = ⊥ ↔ ∀ p ∈ atomsBelow w, p ⊓ a' = ⊥ := by
  sorry

end BooleanAlgebra

namespace BooleanSubalgebra

variable {α : Type*} [BooleanAlgebra α] {A : BooleanSubalgebra α}

lemma val_finsetSup (s : Finset A) : ((s.sup id : A) : α) = s.sup (fun p => (p : α)) := by
  sorry

end BooleanSubalgebra
