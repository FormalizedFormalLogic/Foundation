module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Collection for the broad arithmetical hierarchy

The axioms of `𝗕 Γ s` range over `StrictHierarchy Γ s` formulas only, yet its models satisfy the
collection axiom for every formula of the broad class `Hierarchy Γ s`.

## References

- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s : ℕ}

/-- In a model of `𝗕 Γ s`, witnesses for a `Hierarchy Γ s` formula `θ` at every `x < a` can be
chosen below a single bound `w`. -/
lemma exists_bound_of_models_CollectionOnHierarchy_of_hierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {m : ℕ}
    {θ : ArithmeticSemisentence (m + 2)} (hθ : Hierarchy Γ s θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnHierarchy (Γ := Γ) (s := s);
  obtain ⟨θ', hθ'⟩ := Prenex.models_exists_prenex hθ;
  obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy (Γ := Γ) (s := s)
    (θ := θ'.val) Prenex.val_strictHierarchy e a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (hθ' V (u :> x :> e)).mp hu;
  exact ⟨w, fun x hx ↦ (hw x hx).imp fun u hu ↦ ⟨hu.1, (hθ' V (u :> x :> e)).mpr hu.2⟩⟩;

/-- A model of `𝗕 Γ s` satisfies the collection axiom for every `Hierarchy Γ s` formula. -/
lemma models_collectionAxiom_of_hierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy Γ s φ) : V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ) : ArithmeticSentence) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := Γ) (s := s);
  rw [models_collectionAxiom_iff];
  intro f a h;
  obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy_of_hierarchy
    (θ := φ.toSemisentence ![#1, #0]) (hφ.rew _) (fun i : Fin φ.fvSup ↦ f i) a <| by
      intro x hx;
      obtain ⟨y, hy⟩ := h x hx;
      exact ⟨y, (φ.eval_toSemisentence_two x y f).mpr hy⟩;
  exact ⟨w + 1, fun x hx ↦ (hw x hx).imp fun u hu ↦
    ⟨Arithmetic.lt_succ_iff_le.mpr hu.1, (φ.eval_toSemisentence_two x u f).mp hu.2⟩⟩;

end FFL.FirstOrder.Arithmetic
