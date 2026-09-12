module

public import Foundation.FirstOrder.Arithmetic.Basic.StrictHierarchy
public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# The collection schemata `𝗕𝚺` and `𝗕𝚷` in models

## References

- [HP98, §I.2(a), Lemma I.2.11]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

section models

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma models_collectionAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs];

lemma exists_bound_of_models_collectionAxiom {m : ℕ} {θ : ArithmeticSemisentence (m + 2)}
    (h : V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom
      (Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ)) :
        ArithmeticSentence))
    (e : Fin m → V) (a : V) (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  set ψ : ArithmeticSemiformula ℕ 2 :=
    Rew.embSubsts (#1 :> #0 :> fun i : Fin m ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ θ with hψdef;
  set f : ℕ → V := fun i ↦ if hi : i < m then e ⟨i, hi⟩ else a with hf;
  have heval : ∀ x y : V, ψ.Eval ![x, y] f ↔ V ⊧/(y :> x :> e) θ := by
    intro x y;
    rw [hψdef];
    simp only [Semiformula.eval_embSubsts];
    apply Iff.of_eq;
    apply congrArg (fun b ↦ Semiformula.Evalb (M := V) b θ);
    funext i;
    cases i using Fin.cases with
    | zero => simp;
    | succ i =>
      cases i using Fin.cases with
      | zero => simp;
      | succ i => simp [hf, i.isLt];
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff ψ).mp h f a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (heval x u).mpr hu;
  exact ⟨b, fun x hx ↦ (hb x hx).imp fun u hu ↦ ⟨le_of_lt hu.1, (heval x u).mp hu.2⟩⟩;

end models

section standardModel

instance models_CollectionOnHierarchy (Γ : Polarity) (n : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗕 Γ n := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  . infer_instance;
  . apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, -, rfl⟩;
    apply models_collectionAxiom_iff _ |>.mpr;
    intro f a h;
    choose! g hg using h;
    use (Finset.range a).sup g + 1;
    intro x hx;
    use g x;
    and_intros;
    . exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_range.mpr hx));
    . exact hg x hx;

instance (Γ : Polarity) (n : ℕ) : Entailment.Consistent (𝗕 Γ n) :=
  (𝗕 Γ n).consistent_of_sound (Eq ⊥) rfl

end standardModel

section BSigma_ISigma

theorem ISigma.provable_collectionAxiom_of_hierarchy (n : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) : 𝗜𝚺 (n + 1) ⊢ .univCl (collectionAxiom φ) := by
  apply Arithmetic.complete.{0};
  intro M _ hMT;
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := n + 1);
  apply models_collectionAxiom_iff _ |>.mpr;
  intro f a h;
  obtain ⟨w, hw⟩ := sigma_exists_bound_witness (hφ.rew _) (fun i : Fin φ.fvSup ↦ f i) a <| by
    intro x hx;
    obtain ⟨y, hy⟩ := h x hx;
    exact ⟨y, (φ.eval_toSemisentence_two x y f).mpr hy⟩;
  use w + 1;
  intro x hx;
  obtain ⟨u, hu, hux⟩ := hw x hx;
  use u;
  and_intros;
  . exact Arithmetic.lt_succ_iff_le.mpr hu;
  . exact (φ.eval_toSemisentence_two x u f).mp hux;

theorem BSigma_weakerThan_ISigma (n : ℕ) : 𝗕𝚺 (n + 1) ⪯ 𝗜𝚺 (n + 1) :=
  Entailment.WeakerThan.ofAxm! <| by
    rintro σ (hσ | ⟨φ, hφ, rfl⟩);
    . exact Entailment.WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega))
        (Entailment.by_axm hσ);
    . exact ISigma.provable_collectionAxiom_of_hierarchy n hφ;

end BSigma_ISigma

section strictCollection

variable {V : Type*} [ORingStructure V] {s : ℕ}

def StrictCollection (V : Type*) [ORingStructure V] (s : ℕ) : Prop :=
  ∀ {n : ℕ} {θ : ArithmeticSemisentence (n + 2)}, StrictHierarchy 𝚺 s θ →
    ∀ (e : Fin n → V) (a : V), (∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) →
      ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ

lemma StrictCollection.of_le {s' : ℕ} (h : StrictCollection V s') (hs : s ≤ s') :
    StrictCollection V s := fun hθ ↦ h (hθ.mono hs)

lemma strictCollection_of_models_collectionAxiom [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (h : ∀ ψ : ArithmeticSemiformula ℕ 2, StrictHierarchy 𝚺 s ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence)) :
    StrictCollection V s := fun hθ e a hex ↦
  exists_bound_of_models_collectionAxiom (h _ (hθ.rew _)) e a hex

lemma strictCollection_of_ISigma {s : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] (hs : 0 < s) : StrictCollection V s := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega);
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (n := n + 1);
  show StrictCollection V (n + 1);
  exact strictCollection_of_models_collectionAxiom fun ψ hψ ↦
    consequence_iff.mp (Theory.Proof.sound
      (ISigma.provable_collectionAxiom_of_hierarchy n hψ.hierarchy)) V inferInstance;

end strictCollection

end FFL.FirstOrder.Arithmetic
