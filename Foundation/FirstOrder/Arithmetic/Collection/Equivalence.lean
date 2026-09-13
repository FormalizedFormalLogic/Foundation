module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# The collection schemata `𝗕𝚺 (n + 1)` and `𝗕𝚷 n`

## References

- [HP98, §I.2(a), 0.30, Lemma I.2.10]
- [Bus98, Theorem 1.2.9(a)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {n s : ℕ}

def HierarchyCollection (V : Type*) [ORingStructure V] (Γ : Polarity) (s : ℕ) : Prop :=
  ∀ {n : ℕ} {θ : ArithmeticSemisentence (n + 2)}, Hierarchy Γ s θ →
    ∀ (e : Fin n → V) (a : V), (∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) →
      ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ

lemma hierarchyCollection_of_models_collectionAxiom [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (h : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy Γ s ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence)) :
    HierarchyCollection V Γ s := fun hθ e a hex ↦
  exists_bound_of_models_collectionAxiom (h _ (hθ.rew _)) e a hex

lemma hierarchyCollection_of_models_BPi (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n] :
    HierarchyCollection V 𝚷 n :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕𝚷 n) inferInstance
  hierarchyCollection_of_models_collectionAxiom fun _ hψ ↦
    models_of_mem (T := 𝗕𝚷 n) (Set.mem_union_right _ (mem_CollectionScheme_of_mem hψ))

private def BoundsWitness (V : Type*) [ORingStructure V] {m : ℕ}
    (χ θ : ArithmeticSemisentence (m + 1)) : Prop :=
  (∀ (e : Fin m → V) (v v' : V), v ≤ v' → V ⊧/(v :> e) χ → V ⊧/(v' :> e) χ) ∧
    (∀ (e : Fin m → V) (v : V), V ⊧/(v :> e) χ → ∃ u < v, V ⊧/(u :> e) θ) ∧
    (∀ (e : Fin m → V) (u : V), V ⊧/(u :> e) θ → ∃ v, V ⊧/(v :> e) χ)

section

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

private lemma exists_boundsWitness_of_hierarchy {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}
    (h : Hierarchy 𝚷 n θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ BoundsWitness V χ θ := by
  have heval : ∀ (e : Fin m → V) (v : V),
      V ⊧/(v :> e) ((θ ⇜ (#0 :> (#·.succ.succ))).bexsLT #0) ↔ ∃ u < v, V ⊧/(u :> e) θ := by
    intro e v;
    simp only [Semiformula.eval_bexsLT];
    exact exists_congr fun u ↦ and_congr (by simp) (Semiformula.eval_insert1 θ u v e);
  use (θ ⇜ (#0 :> (#·.succ.succ))).bexsLT #0;
  and_intros;
  . simpa using h;
  . intro e v v' hv hχ;
    obtain ⟨u, hu, hθ⟩ := (heval e v).mp hχ;
    exact (heval e v').mpr ⟨u, lt_of_lt_of_le hu hv, hθ⟩;
  . exact fun e v hχ ↦ (heval e v).mp hχ;
  . exact fun e u hu ↦ ⟨u + 1, (heval e (u + 1)).mpr ⟨u, by simp, hu⟩⟩;

private lemma exists_boundsWitness_exs {m : ℕ} {θ χ : ArithmeticSemisentence (m + 2)}
    (hχ : Hierarchy 𝚷 n χ) (hB : BoundsWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ' ∧ BoundsWitness V χ' (∃¹ θ) := by
  obtain ⟨hmono, hbound, hwitness⟩ := hB;
  have heval : ∀ (e : Fin m → V) (v : V),
      V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) ↔
        ∃ u < v, V ⊧/(v :> u :> e) χ := by
    intro e v;
    simp only [Semiformula.eval_bexsLT];
    exact exists_congr fun u ↦ and_congr (by simp) (Semiformula.eval_swap01 χ u v e);
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0;
  and_intros;
  . simpa using hχ;
  . intro e v v' hv h;
    obtain ⟨u, hu, h⟩ := (heval e v).mp h;
    exact (heval e v').mpr ⟨u, lt_of_lt_of_le hu hv, hmono (u :> e) v v' hv h⟩;
  . intro e v h;
    obtain ⟨u, hu, h⟩ := (heval e v).mp h;
    obtain ⟨z, -, hz⟩ := hbound (u :> e) v h;
    exact ⟨u, hu, Semiformula.eval_ex.mpr ⟨z, hz⟩⟩;
  . intro e u h;
    obtain ⟨z, hz⟩ := Semiformula.eval_ex.mp h;
    obtain ⟨v, hv⟩ := hwitness (u :> e) z hz;
    exact ⟨max (u + 1) v, (heval e (max (u + 1) v)).mpr
      ⟨u, lt_of_lt_of_le (lt_add_one u) (le_max_left _ _),
        hmono (u :> e) v (max (u + 1) v) (le_max_right _ _) hv⟩⟩;

private lemma exists_boundsWitness_of_strictHierarchy :
    ∀ {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}, StrictHierarchy 𝚺 (n + 1) θ →
      ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ BoundsWitness V χ θ := by
  have key : ∀ (c : ℕ) {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}, θ.complexity ≤ c →
      StrictHierarchy 𝚺 (n + 1) θ →
        ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ BoundsWitness V χ θ := by
    intro c;
    induction c with
    | zero =>
      intro m θ hc hθ;
      cases hθ with
      | ofAlt h => exact exists_boundsWitness_of_hierarchy h.hierarchy;
      | exs h => simp at hc;
    | succ c ih =>
      intro m θ hc hθ;
      cases hθ with
      | ofAlt h => exact exists_boundsWitness_of_hierarchy h.hierarchy;
      | exs h =>
        obtain ⟨χ, hχ, hB⟩ := ih (by simpa using hc) h;
        exact exists_boundsWitness_exs hχ hB;
  intro m θ hθ;
  exact key θ.complexity le_rfl hθ;

lemma exists_pi_eval_iff (hC : StrictCollection V (n + 1)) {φ : ArithmeticSemiformula ℕ 1}
    (hφ : Hierarchy 𝚺 (n + 1) φ) (f : ℕ → V) :
    ∃ χ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 n χ ∧
      ∀ x : V, φ.Eval ![x] f ↔ ∃ w, χ.Eval ![x, w] f := by
  obtain ⟨ψ, hψ, hψiff⟩ := exists_strictHierarchy_eval_iff (V := V) hC hφ f;
  obtain ⟨χ, hχ, -, hbound, hwitness⟩ :=
    exists_boundsWitness_of_strictHierarchy (V := V)
      (θ := (Rew.bShift ▹ ψ.toSemisentence ![#0] : ArithmeticSemisentence (ψ.fvSup + 2)))
      ((hψ.rew _).rew _);
  have hshift : ∀ u x : V,
      V ⊧/(u :> x :> fun i : Fin ψ.fvSup ↦ f i) (Rew.bShift ▹ ψ.toSemisentence ![#0]) ↔
        ψ.Eval ![x] f := fun u x ↦ by simpa using ψ.eval_toSemisentence_one x f;
  use Rew.embSubsts (#1 :> #0 :> fun i : Fin ψ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ χ;
  and_intros;
  . exact hχ.rew _;
  . intro x;
    have hval : ∀ w : V,
        (Rew.embSubsts (#1 :> #0 :> fun i : Fin ψ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹
          χ).Eval ![x, w] f ↔ V ⊧/(w :> x :> fun i : Fin ψ.fvSup ↦ f i) χ := by
      intro w;
      simp only [Semiformula.eval_embSubsts];
      apply Iff.of_eq;
      apply congrArg (fun b ↦ Semiformula.Evalb (M := V) b χ);
      funext i;
      cases i using Fin.cases with
      | zero => simp;
      | succ i =>
        cases i using Fin.cases with
        | zero => simp;
        | succ i => simp;
    rw [← hψiff x];
    constructor;
    . intro h;
      obtain ⟨v, hv⟩ := hwitness (x :> fun i : Fin ψ.fvSup ↦ f i) 0 ((hshift 0 x).mpr h);
      exact ⟨v, (hval v).mpr hv⟩;
    . rintro ⟨w, hw⟩;
      obtain ⟨u, -, hu⟩ := hbound (x :> fun i : Fin ψ.fvSup ↦ f i) w ((hval w).mp hw);
      exact (hshift u x).mp hu;

lemma strictCollection_succ_of_hierarchyCollection (hC : HierarchyCollection V 𝚷 n) :
    StrictCollection V (n + 1) := by
  intro m θ hθ e a hex;
  obtain ⟨χ, hχ, -, hbound, hwitness⟩ := exists_boundsWitness_of_strictHierarchy (V := V) hθ;
  obtain ⟨w, hw⟩ := hC hχ e a fun x hx ↦ (hex x hx).elim fun u hu ↦ hwitness (x :> e) u hu;
  use w;
  intro x hx;
  obtain ⟨v, hvw, hv⟩ := hw x hx;
  obtain ⟨u, huv, hu⟩ := hbound (x :> e) v hv;
  exact ⟨u, le_of_lt (lt_of_lt_of_le huv hvw), hu⟩;

lemma hierarchyCollection_sigma_succ_of_pi (hC : HierarchyCollection V 𝚷 n) :
    HierarchyCollection V 𝚺 (n + 1) := by
  intro m θ hθ e a hex;
  have hS : StrictCollection V (n + 1) := strictCollection_succ_of_hierarchyCollection hC;
  obtain ⟨θ', hθ'⟩ := Prenex.models_exists_prenex (Γ := 𝚺) (s := n + 1) hθ;
  have hiff : ∀ b : Fin (m + 2) → V, V ⊧/b θ ↔ V ⊧/b θ'.val := hθ' V hS;
  obtain ⟨w, hw⟩ := hS (θ := θ'.val) Prenex.val_strictHierarchy e a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (hiff _).mp hu;
  exact ⟨w, fun x hx ↦ (hw x hx).imp fun u hu ↦ ⟨hu.1, (hiff _).mpr hu.2⟩⟩;

lemma models_collectionAxiom_of_hierarchyCollection (hC : HierarchyCollection V 𝚷 n)
    {φ : ArithmeticSemiformula ℕ 2} (hφ : Hierarchy 𝚺 (n + 1) φ) :
    V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ) : ArithmeticSentence) := by
  rw [models_collectionAxiom_iff];
  intro f a h;
  obtain ⟨w, hw⟩ := hierarchyCollection_sigma_succ_of_pi hC (θ := φ.toSemisentence ![#1, #0])
    (hφ.rew _) (fun i : Fin φ.fvSup ↦ f i) a <| by
      intro x hx;
      obtain ⟨y, hy⟩ := h x hx;
      exact ⟨y, (φ.eval_toSemisentence_two x y f).mpr hy⟩;
  exact ⟨w + 1, fun x hx ↦ (hw x hx).imp fun u hu ↦
    ⟨Arithmetic.lt_succ_iff_le.mpr hu.1, (φ.eval_toSemisentence_two x u f).mp hu.2⟩⟩;

end

theorem BPi.provable_collectionAxiom_of_hierarchy (n : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) : 𝗕𝚷 n ⊢ .univCl (collectionAxiom φ) := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕𝚷 n) inferInstance;
  exact models_collectionAxiom_of_hierarchyCollection (hierarchyCollection_of_models_BPi M) hφ;

theorem BSigma_succ_weakerThan_BPi (n : ℕ) : 𝗕𝚺 (n + 1) ⪯ 𝗕𝚷 n :=
  WeakerThan.ofAxm! <| by
    rintro σ (hσ | ⟨φ, hφ, rfl⟩);
    . exact WeakerThan.pbl (h := (inferInstance : 𝗜𝚺₀ ⪯ 𝗕𝚷 n)) (by_axm hσ);
    . exact BPi.provable_collectionAxiom_of_hierarchy n hφ;

theorem BSigma_succ_equiv_BPi (n : ℕ) : 𝗕𝚺 (n + 1) ≊ 𝗕𝚷 n :=
  Equiv.antisymm_iff.mpr
    ⟨BSigma_succ_weakerThan_BPi n, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 n⟩

end FFL.FirstOrder.Arithmetic
