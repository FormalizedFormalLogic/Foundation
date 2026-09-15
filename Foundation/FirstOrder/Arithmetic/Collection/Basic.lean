module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The collection schemata `𝗕𝚺` and `𝗕𝚷` in models, and `𝗕𝚺 (s + 1)` below `𝗜𝚺 (s + 1)`

## References

- [HP98]
- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section models

/-! ### Collection axioms in models -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- `V` satisfies the collection axiom for `φ` exactly when, for every parameter assignment and
every `a`, witnesses chosen for all `x < a` admit a common bound `b`. -/
lemma models_collectionAxiom_iff (φ : ArithmeticSemiformula ℕ 2) :
    V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom φ) ↔
      ∀ f : ℕ → V, ∀ a : V, (∀ x < a, ∃ y, φ.Eval ![x, y] f) →
        ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f := by
  simp [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
    Semiformula.eval_bexsLT, Semiformula.eval_substs];

/-- Under the collection axiom for `θ` with its parameters substituted, witnesses `u` for the
values `x < a` can be chosen below a single bound `w`. -/
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

/-- If `V` satisfies collection for every `Hierarchy Γ s` formula, then a `Γ-[s]`-definable
relation that is total below `a` has all its witnesses below a single bound `b`. -/
lemma exists_bound_of_definable {Γ : Polarity} {s : ℕ}
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy Γ s ψ → V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom ψ))
    {R : V → V → Prop} (hR : Γ-[s].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  obtain ⟨e, ψ, hψ, hiff⟩ := exists_hierarchy_eval_iff hR;
  have heval : ∀ x y : V, R x y ↔ ψ.Eval ![x, y] e := fun x y ↦ by simpa using hiff ![x, y];
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff ψ).mp (hcol ψ hψ) e a
    fun x hx ↦ (h x hx).imp fun y hy ↦ (heval x y).mp hy;
  exact ⟨b, fun x hx ↦ (hb x hx).imp fun y hy ↦ ⟨hy.1, (heval x y).mpr hy.2⟩⟩;

end models

section standardModel

/-! ### The standard model -/

instance models_CollectionOnHierarchy (Γ : Polarity) (s : ℕ) : ℕ↓[ℒₒᵣ] ⊧* 𝗕 Γ s := by
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

instance (Γ : Polarity) (s : ℕ) : Consistent (𝗕 Γ s) :=
  (𝗕 Γ s).consistent_of_sound (Eq ⊥) rfl

end standardModel

section boundedWitness

/-! ### A single bound for a `𝚺 (s + 1)` predicate -/

variable {V : Type*} {n s : ℕ} (e : Fin n → V)

private def collectionCore (θ : ArithmeticSemisentence (n + 2)) :
    ArithmeticSemiformula V 4 :=
  Rew.embSubsts (#0 :> #1 :> fun i ↦ (&(e i) : ArithmeticSemiterm V 4)) ▹ θ

private def collectionMotive (θ : ArithmeticSemisentence (n + 2)) (a : V) :
    ArithmeticSemiformula V 1 :=
  let cond : ArithmeticSemiformula V 3 :=
    Semiformula.rel Language.LT.lt ![(#0 : ArithmeticSemiterm V 3), (&a : ArithmeticSemiterm V 3)]
  let inner : ArithmeticSemiformula V 3 := (collectionCore e θ).bexsLTSucc (#1 : ArithmeticSemiterm V 3)
  ∃¹ ((cond 🡒 inner).ballLT (#1 : ArithmeticSemiterm V 2))

variable {θ : ArithmeticSemisentence (n + 2)}

private lemma hierarchy_collectionCore (hθ : Hierarchy 𝚺 (s + 1) θ) :
    Hierarchy 𝚺 (s + 1) (collectionCore e θ) := by
  simp [collectionCore, hθ];

private lemma hierarchy_collectionMotive (hθ : Hierarchy 𝚺 (s + 1) θ) (a : V) :
    Hierarchy 𝚺 (s + 1) (collectionMotive e θ a) := by
  have : Hierarchy 𝚺 (s + 1) (collectionCore e θ) := hierarchy_collectionCore e hθ;
  simp [collectionMotive, this];

variable [ORingStructure V]

private lemma eval_collectionCore (u x w y : V) :
    (collectionCore e θ).Eval (u :> x :> w :> ![y]) id ↔ V ⊧/(u :> x :> e) θ := by
  simp only [collectionCore, Semiformula.eval_embSubsts, Function.comp_def];
  exact Iff.of_eq (congrArg (fun b ↦ Semiformula.Evalb (M := V) b θ)
    (Fin.funext_two (by simp) (by simp) fun i ↦ by simp));

private lemma eval_collectionMotive [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (a : V) (v : Fin 1 → V) :
    (collectionMotive e θ a).Eval v id ↔
      ∃ w, ∀ x < v 0, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  rw [Matrix.fun_eq_vec_one v];
  simp [collectionMotive, Semiformula.eval_ballLT, Semiformula.eval_bexsLTSucc,
    Arithmetic.lt_succ_iff_le, eval_collectionCore, Function.comp_def];

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)]

private lemma collectionMotive_definable (hθ : Hierarchy 𝚺 (s + 1) θ) (a : V) :
    𝚺-[s + 1].DefinablePred (fun y ↦ ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ) := by
  have := mod_paMinus_of_ISigma (V := V) (s := s + 1);
  exact HierarchySymbol.Definable.mkPolarity (collectionMotive e θ a)
    (hierarchy_collectionMotive e hθ a) (fun v ↦ (eval_collectionMotive e a v).symm);

/-- In a model of `𝗜𝚺 (s + 1)`, witnesses for a `𝚺 (s + 1)` formula `θ` at every `x < a` can be
chosen below a single bound `w`. -/
theorem sigma_exists_bound_witness {θ : ArithmeticSemisentence (n + 2)} (hθ : Hierarchy 𝚺 (s + 1) θ)
    (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have := mod_paMinus_of_ISigma (V := V) (s := s + 1);
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 (s + 1)
      (P := fun y ↦ ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ)
      (hP := collectionMotive_definable e hθ a);
    . exact ⟨0, fun x hx _ ↦ absurd hx (by simp)⟩;
    . rintro y ⟨w, hw⟩;
      rcases lt_or_ge y a with hya | hya;
      . obtain ⟨u₀, hu₀⟩ := h y hya;
        use max w u₀;
        intro x hx _;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        . obtain ⟨u, hu, hPu⟩ := hw x hx (lt_trans hx hya);
          exact ⟨u, le_trans hu (le_max_left w u₀), hPu⟩;
        . exact ⟨u₀, le_max_right w u₀, hu₀⟩;
      . use w;
        intro x hx hxa;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        . exact hw x hx hxa;
        . exact absurd hxa (not_lt.mpr hya);
  obtain ⟨w, hw⟩ := key (a + 1);
  exact ⟨w, fun x hx ↦ hw x (lt_trans hx (lt_add_one a)) hx⟩;

end boundedWitness

variable {V : Type*} [ORingStructure V] {s : ℕ}

section BSigma_ISigma

/-! ### `𝗕𝚺 (s + 1)` below `𝗜𝚺 (s + 1)` -/

theorem ISigma.provable_collectionAxiom_of_hierarchy (s : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (s + 1) φ) : 𝗜𝚺 (s + 1) ⊢ .univCl (collectionAxiom φ) := by
  apply Arithmetic.complete.{0};
  intro M _ hMT;
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := s + 1);
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

@[instance]
theorem BSigma_weakerThan_ISigma : 𝗕𝚺 (s + 1) ⪯ 𝗜𝚺 (s + 1) := WeakerThan.ofAxm! <| by
  rintro σ (hσ | ⟨φ, hφ, rfl⟩);
  . exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega))
      (by_axm hσ);
  . exact ISigma.provable_collectionAxiom_of_hierarchy s hφ;

@[instance]
theorem BSigma_weakerThan_ISigma_succ : 𝗕𝚺 s ⪯ 𝗜𝚺 (s + 1) :=
  WeakerThan.trans (CollectionOnHierarchy_weakerThan_of_le (by omega)) BSigma_weakerThan_ISigma

@[instance]
theorem BSigma_weakerThan_Peano : 𝗕𝚺 s ⪯ 𝗣𝗔 :=
  WeakerThan.trans BSigma_weakerThan_ISigma_succ (inferInstance : 𝗜𝚺 (s + 1) ⪯ 𝗣𝗔)

end BSigma_ISigma

section models_CollectionOnHierarchy

/-! ### Models of `𝗕 Γ s` -/

variable {Γ : Polarity} {s : ℕ}

-- This is stated as a `lemma`, not an `instance`, since `Γ` and `s` do not occur in the
-- conclusion `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`, so instance search cannot infer them.
lemma models_paMinus_of_models_CollectionOnHierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕 Γ s) inferInstance

/-- In a model of `𝗕 Γ s`, witnesses for a `Hierarchy Γ s` formula `θ` at every `x < a` can be
chosen below a single bound `w`. -/
lemma exists_bound_of_models_CollectionOnHierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {m : ℕ}
    {θ : ArithmeticSemisentence (m + 2)} (hθ : Hierarchy Γ s θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := Γ) (s := s);
  exists_bound_of_models_collectionAxiom
    (models_of_mem (T := 𝗕 Γ s)
    (Set.mem_union_right _ (mem_CollectionScheme_of_mem (hθ.rew _)))) e a hex

end models_CollectionOnHierarchy

end FFL.FirstOrder.Arithmetic
