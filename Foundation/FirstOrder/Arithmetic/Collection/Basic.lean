module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The collection schemata `𝗕𝚺` and `𝗕𝚷` in models, their equivalence, and `𝗜𝚺` from `𝗕𝚺`

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

section BSigma_succ_BPi

/-! ### `𝗕𝚺 (s + 1)` and `𝗕𝚷 s` -/

variable {m : ℕ}

private structure MonotoneWitness (V : Type*) [ORingStructure V]
  (χ : ArithmeticSemisentence (m + 1)) (θ : ArithmeticSemisentence m) : Prop where
  monotone : ∀ (e : Fin m → V) (v v' : V), v ≤ v' → V ⊧/(v :> e) χ → V ⊧/(v' :> e) χ
  sound : ∀ (e : Fin m → V) (v : V), V ⊧/(v :> e) χ → V ⊧/e θ
  complete : ∀ e : Fin m → V, V ⊧/e θ → ∃ v, V ⊧/(v :> e) χ

private lemma monotoneWitness_bShift (θ : ArithmeticSemisentence m) : MonotoneWitness V (Rew.bShift ▹ θ) θ := by
  constructor <;> simp;

private lemma eval_bexsLT_swap01 (χ : ArithmeticSemisentence (m + 2)) (e : Fin m → V) (v : V) :
  V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) ↔ ∃ x < v, V ⊧/(v :> x :> e) χ := by
  simp only [Semiformula.eval_bexsLT];
  exact exists_congr fun x ↦ and_congr (by simp) (Semiformula.eval_swap01 χ x v e);

section

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s]

omit [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s] in
private lemma exists_monotoneWitness_of_pi {θ} (h : Hierarchy 𝚷 s θ) :
  ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ ∧ MonotoneWitness V χ θ :=
  ⟨Rew.bShift ▹ θ, h.rew _, monotoneWitness_bShift θ⟩

private lemma exists_monotoneWitness_ball {θ χ} (u : ArithmeticSemiterm Empty m)
  (hχ : Hierarchy 𝚷 s χ) (hM : MonotoneWitness V χ θ) :
  ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ' ∧ MonotoneWitness V χ' (θ.ballLT u) := by
  obtain ⟨hmono, hsound, hcomplete⟩ := hM;
  have heval : ∀ (e : Fin m → V) (v : V),
      V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).ballLT (Rew.bShift u)) ↔
        ∀ x < u.valb e, V ⊧/(v :> x :> e) χ := by
    intro e v;
    simp only [Semiformula.eval_ballLT, Semiterm.val_bShift];
    exact forall_congr' fun x ↦ imp_congr_right fun _ ↦ Semiformula.eval_swap01 χ x v e;
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).ballLT (Rew.bShift u);
  and_intros;
  . simpa using hχ;
  . constructor;
    . intro e v v' hv h;
      exact (heval e v').mpr fun x hx ↦ hmono (x :> e) v v' hv ((heval e v).mp h x hx);
    . intro e v h;
      simp only [Semiformula.eval_ballLT];
      exact fun x hx ↦ hsound (x :> e) v ((heval e v).mp h x hx);
    . intro e h;
      simp only [Semiformula.eval_ballLT] at h;
      obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s) hχ e
        (u.valb e) fun x hx ↦ hcomplete (x :> e) (h x hx);
      exact ⟨w, (heval e w).mpr fun x hx ↦ (hw x hx).elim fun v hv ↦
        hmono (x :> e) v w hv.1 hv.2⟩;

omit [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s] in
private lemma exists_monotoneWitness_bexs {θ χ} (u : ArithmeticSemiterm Empty m)
  (hχ : Hierarchy 𝚷 s χ) (hM : MonotoneWitness V χ θ) :
  ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ' ∧ MonotoneWitness V χ' (θ.bexsLT u) := by
  obtain ⟨hmono, hsound, hcomplete⟩ := hM;
  have heval : ∀ (e : Fin m → V) (v : V),
      V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT (Rew.bShift u)) ↔
        ∃ x < u.valb e, V ⊧/(v :> x :> e) χ := by
    intro e v;
    simp only [Semiformula.eval_bexsLT, Semiterm.val_bShift];
    exact exists_congr fun x ↦ and_congr_right fun _ ↦ Semiformula.eval_swap01 χ x v e;
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT (Rew.bShift u);
  and_intros;
  . simpa using hχ;
  . constructor;
    . intro e v v' hv h;
      obtain ⟨x, hx, h⟩ := (heval e v).mp h;
      exact (heval e v').mpr ⟨x, hx, hmono (x :> e) v v' hv h⟩;
    . intro e v h;
      obtain ⟨x, hx, h⟩ := (heval e v).mp h;
      simp only [Semiformula.eval_bexsLT];
      exact ⟨x, hx, hsound (x :> e) v h⟩;
    . intro e h;
      simp only [Semiformula.eval_bexsLT] at h;
      obtain ⟨x, hx, h⟩ := h;
      obtain ⟨v, hv⟩ := hcomplete (x :> e) h;
      exact ⟨v, (heval e v).mpr ⟨x, hx, hv⟩⟩;

private lemma exists_monotoneWitness_exs  {θ χ}
  (hχ : Hierarchy 𝚷 s χ) (hM : MonotoneWitness V χ θ) :
  ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ' ∧ MonotoneWitness V χ' (∃¹ θ) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  obtain ⟨hmono, hsound, hcomplete⟩ := hM;
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0;
  and_intros;
  . simpa using hχ;
  . constructor;
    . intro e v v' hv h;
      obtain ⟨x, hx, h⟩ := (eval_bexsLT_swap01 χ e v).mp h;
      exact (eval_bexsLT_swap01 χ e v').mpr
        ⟨x, lt_of_lt_of_le hx hv, hmono (x :> e) v v' hv h⟩;
    . intro e v h;
      obtain ⟨x, -, h⟩ := (eval_bexsLT_swap01 χ e v).mp h;
      exact Semiformula.eval_ex.mpr ⟨x, hsound (x :> e) v h⟩;
    . intro e h;
      obtain ⟨x, hx⟩ := Semiformula.eval_ex.mp h;
      obtain ⟨v, hv⟩ := hcomplete (x :> e) hx;
      exact ⟨max (x + 1) v, (eval_bexsLT_swap01 χ e (max (x + 1) v)).mpr
        ⟨x, lt_of_lt_of_le (lt_add_one x) (le_max_left _ _),
          hmono (x :> e) v (max (x + 1) v) (le_max_right _ _) hv⟩⟩;

private lemma exists_monotoneWitness_of_complexity_le (c : ℕ) :
    ∀ {m : ℕ} {θ : ArithmeticSemisentence m}, θ.complexity ≤ c → Hierarchy 𝚺 (s + 1) θ →
      ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ ∧ MonotoneWitness V χ θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  induction c with
  | zero =>
    intro m θ hc hθ;
    cases hθ with
    | verum => exact exists_monotoneWitness_of_pi (by simp);
    | falsum => exact exists_monotoneWitness_of_pi (by simp);
    | rel => exact exists_monotoneWitness_of_pi (by simp);
    | nrel => exact exists_monotoneWitness_of_pi (by simp);
    | _ => simp [Semiformula.ball_eq, Semiformula.bexs_eq, Semiformula.imp_eq] at hc;
  | succ c ih =>
    intro m θ hc hθ;
    cases hθ with
    | verum => exact exists_monotoneWitness_of_pi (by simp);
    | falsum => exact exists_monotoneWitness_of_pi (by simp);
    | rel => exact exists_monotoneWitness_of_pi (by simp);
    | nrel => exact exists_monotoneWitness_of_pi (by simp);
    | and hφ hψ =>
      obtain ⟨χ₁, hχ₁, hmono₁, hsound₁, hcomplete₁⟩ := ih (by simp at hc; omega) hφ;
      obtain ⟨χ₂, hχ₂, hmono₂, hsound₂, hcomplete₂⟩ := ih (by simp at hc; omega) hψ;
      use χ₁ ⋏ χ₂;
      and_intros;
      . simp [hχ₁, hχ₂];
      . constructor;
        . intro e v v' hv h;
          exact ⟨hmono₁ e v v' hv h.1, hmono₂ e v v' hv h.2⟩;
        . intro e v h;
          exact ⟨hsound₁ e v h.1, hsound₂ e v h.2⟩;
        . intro e h;
          obtain ⟨v₁, hv₁⟩ := hcomplete₁ e h.1;
          obtain ⟨v₂, hv₂⟩ := hcomplete₂ e h.2;
          exact ⟨max v₁ v₂, hmono₁ e v₁ _ (le_max_left _ _) hv₁,
            hmono₂ e v₂ _ (le_max_right _ _) hv₂⟩;
    | or hφ hψ =>
      obtain ⟨χ₁, hχ₁, hmono₁, hsound₁, hcomplete₁⟩ := ih (by simp at hc; omega) hφ;
      obtain ⟨χ₂, hχ₂, hmono₂, hsound₂, hcomplete₂⟩ := ih (by simp at hc; omega) hψ;
      use χ₁ ⋎ χ₂;
      and_intros;
      . simp [hχ₁, hχ₂];
      . constructor;
        . intro e v v' hv h;
          exact h.imp (hmono₁ e v v' hv) (hmono₂ e v v' hv);
        . intro e v h;
          exact h.imp (hsound₁ e v) (hsound₂ e v);
        . intro e h;
          rcases h with h | h;
          . exact (hcomplete₁ e h).imp fun v hv ↦ by tauto;
          . exact (hcomplete₂ e h).imp fun v hv ↦ by tauto;
    | ball ht hφ =>
      obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
      obtain ⟨χ, hχ, hM⟩ :=
        ih (by simp [Semiformula.ball_eq, Semiformula.imp_eq] at hc; omega) hφ;
      exact exists_monotoneWitness_ball u hχ hM;
    | bexs ht hφ =>
      obtain ⟨u, rfl⟩ := Rew.positive_iff.mp ht;
      obtain ⟨χ, hχ, hM⟩ := ih (by simp [Semiformula.bexs_eq] at hc; omega) hφ;
      exact exists_monotoneWitness_bexs u hχ hM;
    | exs hφ =>
      obtain ⟨χ, hχ, hM⟩ := ih (by simp at hc; omega) hφ;
      exact exists_monotoneWitness_exs hχ hM;
    | sigma hφ =>
      exact exists_monotoneWitness_exs (hφ.rew _) (monotoneWitness_bShift _);
    | dummy_sigma hφ =>
      exact exists_monotoneWitness_of_pi hφ.all;

private lemma exists_monotoneWitness_of_hierarchy {θ : ArithmeticSemisentence m}
    (hθ : Hierarchy 𝚺 (s + 1) θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ ∧ MonotoneWitness V χ θ :=
  exists_monotoneWitness_of_complexity_le θ.complexity le_rfl hθ

/-- In a model of `𝗕𝚷 s`, every `𝚺 (s + 1)` formula in one free variable is equivalent to an
existential quantification of a `𝚷 s` formula. -/
lemma exists_pi_eval_iff {φ : ArithmeticSemiformula ℕ 1} (hφ : Hierarchy 𝚺 (s + 1) φ) (f : ℕ → V) :
  ∃ χ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 s χ ∧ ∀ x : V, φ.Eval ![x] f ↔ ∃ w, χ.Eval ![x, w] f := by
  obtain ⟨χ, hχ, -, hsound, hcomplete⟩ := exists_monotoneWitness_of_hierarchy (V := V)
    (θ := (φ.toSemisentence ![#0] : ArithmeticSemisentence (φ.fvSup + 1))) (hφ.rew _);
  use Rew.embSubsts (#1 :> #0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ χ;
  and_intros;
  . exact hχ.rew _;
  . intro x;
    rw [← φ.eval_toSemisentence_one x f];
    have hval : ∀ w : V,
        (Rew.embSubsts (#1 :> #0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹
          χ).Eval ![x, w] f ↔ V ⊧/(w :> x :> fun i : Fin φ.fvSup ↦ f i) χ := by
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
    constructor;
    . intro h;
      obtain ⟨w, hw⟩ := hcomplete (x :> fun i : Fin φ.fvSup ↦ f i) h;
      exact ⟨w, (hval w).mpr hw⟩;
    . rintro ⟨w, hw⟩;
      exact hsound (x :> fun i : Fin φ.fvSup ↦ f i) w ((hval w).mp hw);

private lemma exists_bound_sigma_succ_of_models_BPi {θ : ArithmeticSemisentence (m + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  obtain ⟨χ, hχ, hmono, hsound, hcomplete⟩ := exists_monotoneWitness_of_hierarchy (V := V) hθ;
  obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s)
    (θ := (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) (by simpa using hχ) e a <| by
      intro x hx;
      obtain ⟨u, hu⟩ := hex x hx;
      obtain ⟨v, hv⟩ := hcomplete (u :> x :> e) hu;
      exact ⟨max (u + 1) v, (eval_bexsLT_swap01 χ (x :> e) (max (u + 1) v)).mpr
        ⟨u, lt_of_lt_of_le (lt_add_one u) (le_max_left _ _),
          hmono (u :> x :> e) v (max (u + 1) v) (le_max_right _ _) hv⟩⟩;
  use w;
  intro x hx;
  obtain ⟨v, hvw, hv⟩ := hw x hx;
  obtain ⟨u, huv, hu⟩ := (eval_bexsLT_swap01 χ (x :> e) v).mp hv;
  exact ⟨u, le_of_lt (lt_of_lt_of_le huv hvw), hsound (u :> x :> e) v hu⟩;

lemma models_collectionAxiom_of_models_BPi (hφ : Hierarchy 𝚺 (s + 1) φ) :
  V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ)) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  rw [models_collectionAxiom_iff];
  intro f a h;
  obtain ⟨w, hw⟩ := exists_bound_sigma_succ_of_models_BPi (θ := φ.toSemisentence ![#1, #0])
    (hφ.rew _) (fun i : Fin φ.fvSup ↦ f i) a <| by
      intro x hx;
      obtain ⟨y, hy⟩ := h x hx;
      exact ⟨y, (φ.eval_toSemisentence_two x y f).mpr hy⟩;
  exact ⟨w + 1, fun x hx ↦ (hw x hx).imp fun u hu ↦
    ⟨Arithmetic.lt_succ_iff_le.mpr hu.1, (φ.eval_toSemisentence_two x u f).mp hu.2⟩⟩;

end

variable {s : ℕ}

theorem BPi.provable_collectionAxiom_of_hierarchy (hφ : Hierarchy 𝚺 (s + 1) φ)
  : 𝗕𝚷 s ⊢ .univCl (collectionAxiom φ) := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  exact models_collectionAxiom_of_models_BPi hφ;

@[instance]
theorem BSigma_succ_weakerThan_BPi : 𝗕𝚺 (s + 1) ⪯ 𝗕𝚷 s := WeakerThan.ofAxm! <| by
  rintro σ (hσ | ⟨φ, hφ, rfl⟩);
  . exact WeakerThan.pbl (h := (inferInstance : 𝗜𝚺₀ ⪯ 𝗕𝚷 s)) (by_axm hσ);
  . exact BPi.provable_collectionAxiom_of_hierarchy hφ;

@[instance]
theorem BSigma_succ_equiv_BPi : 𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s :=
  Equiv.antisymm_iff.mpr ⟨BSigma_succ_weakerThan_BPi, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 s⟩

end BSigma_succ_BPi

section ISigma_BSigma_succ

/-! ### `𝗜𝚺 s` from `𝗕𝚺 (s + 1)` -/

section models

private lemma definable_step {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) :
    𝚷-[s + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
  have hex : 𝚺-[s + 1].DefinablePred fun x ↦ ∃ z, Q x z := by
    apply HierarchySymbol.Definable.exs;
    exact HierarchySymbol.Definable.of_iff
      ((hQ.of_lt (s := s + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
  apply HierarchySymbol.Definable.or;
  . exact HierarchySymbol.Definable.of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
  . exact HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2 (hQ.of_lt (s := s + 1) (Γ := 𝚷) (by simp))
        ![‘#0 + 1’, #1]) (by intro v; simp);

private lemma definable_bounded {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) (a u : V) :
    𝚷-[s].DefinablePred fun x ↦ ∃ y < u, Q x y ∨ a < x := by
  have hlt : 𝚷-[s].Definable fun w : Fin 2 → V ↦ a < w 1 :=
    HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2
        (inferInstance : 𝚷-[s].DefinableRel (LT.lt : V → V → Prop)) ![&a, #1])
      (by intro w; simp);
  have h : 𝚷-[s].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&u : ArithmeticSemiterm V 1).val v id, Q (v 0) y ∨ a < v 0 := by
    apply HierarchySymbol.Definable.bexs;
    exact HierarchySymbol.Definable.of_iff ((hQ.retraction ![1, 0]).or hlt) (by intro w; simp);
  exact h.of_iff (by intro v; simp);

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s]

/-- Given collection for `𝚷 (s + 1)` formulas, successor induction holds for every predicate of
the form `fun x ↦ ∃ w, Q x w` with `Q` a `𝚷-[s]`-definable relation. -/
lemma succ_induction_of_exists_pi
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (s + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  intro a;
  obtain ⟨v, hv⟩ := exists_bound_of_definable hcol (definable_step hQ) a <| by
    intro x _;
    by_cases hx : ∃ z, Q x z;
    . exact ((hPQ (x + 1)).mp (succ x ((hPQ x).mpr hx))).imp fun w hw ↦ Or.inr hw;
    . exact ⟨0, Or.inl hx⟩;
  obtain ⟨w₀, hw₀⟩ := (hPQ 0).mp zero;
  have hpos : (0 : V) < max v (w₀ + 1) :=
    lt_of_lt_of_le (lt_of_le_of_lt (by simp) (lt_add_one w₀)) (le_max_right v (w₀ + 1));
  have key : ∀ x, ∃ y < max v (w₀ + 1), Q x y ∨ a < x := by
    apply InductionOnHierarchy.succ_induction 𝚷 s (definable_bounded hQ a _)
      ⟨w₀, lt_of_lt_of_le (lt_add_one w₀) (le_max_right v (w₀ + 1)), Or.inl hw₀⟩;
    rintro x ⟨y, -, hy | hy⟩;
    . by_cases hxa : x < a;
      . obtain ⟨z, hzv, hz | hz⟩ := hv x hxa;
        . exact absurd ⟨y, hy⟩ hz;
        . exact ⟨z, lt_of_lt_of_le hzv (le_max_left v (w₀ + 1)), Or.inl hz⟩;
      . exact ⟨0, hpos, Or.inr (lt_of_le_of_lt (not_lt.mp hxa) (lt_add_one x))⟩;
    . exact ⟨0, hpos, Or.inr (lt_trans hy (lt_add_one x))⟩;
  obtain ⟨y, -, hy | hy⟩ := key a;
  . exact (hPQ a).mpr ⟨y, hy⟩;
  . exact absurd hy (lt_irrefl a);

end models

section theorems

private lemma models_ISigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 2)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1) := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕𝚺 (s + 2)) inferInstance;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := models_of_ss inferInstance
    ((CollectionOnHierarchy_subset_BSigma_succ 𝚷 s).trans
    (CollectionOnHierarchy_subset_mono (Nat.le_succ (s + 1))));
  have hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (s + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence) := fun _ hψ ↦
    models_of_mem (T := 𝗕𝚺 (s + 2))
      (Set.mem_union_right _ (mem_CollectionScheme_of_mem (hψ.accum 𝚺)));
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (s + 1)) by
    simpa [ISigma, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩;
  simp only [InductionScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro f;
  obtain ⟨χ, hχ, hiff⟩ := exists_pi_eval_iff hφ f;
  exact succ_induction_of_exists_pi hcol (definableRel_of_hierarchy hχ f) hiff;

lemma models_ISigma_of_models_BSigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := by
  rename_i hn;
  induction s generalizing hn with
  | zero =>
    exact models_of_subtheory (T := 𝗜𝚺₀) (U := 𝗕𝚺 1) inferInstance;
  | succ s ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (s + 1) :=
      models_of_ss inferInstance $ CollectionOnHierarchy_subset_mono $ Nat.le_succ (s + 1);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := ih;
    exact models_ISigma_succ;

@[instance]
theorem ISigma_weakerThan_BSigma_succ : 𝗜𝚺 s ⪯ 𝗕𝚺 (s + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma_of_models_BSigma_succ

end theorems

end ISigma_BSigma_succ

end FFL.FirstOrder.Arithmetic
