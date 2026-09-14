module

public import Foundation.FirstOrder.Arithmetic.BoundedCollection

/-!
# The collection schemata `𝗕𝚺` and `𝗕𝚷` in models, their equivalence, and `𝗜𝚺` from `𝗕𝚺`

## References

- [HP98, §I.2(a), Lemma I.2.9, Lemma I.2.10, Lemma I.2.11, Lemma I.2.15]
- [Bus98, Theorem 1.2.9(a)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {n : ℕ}

section models

/-! ### Collection axioms in models -/

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

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

lemma exists_bound_of_definable {Γ : Polarity} {s : ℕ}
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy Γ s ψ →
      V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom ψ))
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

instance (Γ : Polarity) (n : ℕ) : Consistent (𝗕 Γ n) :=
  (𝗕 Γ n).consistent_of_sound (Eq ⊥) rfl

end standardModel

section BSigma_ISigma

/-! ### `𝗕𝚺 (n + 1)` below `𝗜𝚺 (n + 1)` -/

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

@[instance]
theorem BSigma_weakerThan_ISigma : 𝗕𝚺 (n + 1) ⪯ 𝗜𝚺 (n + 1) := WeakerThan.ofAxm! <| by
  rintro σ (hσ | ⟨φ, hφ, rfl⟩);
  . exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega))
      (by_axm hσ);
  . exact ISigma.provable_collectionAxiom_of_hierarchy n hφ;

instance : 𝗕𝚺 n ⪯ 𝗜𝚺 (n + 1) := WeakerThan.trans
  (CollectionOnHierarchy_weakerThan_of_le (by omega)) $ BSigma_weakerThan_ISigma

instance : 𝗕𝚺 n ⪯ 𝗣𝗔 :=
  WeakerThan.trans (inferInstance : 𝗕𝚺 n ⪯ 𝗜𝚺 (n + 1)) inferInstance

end BSigma_ISigma

section models_CollectionOnHierarchy

/-! ### Models of `𝗕 Γ s` -/

variable {Γ : Polarity} {s : ℕ}

-- This is stated as a `lemma`, not an `instance`, since `Γ` and `s` do not occur in the
-- conclusion `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`, so instance search cannot infer them.
lemma models_paMinus_of_models_CollectionOnHierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕 Γ s) inferInstance

lemma exists_bound_of_models_CollectionOnHierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {m : ℕ}
    {θ : ArithmeticSemisentence (m + 2)} (hθ : Hierarchy Γ s θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := Γ) (s := s)
  exists_bound_of_models_collectionAxiom
    (models_of_mem (T := 𝗕 Γ s)
      (Set.mem_union_right _ (mem_CollectionScheme_of_mem (hθ.rew _)))) e a hex

end models_CollectionOnHierarchy

section BSigma_succ_BPi

/-! ### `𝗕𝚺 (n + 1)` and `𝗕𝚷 n` -/

variable {m : ℕ}

private structure MonotoneWitness (V : Type*) [ORingStructure V]
  (χ : ArithmeticSemisentence (m + 1)) (θ : ArithmeticSemisentence m) : Prop where
  monotone : ∀ (e : Fin m → V) (v v' : V), v ≤ v' → V ⊧/(v :> e) χ → V ⊧/(v' :> e) χ
  sound : ∀ (e : Fin m → V) (v : V), V ⊧/(v :> e) χ → V ⊧/e θ
  complete : ∀ e : Fin m → V, V ⊧/e θ → ∃ v, V ⊧/(v :> e) χ

private lemma monotoneWitness_bShift (θ : ArithmeticSemisentence m) : MonotoneWitness V (Rew.bShift ▹ θ) θ := by
  constructor;
  . intro e v v' _ h; simpa using h;
  . intro e v h; simpa using h;
  . intro e h; exact ⟨0, by simpa using h⟩;

private lemma eval_bexsLT_swap01 (χ : ArithmeticSemisentence (m + 2)) (e : Fin m → V)
    (v : V) :
    V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) ↔
      ∃ x < v, V ⊧/(v :> x :> e) χ := by
  simp only [Semiformula.eval_bexsLT];
  exact exists_congr fun x ↦ and_congr (by simp) (Semiformula.eval_swap01 χ x v e);

section

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n]

omit [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n] in
private lemma exists_monotoneWitness_of_pi {θ : ArithmeticSemisentence m}
    (h : Hierarchy 𝚷 n θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ MonotoneWitness V χ θ :=
  ⟨Rew.bShift ▹ θ, h.rew _, monotoneWitness_bShift θ⟩

private lemma exists_monotoneWitness_ball {θ : ArithmeticSemisentence (m + 1)}
    {χ : ArithmeticSemisentence (m + 2)} (u : ArithmeticSemiterm Empty m)
    (hχ : Hierarchy 𝚷 n χ) (hM : MonotoneWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ' ∧
      MonotoneWitness V χ' (θ.ballLT u) := by
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
      obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n) hχ e
        (u.valb e) fun x hx ↦ hcomplete (x :> e) (h x hx);
      exact ⟨w, (heval e w).mpr fun x hx ↦ (hw x hx).elim fun v hv ↦
        hmono (x :> e) v w hv.1 hv.2⟩;

omit [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n] in
private lemma exists_monotoneWitness_bexs {θ : ArithmeticSemisentence (m + 1)}
    {χ : ArithmeticSemisentence (m + 2)} (u : ArithmeticSemiterm Empty m)
    (hχ : Hierarchy 𝚷 n χ) (hM : MonotoneWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ' ∧
      MonotoneWitness V χ' (θ.bexsLT u) := by
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

private lemma exists_monotoneWitness_exs {θ : ArithmeticSemisentence (m + 1)}
    {χ : ArithmeticSemisentence (m + 2)} (hχ : Hierarchy 𝚷 n χ) (hM : MonotoneWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ' ∧
      MonotoneWitness V χ' (∃¹ θ) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n);
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

private lemma exists_monotoneWitness_of_hierarchy :
    ∀ {m : ℕ} {θ : ArithmeticSemisentence m}, Hierarchy 𝚺 (n + 1) θ →
      ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ MonotoneWitness V χ θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n);
  have key : ∀ (c : ℕ) {m : ℕ} {θ : ArithmeticSemisentence m}, θ.complexity ≤ c →
      Hierarchy 𝚺 (n + 1) θ →
        ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ MonotoneWitness V χ θ := by
    intro c;
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
  intro m θ hθ;
  exact key θ.complexity le_rfl hθ;

lemma exists_pi_eval_iff {φ : ArithmeticSemiformula ℕ 1} (hφ : Hierarchy 𝚺 (n + 1) φ) (f : ℕ → V) :
    ∃ χ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 n χ ∧
      ∀ x : V, φ.Eval ![x] f ↔ ∃ w, χ.Eval ![x, w] f := by
  obtain ⟨χ, hχ, -, hsound, hcomplete⟩ :=
    exists_monotoneWitness_of_hierarchy (V := V)
      (θ := (φ.toSemisentence ![#0] : ArithmeticSemisentence (φ.fvSup + 1))) (hφ.rew _);
  use Rew.embSubsts (#1 :> #0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ χ;
  and_intros;
  . exact hχ.rew _;
  . intro x;
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
    rw [← φ.eval_toSemisentence_one x f];
    constructor;
    . intro h;
      obtain ⟨w, hw⟩ := hcomplete (x :> fun i : Fin φ.fvSup ↦ f i) h;
      exact ⟨w, (hval w).mpr hw⟩;
    . rintro ⟨w, hw⟩;
      exact hsound (x :> fun i : Fin φ.fvSup ↦ f i) w ((hval w).mp hw);

private lemma exists_bound_sigma_succ_of_models_BPi {θ : ArithmeticSemisentence (m + 2)}
    (hθ : Hierarchy 𝚺 (n + 1) θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n);
  obtain ⟨χ, hχ, hmono, hsound, hcomplete⟩ := exists_monotoneWitness_of_hierarchy (V := V) hθ;
  obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n)
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

lemma models_collectionAxiom_of_models_BPi {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) :
    V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ) : ArithmeticSentence) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n);
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

theorem BPi.provable_collectionAxiom_of_hierarchy (n : ℕ) {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy 𝚺 (n + 1) φ) : 𝗕𝚷 n ⊢ .univCl (collectionAxiom φ) := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  exact models_collectionAxiom_of_models_BPi hφ;

theorem BSigma_succ_weakerThan_BPi (n : ℕ) : 𝗕𝚺 (n + 1) ⪯ 𝗕𝚷 n :=
  WeakerThan.ofAxm! <| by
    rintro σ (hσ | ⟨φ, hφ, rfl⟩);
    . exact WeakerThan.pbl (h := (inferInstance : 𝗜𝚺₀ ⪯ 𝗕𝚷 n)) (by_axm hσ);
    . exact BPi.provable_collectionAxiom_of_hierarchy n hφ;

theorem BSigma_succ_equiv_BPi (n : ℕ) : 𝗕𝚺 (n + 1) ≊ 𝗕𝚷 n :=
  Equiv.antisymm_iff.mpr
    ⟨BSigma_succ_weakerThan_BPi n, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 n⟩

end BSigma_succ_BPi

section ISigma_BSigma_succ

/-! ### `𝗜𝚺 n` from `𝗕𝚺 (n + 1)` -/

section models

private lemma definable_step {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) :
    𝚷-[n + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
  have hex : 𝚺-[n + 1].DefinablePred fun x ↦ ∃ z, Q x z := by
    apply HierarchySymbol.Definable.exs;
    exact HierarchySymbol.Definable.of_iff
      ((hQ.of_lt (s := n + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
  apply HierarchySymbol.Definable.or;
  . exact HierarchySymbol.Definable.of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
  . exact HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2 (hQ.of_lt (s := n + 1) (Γ := 𝚷) (by simp))
        ![‘#0 + 1’, #1]) (by intro v; simp);

private lemma definable_bounded {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) (a u : V) :
    𝚷-[n].DefinablePred fun x ↦ ∃ y < u, Q x y ∨ a < x := by
  have hlt : 𝚷-[n].Definable fun w : Fin 2 → V ↦ a < w 1 :=
    HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2
        (inferInstance : 𝚷-[n].DefinableRel (LT.lt : V → V → Prop)) ![&a, #1])
      (by intro w; simp);
  have h : 𝚷-[n].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&u : ArithmeticSemiterm V 1).val v id, Q (v 0) y ∨ a < v 0 := by
    apply HierarchySymbol.Definable.bexs;
    exact HierarchySymbol.Definable.of_iff ((hQ.retraction ![1, 0]).or hlt) (by intro w; simp);
  exact h.of_iff (by intro v; simp);

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n]

lemma succ_induction_of_exists_pi
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (n + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
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
    apply InductionOnHierarchy.succ_induction 𝚷 n (definable_bounded hQ a _)
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

private lemma models_ISigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 2)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕𝚺 (n + 2)) inferInstance;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n := models_of_ss inferInstance
    ((CollectionOnHierarchy_subset_BSigma_succ 𝚷 n).trans
    (CollectionOnHierarchy_subset_mono (Nat.le_succ (n + 1))));
  have hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (n + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence) := fun _ hψ ↦
    models_of_mem (T := 𝗕𝚺 (n + 2))
      (Set.mem_union_right _ (mem_CollectionScheme_of_mem (hψ.accum 𝚺)));
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (n + 1)) by
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

lemma models_ISigma_of_models_BSigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := by
  rename_i hn;
  induction n generalizing hn with
  | zero =>
    exact models_of_subtheory (T := 𝗜𝚺₀) (U := 𝗕𝚺 1) inferInstance;
  | succ n ih =>
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 1) := models_of_ss inferInstance $ CollectionOnHierarchy_subset_mono $ Nat.le_succ (n + 1);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := ih;
    exact models_ISigma_succ;

theorem ISigma_weakerThan_BSigma_succ (n : ℕ) : 𝗜𝚺 n ⪯ 𝗕𝚺 (n + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma_of_models_BSigma_succ

end theorems

end ISigma_BSigma_succ

end FFL.FirstOrder.Arithmetic
