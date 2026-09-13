module

public import Foundation.FirstOrder.Arithmetic.Collection.Basic

/-!
# The collection schemata `𝗕𝚺 (n + 1)` and `𝗕𝚷 n`

## References

- [HP98, §I.2(a), Lemma I.2.9, Lemma I.2.10]
- [Bus98, Theorem 1.2.9(a)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {n : ℕ}

private def MonotoneWitness (V : Type*) [ORingStructure V] {m : ℕ}
    (χ : ArithmeticSemisentence (m + 1)) (θ : ArithmeticSemisentence m) : Prop :=
  (∀ (e : Fin m → V) (v v' : V), v ≤ v' → V ⊧/(v :> e) χ → V ⊧/(v' :> e) χ) ∧
    (∀ (e : Fin m → V) (v : V), V ⊧/(v :> e) χ → V ⊧/e θ) ∧
    (∀ e : Fin m → V, V ⊧/e θ → ∃ v, V ⊧/(v :> e) χ)

private lemma monotoneWitness_bShift {m : ℕ} (θ : ArithmeticSemisentence m) :
    MonotoneWitness V (Rew.bShift ▹ θ) θ := by
  and_intros;
  . intro e v v' _ h; simpa using h;
  . intro e v h; simpa using h;
  . intro e h; exact ⟨0, by simpa using h⟩;

private lemma eval_bexsLT_swap01 {m : ℕ} (χ : ArithmeticSemisentence (m + 2)) (e : Fin m → V)
    (v : V) :
    V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) ↔
      ∃ x < v, V ⊧/(v :> x :> e) χ := by
  simp only [Semiformula.eval_bexsLT];
  exact exists_congr fun x ↦ and_congr (by simp) (Semiformula.eval_swap01 χ x v e);

section

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n]

omit [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n] in
private lemma exists_monotoneWitness_of_pi {m : ℕ} {θ : ArithmeticSemisentence m}
    (h : Hierarchy 𝚷 n θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ ∧ MonotoneWitness V χ θ :=
  ⟨Rew.bShift ▹ θ, h.rew _, monotoneWitness_bShift θ⟩

private lemma exists_monotoneWitness_ball {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}
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
private lemma exists_monotoneWitness_bexs {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}
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

private lemma exists_monotoneWitness_exs {m : ℕ} {θ : ArithmeticSemisentence (m + 1)}
    {χ : ArithmeticSemisentence (m + 2)} (hχ : Hierarchy 𝚷 n χ) (hM : MonotoneWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 n χ' ∧
      MonotoneWitness V χ' (∃¹ θ) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := n);
  obtain ⟨hmono, hsound, hcomplete⟩ := hM;
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0;
  and_intros;
  . simpa using hχ;
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

lemma hierarchyCollection_sigma_succ_of_pi : HierarchyCollection V 𝚺 (n + 1) := by
  intro m θ hθ e a hex;
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
  obtain ⟨w, hw⟩ := hierarchyCollection_sigma_succ_of_pi (θ := φ.toSemisentence ![#1, #0])
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

end FFL.FirstOrder.Arithmetic
