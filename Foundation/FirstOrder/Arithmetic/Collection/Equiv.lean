module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Equivalences between the collection schemata

Collection for the broad hierarchy, the collapse `𝗕⁺ Γ s ≊ 𝗕 Γ s`, the equivalence
`𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s`, and `𝗜𝚺 s` from `𝗕𝚺 (s + 1)`.

## References

- [HP98]
- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {s : ℕ}

private lemma models_collectionAxiom_of_exists_bound [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {φ : ArithmeticSemiformula ℕ 2}
    (H : ∀ (e : Fin φ.fvSup → V) (a : V),
      (∀ x < a, ∃ u, V ⊧/(u :> x :> e) (φ.toSemisentence ![#1, #0])) →
        ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) (φ.toSemisentence ![#1, #0])) :
    V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ) : ArithmeticSentence) := by
  suffices ∀ f : ℕ → V, ∀ a : V,
      (∀ x < a, ∃ y, φ.Eval ![x, y] f) → ∃ b, ∀ x < a, ∃ y < b, φ.Eval ![x, y] f by
    simpa [models_iff, Semiformula.eval_univCl, collectionAxiom, Semiformula.eval_ballLT,
      Semiformula.eval_bexsLT, Semiformula.eval_substs] using this;
  intro f a h;
  obtain ⟨w, hw⟩ := H (fun i : Fin φ.fvSup ↦ f i) a
    fun x hx ↦ (h x hx).imp fun y hy ↦ (φ.eval_toSemisentence₂ x y f).mpr hy;
  exact ⟨w + 1, fun x hx ↦ (hw x hx).imp fun u hu ↦
    ⟨lt_succ_iff_le.mpr hu.1, (φ.eval_toSemisentence₂ x u f).mp hu.2⟩⟩;

private lemma exists_bound_of_definable {Γ : Polarity}
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy Γ s ψ → V↓[ℒₒᵣ] ⊧ .univCl (collectionAxiom ψ))
    {R : V → V → Prop} (hR : Γ-[s].DefinableRel R) (a : V) (h : ∀ x < a, ∃ y, R x y) :
    ∃ b, ∀ x < a, ∃ y < b, R x y := by
  have : V↓[ℒₒᵣ] ⊧* CollectionScheme (Hierarchy Γ s) :=
    Semantics.ModelsSet.setOf_iff.mpr (by rintro _ ⟨ψ, hψ, rfl⟩; exact hcol ψ hψ);
  obtain ⟨e, ψ, hψ, hiff⟩ := exists_hierarchy_eval_iff hR;
  exact CollectionScheme.collection (C := Hierarchy Γ s)
    ⟨e, ψ, hψ, fun x y ↦ by simpa using hiff ![x, y]⟩ a h;

section BroadHierarchy

/-! ### Collection for the broad hierarchy -/

variable {Γ : Polarity}

/-- In a model of `𝗕 Γ s`, witnesses for a `Hierarchy Γ s` formula `θ` at every `x < a` can be
chosen below a single bound `w`. -/
lemma exists_bound_of_models_CollectionOnHierarchy_of_hierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {m : ℕ}
    {θ : ArithmeticSemisentence (m + 2)} (hθ : Hierarchy Γ s θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := Γ) (s := s);
  obtain ⟨θ', hθ'⟩ := Prenex.models_exists_prenex (Γ' := Γ) hθ;
  obtain ⟨w, hw⟩ := CollectionOnHierarchy.collection Γ s
    (.of_strictHierarchy (θ := θ'.val) Prenex.val_strictHierarchy e) a
    fun x hx ↦ (hex x hx).imp fun u hu ↦ (hθ' V (u :> x :> e)).mp hu;
  exact ⟨w, fun x hx ↦ (hw x hx).imp fun u hu ↦
    ⟨le_of_lt hu.1, (hθ' V (u :> x :> e)).mpr hu.2⟩⟩;

/-- A model of `𝗕 Γ s` satisfies the collection axiom for every `Hierarchy Γ s` formula. -/
lemma models_collectionAxiom_of_hierarchy [V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] {φ : ArithmeticSemiformula ℕ 2}
    (hφ : Hierarchy Γ s φ) : V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ) : ArithmeticSentence) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := Γ) (s := s);
  models_collectionAxiom_of_exists_bound fun e a ↦
    exists_bound_of_models_CollectionOnHierarchy_of_hierarchy (hφ.rew _) e a

/-- The broad and the strict collection schemata collapse: `𝗕⁺ Γ s` and `𝗕 Γ s` prove the same
sentences.

- [Bus98, pp. 84-85]
-/
theorem CollectionOnBroadHierarchy_equiv_CollectionOnHierarchy {Γ : Polarity} {s : ℕ} :
    𝗕⁺ Γ s ≊ 𝗕 Γ s := by
  apply Equiv.antisymm_iff.mpr;
  and_intros;
  . apply weakerThan_of_models.{0};
    intro M _ _;
    apply Semantics.ModelsSet.union_iff.mpr;
    and_intros;
    . exact models_of_ss (U := 𝗕 Γ s) inferInstance Set.subset_union_left;
    . apply Semantics.ModelsSet.setOf_iff.mpr;
      rintro _ ⟨φ, hφ, rfl⟩;
      exact models_collectionAxiom_of_hierarchy hφ;
  . exact CollectionOnHierarchy_weakerThan_CollectionOnBroadHierarchy Γ s;

end BroadHierarchy

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

private lemma MonotoneWitness.and [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {χ₁ χ₂ : ArithmeticSemisentence (m + 1)}
    {θ₁ θ₂ : ArithmeticSemisentence m} (h₁ : MonotoneWitness V χ₁ θ₁)
    (h₂ : MonotoneWitness V χ₂ θ₂) : MonotoneWitness V (χ₁ ⋏ χ₂) (θ₁ ⋏ θ₂) where
  monotone e v v' hv h := ⟨h₁.monotone e v v' hv h.1, h₂.monotone e v v' hv h.2⟩
  sound e v h := ⟨h₁.sound e v h.1, h₂.sound e v h.2⟩
  complete e h := by
    obtain ⟨v₁, hv₁⟩ := h₁.complete e h.1;
    obtain ⟨v₂, hv₂⟩ := h₂.complete e h.2;
    exact ⟨max v₁ v₂, h₁.monotone e v₁ _ (le_max_left _ _) hv₁,
      h₂.monotone e v₂ _ (le_max_right _ _) hv₂⟩;

private lemma MonotoneWitness.or {χ₁ χ₂ : ArithmeticSemisentence (m + 1)}
    {θ₁ θ₂ : ArithmeticSemisentence m} (h₁ : MonotoneWitness V χ₁ θ₁)
    (h₂ : MonotoneWitness V χ₂ θ₂) : MonotoneWitness V (χ₁ ⋎ χ₂) (θ₁ ⋎ θ₂) where
  monotone e v v' hv h := h.imp (h₁.monotone e v v' hv) (h₂.monotone e v v' hv)
  sound e v h := h.imp (h₁.sound e v) (h₂.sound e v)
  complete e h := by
    rcases h with h | h;
    . exact (h₁.complete e h).imp fun v hv ↦ by tauto;
    . exact (h₂.complete e h).imp fun v hv ↦ by tauto;

private lemma eval_bexsLT_swap01 (χ : ArithmeticSemisentence (m + 2)) (e : Fin m → V) (v : V) :
    V ⊧/(v :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) ↔ ∃ x < v, V ⊧/(v :> x :> e) χ := by
  simp only [Semiformula.eval_bexsLT];
  exact exists_congr fun x ↦ and_congr (by simp) (Semiformula.eval_swap01 χ x v e);

private lemma MonotoneWitness.exists_eval_bexsLT_swap01 [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    {χ : ArithmeticSemisentence (m + 2)} {θ : ArithmeticSemisentence (m + 1)}
    (hM : MonotoneWitness V χ θ) (e : Fin m → V) {x v : V} (h : V ⊧/(v :> x :> e) χ) :
    ∃ w, V ⊧/(w :> e) ((χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) :=
  ⟨max (x + 1) v, (eval_bexsLT_swap01 χ e _).mpr
    ⟨x, lt_of_lt_of_le (lt_add_one x) (le_max_left _ _),
      hM.monotone (x :> e) v _ (le_max_right _ _) h⟩⟩

private lemma exists_monotoneWitness_of_pi {θ} (h : Hierarchy 𝚷 s θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ ∧ MonotoneWitness V χ θ :=
  ⟨Rew.bShift ▹ θ, h.rew _, monotoneWitness_bShift θ⟩

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

section

variable [V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s]

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
      obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy_of_hierarchy (Γ := 𝚷) (s := s) hχ e
        (u.valb e) fun x hx ↦ hcomplete (x :> e) (h x hx);
      exact ⟨w, (heval e w).mpr fun x hx ↦ (hw x hx).elim fun v hv ↦
        hmono (x :> e) v w hv.1 hv.2⟩;

private lemma exists_monotoneWitness_exs {θ χ} (hχ : Hierarchy 𝚷 s χ) (hM : MonotoneWitness V χ θ) :
    ∃ χ' : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ' ∧ MonotoneWitness V χ' (∃¹ θ) := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  use (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0;
  and_intros;
  . simpa using hχ;
  . constructor;
    . intro e v v' hv h;
      obtain ⟨x, hx, h⟩ := (eval_bexsLT_swap01 χ e v).mp h;
      exact (eval_bexsLT_swap01 χ e v').mpr
        ⟨x, lt_of_lt_of_le hx hv, hM.monotone (x :> e) v v' hv h⟩;
    . intro e v h;
      obtain ⟨x, -, h⟩ := (eval_bexsLT_swap01 χ e v).mp h;
      exact Semiformula.eval_ex.mpr ⟨x, hM.sound (x :> e) v h⟩;
    . intro e h;
      obtain ⟨x, hx⟩ := Semiformula.eval_ex.mp h;
      obtain ⟨v, hv⟩ := hM.complete (x :> e) hx;
      exact hM.exists_eval_bexsLT_swap01 e hv;

private lemma exists_monotoneWitness_of_complexity_le {θ : ArithmeticSemisentence m} (c : ℕ)
    (hc : θ.complexity ≤ c) (hθ : Hierarchy 𝚺 (s + 1) θ) :
    ∃ χ : ArithmeticSemisentence (m + 1), Hierarchy 𝚷 s χ ∧ MonotoneWitness V χ θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  induction c generalizing m θ hθ with
  | zero =>
    cases hθ with
    | verum | falsum | rel | nrel => exact exists_monotoneWitness_of_pi (by simp);
    | _ => simp [Semiformula.ball_eq, Semiformula.bexs_eq, Semiformula.imp_eq] at hc;
  | succ c ih =>
    cases hθ with
    | verum | falsum | rel | nrel => exact exists_monotoneWitness_of_pi (by simp);
    | and hφ hψ =>
      obtain ⟨χ₁, hχ₁, hM₁⟩ := ih (by simp at hc; omega) hφ;
      obtain ⟨χ₂, hχ₂, hM₂⟩ := ih (by simp at hc; omega) hψ;
      exact ⟨χ₁ ⋏ χ₂, by simp [hχ₁, hχ₂], hM₁.and hM₂⟩;
    | or hφ hψ =>
      obtain ⟨χ₁, hχ₁, hM₁⟩ := ih (by simp at hc; omega) hφ;
      obtain ⟨χ₂, hχ₂, hM₂⟩ := ih (by simp at hc; omega) hψ;
      exact ⟨χ₁ ⋎ χ₂, by simp [hχ₁, hχ₂], hM₁.or hM₂⟩;
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
    ∃ χ : ArithmeticSemiformula ℕ 2,
      Hierarchy 𝚷 s χ ∧ ∀ x : V, φ.Eval ![x] f ↔ ∃ w, χ.Eval ![x, w] f := by
  obtain ⟨χ, hχ, -, hsound, hcomplete⟩ := exists_monotoneWitness_of_hierarchy (V := V)
    (θ := (φ.toSemisentence ![#0] : ArithmeticSemisentence (φ.fvSup + 1))) (hφ.rew _);
  use Rew.embSubsts (#1 :> #0 :> fun i : Fin φ.fvSup ↦ (&(i : ℕ) : ArithmeticSemiterm ℕ 2)) ▹ χ;
  and_intros;
  . exact hχ.rew _;
  . intro x;
    rw [← φ.eval_toSemisentence₁ x f];
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
      | succ i => cases i using Fin.cases <;> simp;
    exact ⟨fun h ↦ (hcomplete _ h).imp fun w hw ↦ (hval w).mpr hw,
      fun ⟨w, hw⟩ ↦ hsound _ w ((hval w).mp hw)⟩;

private lemma exists_bound_sigma_succ_of_models_BPi {θ : ArithmeticSemisentence (m + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ) (e : Fin m → V) (a : V)
    (hex : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  obtain ⟨χ, hχ, hM⟩ := exists_monotoneWitness_of_hierarchy (V := V) hθ;
  obtain ⟨w, hw⟩ := exists_bound_of_models_CollectionOnHierarchy_of_hierarchy (Γ := 𝚷) (s := s)
    (θ := (χ ⇜ (#1 :> #0 :> (#·.succ.succ))).bexsLT #0) (by simpa using hχ) e a <| by
      intro x hx;
      obtain ⟨u, hu⟩ := hex x hx;
      obtain ⟨v, hv⟩ := hM.complete (u :> x :> e) hu;
      exact hM.exists_eval_bexsLT_swap01 (x :> e) hv;
  use w;
  intro x hx;
  obtain ⟨v, hvw, hv⟩ := hw x hx;
  obtain ⟨u, huv, hu⟩ := (eval_bexsLT_swap01 χ (x :> e) v).mp hv;
  exact ⟨u, le_of_lt (lt_of_lt_of_le huv hvw), hM.sound (u :> x :> e) v hu⟩;

lemma models_collectionAxiom_of_models_BPi (hφ : Hierarchy 𝚺 (s + 1) φ) :
    V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom φ)) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_paMinus_of_models_CollectionOnHierarchy (Γ := 𝚷) (s := s);
  models_collectionAxiom_of_exists_bound fun e a ↦
    exists_bound_sigma_succ_of_models_BPi (hφ.rew _) e a

end

theorem BPi.provable_collectionAxiom_of_hierarchy (hφ : Hierarchy 𝚺 (s + 1) φ) :
    𝗕𝚷 s ⊢ .univCl (collectionAxiom φ) := by
  apply complete.{0};
  intro M _ _;
  exact models_collectionAxiom_of_models_BPi hφ;

@[instance]
theorem BSigma_succ_weakerThan_BPi : 𝗕𝚺 (s + 1) ⪯ 𝗕𝚷 s := WeakerThan.ofAxm! <| by
  rintro σ (hσ | ⟨φ, hφ, rfl⟩);
  . exact WeakerThan.pbl (h := (inferInstance : 𝗜𝚺₀ ⪯ 𝗕𝚷 s)) (by_axm hσ);
  . exact BPi.provable_collectionAxiom_of_hierarchy hφ.hierarchy;

@[instance]
theorem BSigma_succ_equiv_BPi : 𝗕𝚺 (s + 1) ≊ 𝗕𝚷 s :=
  Equiv.antisymm_iff.mpr ⟨BSigma_succ_weakerThan_BPi, CollectionOnHierarchy_weakerThan_BSigma_succ 𝚷 s⟩

end BSigma_succ_BPi

section ISigma_BSigma_succ

/-! ### `𝗜𝚺 s` from `𝗕𝚺 (s + 1)` -/

section models

private lemma definable_step {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) :
    𝚷-[s + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
  have hex : 𝚺-[s + 1].DefinablePred fun x ↦ ∃ z, Q x z :=
    HierarchySymbol.Definable.exs <|
      .of_iff ((hQ.of_lt (s := s + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
  apply HierarchySymbol.Definable.or;
  . exact .of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
  . exact .of_iff (HierarchySymbol.Definable.retractiont 2
      (hQ.of_lt (s := s + 1) (Γ := 𝚷) (by simp)) ![‘#0 + 1’, #1]) (by intro v; simp);

private lemma definable_bounded {Q : V → V → Prop} (hQ : 𝚷-[s].DefinableRel Q) (a u : V) :
    𝚷-[s].DefinablePred fun x ↦ ∃ y < u, Q x y ∨ a < x := by
  have hlt : 𝚷-[s].Definable fun w : Fin 2 → V ↦ a < w 1 :=
    .of_iff (HierarchySymbol.Definable.retractiont 2
      (inferInstance : 𝚷-[s].DefinableRel (LT.lt : V → V → Prop)) ![&a, #1]) (by intro w; simp);
  have h : 𝚷-[s].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&u : ArithmeticSemiterm V 1).val v id, Q (v 0) y ∨ a < v 0 := by
    apply HierarchySymbol.Definable.bexs;
    exact .of_iff ((hQ.retraction ![1, 0]).or hlt) (by intro w; simp);
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
    . exact ((hPQ (x + 1)).mp (succ x ((hPQ x).mpr hx))).imp fun w hw ↦ .inr hw;
    . exact ⟨0, .inl hx⟩;
  obtain ⟨w₀, hw₀⟩ := (hPQ 0).mp zero;
  have hw₀' : w₀ < max v (w₀ + 1) := lt_of_lt_of_le (lt_add_one w₀) (le_max_right v (w₀ + 1));
  have hpos : (0 : V) < max v (w₀ + 1) := lt_of_le_of_lt (by simp) hw₀';
  have key : ∀ x, ∃ y < max v (w₀ + 1), Q x y ∨ a < x := by
    apply InductionOnHierarchy.succ_induction 𝚷 s (definable_bounded hQ a _) ⟨w₀, hw₀', .inl hw₀⟩;
    rintro x ⟨y, -, hy | hy⟩;
    . by_cases hxa : x < a;
      . obtain ⟨z, hzv, hz | hz⟩ := hv x hxa;
        . exact absurd ⟨y, hy⟩ hz;
        . exact ⟨z, lt_of_lt_of_le hzv (le_max_left v (w₀ + 1)), .inl hz⟩;
      . exact ⟨0, hpos, .inr (lt_of_le_of_lt (not_lt.mp hxa) (lt_add_one x))⟩;
    . exact ⟨0, hpos, .inr (lt_trans hy (lt_add_one x))⟩;
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
    models_collectionAxiom_of_hierarchy (Γ := 𝚺) (s := s + 2) (hψ.accum 𝚺);
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
      models_of_ss inferInstance <| CollectionOnHierarchy_subset_mono <| Nat.le_succ (s + 1);
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s := ih;
    exact models_ISigma_succ;

@[instance]
theorem ISigma_weakerThan_BSigma_succ : 𝗜𝚺 s ⪯ 𝗕𝚺 (s + 1) :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma_of_models_BSigma_succ

end theorems

end ISigma_BSigma_succ

end FFL.FirstOrder.Arithmetic
