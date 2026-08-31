module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Σ_{s+1}-collection
-/

@[expose] public section

open Classical
open LO
open LO.FirstOrder

universe u
noncomputable section

namespace LO.FirstOrder.Arithmetic

private lemma funext_two {α : Type*} {n : ℕ} {f g : Fin (n + 2) → α}
    (h0 : f 0 = g 0) (h1 : f (Fin.succ 0) = g (Fin.succ 0))
    (hs : ∀ i : Fin n, f i.succ.succ = g i.succ.succ) : f = g := by
  funext i
  induction i using Fin.cases with
  | zero => exact h0
  | succ i =>
    induction i using Fin.cases with
    | zero => exact h1
    | succ i => exact hs i

variable {V : Type u} [ORingStructure V] {n s : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)]

-- `𝗜𝚺₁ ⪯ 𝗜𝚺 (s + 1) ⪯ 𝗣𝗔⁻` is only registered as an instance for the literal level `1`;
-- derive it here for the general level so downstream order/ring instances on `V` resolve.
private lemma models_paMinus {s : ℕ} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  have : 𝗜𝚺₁ ⪯ 𝗜𝚺 (s + 1) := ISigma_weakerThan_of_le (by omega)
  exact models_of_subtheory (U := 𝗜𝚺 (s + 1)) inferInstance

private noncomputable def collectionCore (θ : ArithmeticSemiformula Empty (n + 2))
    (e : Fin n → V) : ArithmeticSemiformula V 4 :=
  Rew.embSubsts (#0 :> #1 :> fun i => (&(e i) : ArithmeticSemiterm V 4)) ▹ θ

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] in
private lemma hierarchy_collectionCore {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ) (e : Fin n → V) : Hierarchy 𝚺 (s + 1) (collectionCore θ e) := by
  simp [collectionCore, hθ]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] in
private lemma eval_collectionCore {θ : ArithmeticSemiformula Empty (n + 2)} (e : Fin n → V)
    (u x w y : V) :
    (collectionCore θ e).Eval (u :> x :> w :> ![y]) id ↔ V ⊧/(u :> x :> e) θ := by
  simp only [collectionCore, Semiformula.eval_embSubsts, Function.comp_def]
  exact Iff.of_eq (congrArg (fun b => Semiformula.Evalb (M := V) b θ)
    (funext_two (by simp) (by simp) fun i => by simp))

private noncomputable def collectionMotive (θ : ArithmeticSemiformula Empty (n + 2))
    (e : Fin n → V) (a : V) : ArithmeticSemiformula V 1 :=
  let cond : ArithmeticSemiformula V 3 :=
    Semiformula.rel Language.LT.lt ![(#0 : ArithmeticSemiterm V 3), (&a : ArithmeticSemiterm V 3)]
  let inner : ArithmeticSemiformula V 3 := (collectionCore θ e).bexsLTSucc (#1 : ArithmeticSemiterm V 3)
  ∃¹ ((cond 🡒 inner).ballLT (#1 : ArithmeticSemiterm V 2))

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] in
private lemma hierarchy_collectionMotive {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ) (e : Fin n → V) (a : V) :
    Hierarchy 𝚺 (s + 1) (collectionMotive θ e a) := by
  have : Hierarchy 𝚺 (s + 1) (collectionCore θ e) := hierarchy_collectionCore hθ e
  simp [collectionMotive, this]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)] in
private lemma eval_collectionMotive [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {θ : ArithmeticSemiformula Empty (n + 2)}
    (e : Fin n → V) (a : V) (v : Fin 1 → V) :
    (collectionMotive θ e a).Eval v id ↔
      ∃ w, ∀ x < v 0, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have hv : v = ![v 0] := by
    funext i; induction i using Fin.cases with | zero => simp | succ i => exact i.elim0
  rw [hv]
  simp [collectionMotive, Semiformula.eval_ballLT, Semiformula.eval_bexsLTSucc,
    Arithmetic.lt_succ_iff_le, eval_collectionCore, Function.comp_def]

private lemma collectionMotive_definable {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ) (e : Fin n → V) (a : V) :
    𝚺-[s + 1].DefinablePred (fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ) := by
  have := models_paMinus (V := V) (s := s)
  exact HierarchySymbol.Definable.mkPolarity (collectionMotive θ e a) (hierarchy_collectionMotive hθ e a)
    (fun v => (eval_collectionMotive e a v).symm)

/-- Semantic Σ_{s+1}-collection over models of `𝗜𝚺 (s + 1)`. -/
theorem sigma_exists_bound_witness {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ)
    (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have := models_paMinus (V := V) (s := s)
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 (s + 1)
      (P := fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ)
      (hP := collectionMotive_definable hθ e a)
    . exact ⟨0, fun x hx _ => absurd hx (by simp)⟩
    . rintro y ⟨w, hw⟩
      by_cases hya : y < a
      . obtain ⟨u₀, hu₀⟩ := h y hya
        use max w u₀;
        intro x hx _
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        . obtain ⟨u, hu, hPu⟩ := hw x hx (lt_trans hx hya)
          exact ⟨u, le_trans hu (le_max_left w u₀), hPu⟩
        . exact ⟨u₀, le_max_right w u₀, hu₀⟩
      . use w;
        intro x hx hxa
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        . exact hw x hx hxa
        . exact absurd hxa hya
  obtain ⟨w, hw⟩ := key (a + 1)
  exact ⟨w, fun x hx => hw x (lt_trans hx (lt_add_one a)) hx⟩

end LO.FirstOrder.Arithmetic
