module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Δ₀-witnessed form for Σ₁ formulas
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

variable {V : Type u} [ORingStructure V] {n : ℕ}

private lemma eval_insert1 (θ : ArithmeticSemiformula Empty (n + 1)) (u w : V) (e : Fin n → V) :
    V ⊧/(u :> w :> e) (Rew.bShift.q ▹ θ) ↔ V ⊧/(u :> e) θ := by
  simp [Semiformula.eval_rew_q, Function.comp_def]

@[simp]
private lemma hierarchy_insert1 {Γ s} {θ : ArithmeticSemiformula Empty (n + 1)} :
    Hierarchy Γ s (Rew.bShift.q ▹ θ) ↔ Hierarchy Γ s θ := by
  simp

private lemma eval_insert2 (θ : ArithmeticSemiformula Empty (n + 2)) (u x w : V) (e : Fin n → V) :
    V ⊧/(u :> x :> w :> e) (Rew.bShift.q.q ▹ θ) ↔ V ⊧/(u :> x :> e) θ := by
  simp only [Semiformula.eval_rew_q, Function.comp_def]
  exact Iff.of_eq (congrArg (fun b => Semiformula.Eval (L := ℒₒᵣ) (M := V) b Empty.elim θ)
    (funext_two (by simp) (by simp) fun i => by simp))

@[simp]
private lemma hierarchy_insert2 {Γ s} {θ : ArithmeticSemiformula Empty (n + 2)} :
    Hierarchy Γ s (Rew.bShift.q.q ▹ θ) ↔ Hierarchy Γ s θ := by
  simp

private def Delta0Witnessed {n : ℕ} (φ : ArithmeticSemiformula Empty n)
    (θ : ArithmeticSemiformula Empty (n + 1)) : Prop :=
  ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
    V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ

private lemma witnessForm_atomic {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 0 φ) :
    ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧ Delta0Witnessed.{u} φ θ := by
  use Rew.bShift ▹ φ;
  and_intros
  . simpa using hφ
  . intro V _ _ e
    constructor
    . intro h; exact ⟨0, by simpa using h⟩
    . rintro ⟨w, h⟩; simpa using h

private lemma witnessForm_and {φ₁ φ₂ : ArithmeticSemiformula Empty n}
    {θ₁ θ₂ : ArithmeticSemiformula Empty (n + 1)} (hθ₁ : Hierarchy 𝚺 0 θ₁) (hθ₂ : Hierarchy 𝚺 0 θ₂)
    (h₁ : Delta0Witnessed.{u} φ₁ θ₁) (h₂ : Delta0Witnessed.{u} φ₂ θ₂) :
    ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧ Delta0Witnessed.{u} (φ₁ ⋏ φ₂) θ := by
  use (Rew.bShift.q ▹ θ₁).bexsLTSucc (#0 : ArithmeticSemiterm Empty (n + 1)) ⋏
    (Rew.bShift.q ▹ θ₂).bexsLTSucc (#0 : ArithmeticSemiterm Empty (n + 1));
  and_intros
  . simp [hθ₁, hθ₂]
  . intro V _ _ e
    simp only [LO.LogicalConnective.HomClass.map_and]
    rw [h₁ V e, h₂ V e]
    simp only [Semiformula.eval_bexsLTSucc, Arithmetic.lt_succ_iff_le, eval_insert1]
    constructor
    . rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩
      exact ⟨w₁ + w₂, ⟨w₁, self_le_add_right w₁ w₂, hw₁⟩, ⟨w₂, self_le_add_left w₂ w₁, hw₂⟩⟩
    . rintro ⟨w, ⟨w₁, _, hw₁⟩, ⟨w₂, _, hw₂⟩⟩
      exact ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩

private lemma witnessForm_or {φ₁ φ₂ : ArithmeticSemiformula Empty n}
    {θ₁ θ₂ : ArithmeticSemiformula Empty (n + 1)} (hθ₁ : Hierarchy 𝚺 0 θ₁) (hθ₂ : Hierarchy 𝚺 0 θ₂)
    (h₁ : Delta0Witnessed.{u} φ₁ θ₁) (h₂ : Delta0Witnessed.{u} φ₂ θ₂) :
    ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧ Delta0Witnessed.{u} (φ₁ ⋎ φ₂) θ := by
  use θ₁ ⋎ θ₂;
  and_intros
  . simp [hθ₁, hθ₂]
  . intro V _ _ e
    simp only [LO.LogicalConnective.HomClass.map_or]
    rw [h₁ V e, h₂ V e]
    aesop

section Collection

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private noncomputable def collectionCore (θ : ArithmeticSemiformula Empty (n + 2))
    (e : Fin n → V) : ArithmeticSemiformula V 4 :=
  Rew.embSubsts (#0 :> #1 :> fun i => (&(e i) : ArithmeticSemiterm V 4)) ▹ θ

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma hierarchy_collectionCore {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) : Hierarchy 𝚺 0 (collectionCore θ e) := by
  simp [collectionCore, hθ]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
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

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma hierarchy_collectionMotive {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) (a : V) :
    Hierarchy 𝚺 1 (collectionMotive θ e a) := by
  have : Hierarchy 𝚺 1 (collectionCore θ e) := (hierarchy_collectionCore hθ e).mono (by omega)
  simp [collectionMotive, this]

private lemma eval_collectionMotive {θ : ArithmeticSemiformula Empty (n + 2)}
    (e : Fin n → V) (a : V) (v : Fin 1 → V) :
    (collectionMotive θ e a).Eval v id ↔
      ∃ w, ∀ x < v 0, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have hv : v = ![v 0] := by
    funext i; induction i using Fin.cases with | zero => simp | succ i => exact i.elim0
  rw [hv]
  simp [collectionMotive, Semiformula.eval_ballLT, Semiformula.eval_bexsLTSucc,
    Arithmetic.lt_succ_iff_le, eval_collectionCore, Function.comp_def]

private lemma collectionMotive_definable {θ : ArithmeticSemiformula Empty (n + 2)}
    (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) (a : V) :
    𝚺-[1].DefinablePred (fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ) :=
  HierarchySymbol.Definable.mkPolarity (collectionMotive θ e a) (hierarchy_collectionMotive hθ e a)
    (fun v => (eval_collectionMotive e a v).symm)

private lemma exists_bound_witness {θ : ArithmeticSemiformula Empty (n + 2)} (hθ : Hierarchy 𝚺 0 θ)
    (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 1
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

end Collection

private lemma witnessForm_exs {φ : ArithmeticSemiformula Empty (n + 1)}
    {θ' : ArithmeticSemiformula Empty (n + 2)} (hθ' : Hierarchy 𝚺 0 θ')
    (h : Delta0Witnessed.{u} φ θ') :
    ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧ Delta0Witnessed.{u} (∃¹ φ) θ := by
  use ((Rew.bShift.q.q ▹ θ').bexsLTSucc (#1 : ArithmeticSemiterm Empty (n + 2))).bexsLTSucc
    (#0 : ArithmeticSemiterm Empty (n + 1));
  and_intros
  . simp [hθ']
  . intro V _ _ e
    simp only [Semiformula.eval_ex, eval_bexsLTSucc', eval_insert2]
    constructor
    . rintro ⟨x, hx⟩
      obtain ⟨w', hw'⟩ := (h V (x :> e)).mp hx
      exact ⟨x + w', x, self_le_add_right x w', w', self_le_add_left w' x, hw'⟩
    . rintro ⟨_, x, -, w', -, hw'⟩
      exact ⟨x, (h V (x :> e)).mpr ⟨w', hw'⟩⟩

private lemma witnessForm_ball {t : ArithmeticSemiterm Empty n} {φ : ArithmeticSemiformula Empty (n + 1)}
    {θ' : ArithmeticSemiformula Empty (n + 2)} (hθ' : Hierarchy 𝚺 0 θ')
    (h : Delta0Witnessed.{u} φ θ') :
    ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧ Delta0Witnessed.{u} (φ.ballLT t) θ := by
  use ((Rew.bShift.q.q ▹ θ').bexsLTSucc (#1 : ArithmeticSemiterm Empty (n + 2))).ballLT
    (Rew.bShift t : ArithmeticSemiterm Empty (n + 1));
  and_intros
  . simp [hθ']
  . intro V _ _ e
    simp only [Semiformula.eval_ballLT, eval_bexsLTSucc', eval_insert2, Semiterm.val_bShift]
    constructor
    . intro hφ
      have hex : ∀ x < t.valb e, ∃ w', V ⊧/(w' :> x :> e) θ' :=
        fun x hx => (h V (x :> e)).mp (hφ x hx)
      obtain ⟨w, hw⟩ := exists_bound_witness hθ' e (t.valb e) hex
      exact ⟨w, fun x hx => hw x hx⟩
    . rintro ⟨w, hw⟩ x hx
      obtain ⟨w', -, hθ'x⟩ := hw x hx
      exact (h V (x :> e)).mpr ⟨w', hθ'x⟩

lemma exists_delta0_witness_form {n : ℕ} {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 1 φ) :
  ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ := by
  apply sigma₁_induction' hφ
    (P := fun n φ => ∃ θ : ArithmeticSemiformula Empty (n + 1), Hierarchy 𝚺 0 θ ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
        V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ)
  . exact fun n => witnessForm_atomic (Hierarchy.verum _ _ _)
  . exact fun n => witnessForm_atomic (Hierarchy.falsum _ _ _)
  . exact fun n t₁ t₂ => witnessForm_atomic (Hierarchy.rel _ _ _ _)
  . exact fun n t₁ t₂ => witnessForm_atomic (Hierarchy.nrel _ _ _ _)
  . exact fun n t₁ t₂ => witnessForm_atomic (Hierarchy.rel _ _ _ _)
  . exact fun n t₁ t₂ => witnessForm_atomic (Hierarchy.nrel _ _ _ _)
  . rintro n φ ψ hφ hψ ⟨θ₁, hθ₁, h₁⟩ ⟨θ₂, hθ₂, h₂⟩
    exact witnessForm_and hθ₁ hθ₂ h₁ h₂
  . rintro n φ ψ hφ hψ ⟨θ₁, hθ₁, h₁⟩ ⟨θ₂, hθ₂, h₂⟩
    exact witnessForm_or hθ₁ hθ₂ h₁ h₂
  . rintro n t φ hφ ⟨θ', hθ', h⟩
    exact witnessForm_ball hθ' h
  . rintro n φ hφ ⟨θ', hθ', h⟩
    exact witnessForm_exs hθ' h

lemma models_iff_of_provable_iff {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T] {n} {φ ψ : ArithmeticSemiformula Empty n}
    (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type w) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  sorry

theorem exists_delta0_witness_provable {n : ℕ} {φ : ArithmeticSemiformula Empty n} (hφ : Hierarchy 𝚺 1 φ) :
    ∃ θ : ArithmeticSemiformula Empty (n + 1),
      Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ ∀¹* (φ 🡘 ∃¹ θ) := by
  sorry

theorem exists_delta0_witness_provable_of_sentence {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ∃ θ : ArithmeticSemisentence 1, Hierarchy 𝚺 0 θ ∧ 𝗜𝚺₁ ⊢ σ 🡘 ∃¹ θ := by
  sorry

end LO.FirstOrder.Arithmetic
