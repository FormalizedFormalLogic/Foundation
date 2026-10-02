module

public import Foundation.FirstOrder.Arithmetic.Collection.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.Hierarchy

/-!
# Prenex normal form for the arithmetical hierarchy

For `𝗕𝚺 s ⪯ T`, every `ℬ[<, ℒₒᵣ].Hierarchy Γ s` formula `φ` is `T`-provably
equivalent to `φ₀.toPrenex Γ s` for some `φ₀ : ℬ[<, ℒₒᵣ].Semisentence (n + s)`.

## References

- [HP98]
-/

@[expose] public section

open FFL

namespace FFL.FirstOrder

namespace Arithmetic

private abbrev PrenexBase : ℕ → ArithmeticTheory
  | 0     => 𝗜𝚺₀
  | s + 1 => 𝗕𝚷 s

private lemma models_PrenexBase_of_models_CollectionOnPrenexHierarchy {V : Type*} [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [h : V↓[ℒₒᵣ] ⊧* 𝗕 Γ s] : V↓[ℒₒᵣ] ⊧* PrenexBase s :=
  match s, h with
  | 0, h => models_of_ss h Set.subset_union_left
  | s + 1, h => models_CollectionOnPrenexHierarchy_of_lt (h := h) (Nat.lt_succ_self s)

end Arithmetic

namespace Bounding.Prenex

open Arithmetic

variable {Γ : Polarity} {s : ℕ} {ξ : Type*} {n : ℕ}
variable {V : Type*} [ORingStructure V] {f : ξ → V}

mutual

def ball : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1) → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, u, φ => ⟨⟨_, .ball rfl (Rew.bShift_positive u) φ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, u, φ =>
      (ball (Rew.bShift u)
        (bexs ‘#1 + 1’ (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(bexs u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def bexs : {Γ : Polarity} → {s n : ℕ} →
    ArithmeticSemiterm ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1) → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, u, φ => ⟨⟨_, .bexs rfl (Rew.bShift_positive u) φ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, u, φ =>
      (bexs (Rew.bShift u) (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma
  | 𝚷, _ + 1, _, u, φ => ∼(ball u (∼φ))
termination_by Γ s n _u _φ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

local notation:64 "∀'[" u "] " φ => Prenex.ball u φ
local notation:64 "∃'[" u "] " φ => Prenex.bexs u φ

@[simp]
lemma ball_zero {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex Γ 0 ξ (n + 1)} :
  (∀'[u] φ) = ⟨⟨_, .ball rfl (Rew.bShift_positive u) φ.matrix.bounded⟩⟩ := by
  simp [ball]

lemma ball_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) =
    (∀'[Rew.bShift u]
      (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma := by
  rw [ball]

lemma ball_succ_pi {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∀'[u] φ) = ∼(∃'[u] ∼φ) := by
  rw [ball]


@[simp]
lemma bexs_zero {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex Γ 0 ξ (n + 1)} :
  (∃'[u] φ) = ⟨⟨_, .bexs rfl (Rew.bShift_positive u) φ.matrix.bounded⟩⟩ := by
  simp [bexs]

lemma bexs_succ_sigma {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) =
    (∃'[Rew.bShift u] (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ))))).sigma := by
  rw [bexs]

lemma bexs_succ_pi {u : ArithmeticSemiterm ξ n} {φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)} :
  (∃'[u] φ) = ∼(∀'[u] ∼φ) := by
  rw [bexs]


mutual

def and : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => ⟨⟨_, .and φ.matrix.bounded ψ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, φ, ψ =>
      (and (∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))
           (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(or (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

def or : {Γ : Polarity} → {s n : ℕ} →
    ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n → ℬ[<, ℒₒᵣ].Prenex Γ s ξ n
  | _, 0, _, φ, ψ => ⟨⟨_, .or φ.matrix.bounded ψ.matrix.bounded⟩⟩
  | 𝚺, _ + 1, _, φ, ψ => (or φ.sigmaInv ψ.sigmaInv).sigma
  | 𝚷, _ + 1, _, φ, ψ => ∼(and (∼φ) (∼ψ))
termination_by Γ s n φ ψ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

instance : HWedge (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n)
    (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) := ⟨and⟩
instance : HVee (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n)
    (ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) := ⟨or⟩

@[simp]
lemma and_zero {φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ 0 ξ n} :
    (φ ⋏ ψ) = ⟨⟨_, .and φ.matrix.bounded ψ.matrix.bounded⟩⟩ := by
  change and φ ψ = _
  simp [and]

lemma and_succ_sigma {φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n} :
  (φ ⋏ ψ) = ((∃'[‘#0 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))) ⋏
    (∃'[‘#0 + 1’] (ψ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ)))))).sigma := by
  change and φ ψ = _
  rw [and]; rfl

lemma and_succ_pi {φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ n} : (φ ⋏ ψ) = ∼(∼φ ⋎ ∼ψ) := by
  change and φ ψ = _
  rw [and]; rfl


@[simp]
lemma or_zero {φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ 0 ξ n} :
    (φ ⋎ ψ) = ⟨⟨_, .or φ.matrix.bounded ψ.matrix.bounded⟩⟩ := by
  change or φ ψ = _
  simp [or]

lemma or_succ_sigma {φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n} :
    (φ ⋎ ψ) = (φ.sigmaInv ⋎ ψ.sigmaInv).sigma := by
  change or φ ψ = _
  rw [or]; rfl

lemma or_succ_pi {φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ n} : (φ ⋎ ψ) = ∼(∼φ ⋏ ∼ψ) := by
  change or φ ψ = _
  rw [or]; rfl

private lemma models_bexs_witness [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (hb : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ (m + 1))
      (e : Fin m → V),
      Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val)
    (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) (x w : V) (e : Fin n → V) :
    Semiformula.Eval (x :> w :> e) f
        (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val
      ↔ ∃ y ≤ w, Semiformula.Eval (y :> x :> e) f φ.sigmaInv.val := by
  simp [hb, Semiformula.eval_insert2, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];

mutual

private theorem models_ball :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (u : ArithmeticSemiterm ξ n) →
      (φ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1)) → (e : Fin n → V) →
    Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val
  | _, 0, _, _, u, φ, e => by
    simp [ball_zero, Prenex.val, Semiformula.eval_ball];
  | 𝚺, s + 1, _, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    have iha : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_ball u φ e;
    have ihb : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    rw [ball_succ_sigma (u := u) (φ := φ), models_sigma];
    simp only [iha (Rew.bShift u), Semiterm.val_bShift, models_bexs_witness ihb φ,
      models_sigmaInv φ];
    constructor;
    · rintro ⟨w, hw⟩ x hx;
      obtain ⟨y, -, hy⟩ := hw x hx;
      exact ⟨y, hy⟩;
    · intro h;
      exact (CollectionOnPrenexHierarchy.collection 𝚷 s
        (.of_prenexHierarchy φ.sigmaInv.val_prenexHierarchy e f) (u.val e f) h).imp
        fun b hb x hx ↦ (hb x hx).imp fun y hy ↦ ⟨le_of_lt hy.1, hy.2⟩;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    have hthis : Semiformula.Eval e f (∃'[u] ∼φ).val ↔
        ∃ x < u.val e f, Semiformula.Eval (x :> e) f (∼φ).val := ih u (∼φ) e;
    have hval : (∀'[u] φ).val = ∼(∃'[u] ∼φ).val := by
      rw [ball_succ_pi (u := u) (φ := φ)];
      exact val_neg (∃'[u] ∼φ);
    rw [hval];
    grind [val_neg, LogicalConnective.Prop.neg_eq];
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

private theorem models_bexs :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (u : ArithmeticSemiterm ξ n) →
      (φ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ (n + 1)) → (e : Fin n → V) →
    Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val
  | _, 0, _, _, u, φ, e => by
    simp [bexs_zero, Prenex.val, Semiformula.eval_bexs];
  | 𝚺, s + 1, n, _, u, φ, e => by
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∃'[u] φ).val ↔ ∃ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_bexs u φ e;
    have hswap : ∀ x b : V,
        Semiformula.Eval (x :> b :> e) f
            (φ.sigmaInv.rew (Rew.subst (#1 :> #0 :> (#·.succ.succ)))).val ↔
          Semiformula.Eval (b :> x :> e) f φ.sigmaInv.val := by
      intro x b;
      rw [val_rew, Semiformula.eval_substs];
      congr!;
      exact Fin.funext_two (by simp) (by simp) fun i ↦ by simp;
    rw [bexs_succ_sigma (u := u) (φ := φ), models_sigma];
    simp only [ih, Semiterm.val_bShift, hswap, models_sigmaInv φ];
    grind;
  | 𝚷, s + 1, _, _, u, φ, e => by
    have ih : ∀ {m : ℕ} (u : ArithmeticSemiterm ξ m) (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (m + 1))
        (e : Fin m → V),
        Semiformula.Eval e f (∀'[u] φ).val ↔ ∀ x < u.val e f, Semiformula.Eval (x :> e) f φ.val :=
      fun u φ e => models_ball u φ e;
    have hthis : Semiformula.Eval e f (∀'[u] ∼φ).val ↔
        ∀ x < u.val e f, Semiformula.Eval (x :> e) f (∼φ).val := ih u (∼φ) e;
    have hval : (∃'[u] φ).val = ∼(∀'[u] ∼φ).val := by
      rw [bexs_succ_pi (u := u) (φ := φ)];
      exact val_neg (∀'[u] ∼φ);
    rw [hval];
    grind [val_neg, LogicalConnective.Prop.neg_eq];
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

mutual

private theorem models_and :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) → (e : Fin n → V) →
    Semiformula.Eval e f (φ ⋏ ψ).val ↔ Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [and_zero, Prenex.val];
  | 𝚺, s + 1, n, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    have iha : ∀ {m : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋏ ψ).val ↔
          Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    rw [and_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    have hbexs : ∀ (χ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n) (z : V),
        Semiformula.Eval (z :> e) f
            (∃'[‘#0 + 1’] (χ.sigmaInv.rew (Rew.subst (#0 :> (#·.succ.succ))))).val ↔
          ∃ x ≤ z, Semiformula.Eval (x :> e) f χ.sigmaInv.val := by
      intro χ z;
      rw [models_bexs];
      simp [Semiformula.eval_insert1, Arithmetic.lt_succ_iff_le, -Semiformula.eval_substs];
    simp only [iha, models_sigmaInv φ, models_sigmaInv ψ, hbexs];
    constructor;
    · rintro ⟨z, ⟨x, -, hx⟩, ⟨y, -, hy⟩⟩;
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩;
      exact ⟨max x y, ⟨x, le_max_left x y, hx⟩, ⟨y, le_max_right x y, hy⟩⟩;
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋎ ψ).val ↔
          Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    have hthis : Semiformula.Eval e f (∼φ ⋎ ∼ψ).val ↔
        Semiformula.Eval e f (∼φ).val ∨ Semiformula.Eval e f (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋏ ψ).val = ∼(∼φ ⋎ ∼ψ).val := by
      rw [and_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋎ ∼ψ);
    rw [hval];
    grind [val_neg, LogicalConnective.Prop.neg_eq];
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

private theorem models_or :
    {Γ : Polarity} → {s n : ℕ} → [V↓[ℒₒᵣ] ⊧* PrenexBase s] →
      (φ ψ : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n) → (e : Fin n → V) →
    Semiformula.Eval e f (φ ⋎ ψ).val ↔ Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val
  | _, 0, _, _, φ, ψ, e => by
    simp [or_zero, Prenex.val];
  | 𝚺, s + 1, _, _, φ, ψ, e => by
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    have ih : ∀ {m : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚷 s ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋎ ψ).val ↔
          Semiformula.Eval e f φ.val ∨ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_or φ ψ e;
    rw [or_succ_sigma (φ := φ) (ψ := ψ), models_sigma];
    simp only [ih, models_sigmaInv φ, models_sigmaInv ψ, exists_or];
  | 𝚷, s + 1, _, _, φ, ψ, e => by
    have ih : ∀ {m : ℕ} (φ ψ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ m) (e : Fin m → V),
        Semiformula.Eval e f (φ ⋏ ψ).val ↔
          Semiformula.Eval e f φ.val ∧ Semiformula.Eval e f ψ.val :=
      fun φ ψ e => models_and φ ψ e;
    have hthis : Semiformula.Eval e f (∼φ ⋏ ∼ψ).val ↔
        Semiformula.Eval e f (∼φ).val ∧ Semiformula.Eval e f (∼ψ).val := ih (∼φ) (∼ψ) e;
    have hval : (φ ⋎ ψ).val = ∼(∼φ ⋏ ∼ψ).val := by
      rw [or_succ_pi (φ := φ) (ψ := ψ)];
      exact val_neg (∼φ ⋏ ∼ψ);
    rw [hval];
    grind [val_neg, LogicalConnective.Prop.neg_eq];
termination_by Γ s _ _ _ _ _ => (s, match Γ with | 𝚺 => 0 | 𝚷 => 1)

end

def exs (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ n :=
  (∃'[‘#0 + 1’] (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).sigma

def all (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1)) : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ n := ∼(exs (∼φ))

local prefix:64 "∃' " => Prenex.exs
local prefix:64 "∀' " => Prenex.all

private lemma models_exs [V↓[ℒₒᵣ] ⊧* 𝗕𝚷s] (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (s + 1) ξ (n + 1))
    (e : Fin n → V) :
    Semiformula.Eval e f (∃' φ).val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕 𝚷 s);
  have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
  rw [exs, models_sigma];
  have hβeval : ∀ z : V,
      Semiformula.Eval (z :> e) f
        (∃'[‘#0 + 1’] (∃'[‘#1 + 1’]
          (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ)))))).val ↔
        ∃ y ≤ z, Semiformula.Eval (y :> z :> e) f
          (∃'[‘#1 + 1’] (φ.sigmaInv.rew (Rew.subst (#0 :> #1 :> (#·.succ.succ.succ))))).val := by
    intro z;
    rw [models_bexs];
    simp [Arithmetic.lt_succ_iff_le];
  simp only [hβeval, models_bexs_witness models_bexs φ, models_sigmaInv φ];
  constructor;
  · rintro ⟨z, y, -, x, -, hx⟩;
    exact ⟨y, x, hx⟩;
  · rintro ⟨y, x, hx⟩;
    exact ⟨max x y, y, le_max_right x y, x, le_max_left x y, hx⟩;

private lemma models_all [V↓[ℒₒᵣ] ⊧* 𝗕𝚷s] (φ : ℬ[<, ℒₒᵣ].Prenex 𝚷 (s + 1) ξ (n + 1))
    (e : Fin n → V) :
    Semiformula.Eval e f (∀' φ).val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  have hthis : Semiformula.Eval e f (∃' ∼φ).val ↔ ∃ x, Semiformula.Eval (x :> e) f (∼φ).val :=
    models_exs (∼φ) e;
  have hval : (∀' φ).val = ∼(∃' ∼φ).val := by
    unfold all;
    exact val_neg (∃' ∼φ);
  rw [hval];
  grind [val_neg, LogicalConnective.Prop.neg_eq];

theorem models_exists_prenex {Γ Γ' : Polarity} {s n : ℕ} {φ : ArithmeticSemiformula ξ n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) :
  ∃ φ' : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n,
    ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗕 Γ' s],
      ∀ (e : Fin n → V) (f : ξ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f φ'.val := by
  suffices h' : ∃ φ' : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n,
      ∀ (V : Type _) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PrenexBase s],
        ∀ (e : Fin n → V) (f : ξ → V), Semiformula.Eval e f φ ↔ Semiformula.Eval e f φ'.val by
    obtain ⟨φ', hφ'⟩ := h';
    use φ';
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy Γ' s;
    exact hφ' V e f;
  induction h with
  | @bounded Γ s n φ h =>
    use ofΔ₀ ⟨φ, h⟩ Γ s;
    intro V _ _ e f;
    exact (models_ofΔ₀ ⟨φ, h⟩ e).symm;
  | and _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋏ ψ';
    intro V _ _ e f;
    grind [models_and φ' ψ' e, LogicalConnective.Prop.and_eq];
  | or _ _ ihφ ihψ =>
    obtain ⟨φ', hφ'⟩ := ihφ;
    obtain ⟨ψ', hψ'⟩ := ihψ;
    use φ' ⋎ ψ';
    intro V _ _ e f;
    grind [models_or φ' ψ' e, LogicalConnective.Prop.or_eq];
  | ball hR pos _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀'[u] φ';
    intro V _ _ e f;
    rw [models_ball u φ' e, Semiformula.eval_ball];
    exact forall_congr' fun x => (imp_congr Iff.rfl (hφ' V (x :> e) f)).trans (by simp);
  | bexs hR pos _ ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨u, rfl⟩ := Rew.positive_iff.mp pos;
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃'[u] φ';
    intro V _ _ e f;
    rw [models_bexs u φ' e, Semiformula.eval_bexs];
    exact exists_congr fun x => (and_congr Iff.rfl (hφ' V (x :> e) f)).trans (by simp);
  | @exs s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∃' φ';
    intro V _ _ e f;
    rw [models_exs φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e) f;
  | @all s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use ∀' φ';
    intro V _ _ e f;
    rw [models_all φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e) f;
  | @sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.sigma;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    rw [models_sigma φ' e, Semiformula.eval_ex];
    exact exists_congr fun x => hφ' V (x :> e) f;
  | @pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use φ'.pi;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase s := models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 s;
    rw [models_pi φ' e, Semiformula.eval_all];
    exact forall_congr' fun x => hφ' V (x :> e) f;
  | @dummy_sigma s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∀' φ').altUp;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase (s + 1) :=
      models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 (s + 1);
    exact Semiformula.eval_all.trans
      ((forall_congr' fun x => hφ' V (x :> e) f).trans
        ((models_all φ' e).symm.trans (models_altUp (∀' φ') e).symm));
  | @dummy_pi s n φ _ ih =>
    obtain ⟨φ', hφ'⟩ := ih;
    use (∃' φ').altUp;
    intro V _ _ e f;
    have : V↓[ℒₒᵣ] ⊧* PrenexBase (s + 1) :=
      models_PrenexBase_of_models_CollectionOnPrenexHierarchy 𝚷 (s + 1);
    exact Semiformula.eval_ex.trans
      ((exists_congr fun x => hφ' V (x :> e) f).trans
      ((models_exs φ' e).symm.trans (models_altUp (∃' φ') e).symm));

end Bounding.Prenex

namespace Bounding.Hierarchy

open Arithmetic

variable {Γ : Polarity} {s n : ℕ}

noncomputable def prenex {ξ : Type*} {φ : ArithmeticSemiformula ξ n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) : ℬ[<, ℒₒᵣ].Prenex Γ s ξ n :=
  (Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) h).choose

lemma provable_prenex (T : ArithmeticTheory) [𝗕𝚺s ⪯ T] {φ : ArithmeticSemisentence n}
    (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) : T ⊢ ∀¹* (φ 🡘 h.prenex.val) := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := eq_weakerThan_of_BSigma (s := s);
  apply provable_iff_of_models_iff.{0};
  intro V _ _ e;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 s := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* T);
  exact (Prenex.models_exists_prenex (Γ' := 𝚺) h).choose_spec V e Empty.elim;

end Bounding.Hierarchy

namespace Arithmetic

section

variable {Γ : Polarity} {s : ℕ} (T : ArithmeticTheory) [𝗕𝚺s ⪯ T]
         {n : ℕ} {φ : ArithmeticSemisentence n}

theorem exists_prenex_of_hierarchy (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) :
  ∃ φ' : ℬ[<, ℒₒᵣ].Prenex Γ s Empty n, T ⊢ ∀¹* (φ 🡘 φ'.val) := ⟨_, h.provable_prenex T⟩

theorem exists_matrix_provable (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) :
  ∃ φ₀ : ℬ[<, ℒₒᵣ].Semisentence (n + s), T ⊢ ∀¹* (φ 🡘 φ₀.val.toPrenex Γ s) := by
  obtain ⟨_, hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨_, by simpa [Bounding.Prenex.val] using hφ'⟩;

theorem exists_prenexHierarchy_of_hierarchy (h : ℬ[<, ℒₒᵣ].Hierarchy Γ s φ) :
  ∃ ψ : ArithmeticSemisentence n, ℬ[<, ℒₒᵣ].PrenexHierarchy Γ s ψ ∧ T ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy T h;
  exact ⟨φ'.val, Bounding.Prenex.val_prenexHierarchy, hφ'⟩;

end

lemma PrenexDefinable.of_definable {V : Type*} [ORingStructure V] {Γ Γ' : Polarity} {s k : ℕ}
    [V↓[ℒₒᵣ] ⊧* 𝗕 Γ' s] {P : (Fin k → V) → Prop} (hP : Γᴬ_[s].Definable P) :
    PrenexDefinable Γ s P := by
  obtain ⟨φ, hφ⟩ := hP;
  obtain ⟨θ, hθ⟩ := Bounding.Prenex.models_exists_prenex (Γ' := Γ') φ.polarity_prop;
  exact ⟨θ.val, Bounding.Prenex.val_prenexHierarchy, fun v ↦ (hθ V v id).symm.trans hφ.iff⟩;

end Arithmetic

end FFL.FirstOrder
