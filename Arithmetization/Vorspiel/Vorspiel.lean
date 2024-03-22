import Logic.FirstOrder.Arith.PAminus
import Logic.FirstOrder.Arith.StrictHierarchy

instance [Zero α] : Nonempty α := ⟨0⟩

namespace Set

@[simp] lemma subset_union_three₁ (s t u : Set α) : s ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₂ (s t u : Set α) : t ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_left (by simp) _

@[simp] lemma subset_union_three₃ (s t u : Set α) : u ⊆ s ∪ t ∪ u := Set.subset_union_of_subset_right (by rfl) _

end Set

namespace Matrix

lemma fun_eq_vec₃ {v : Fin 3 → α} : v = ![v 0, v 1, v 2] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]

lemma fun_eq_vec₄ {v : Fin 4 → α} : v = ![v 0, v 1, v 2, v 3] := by
  funext x
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  cases' x using Fin.cases with x <;> simp [Fin.eq_zero]
  rfl

@[simp] lemma cons_app_four {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ → α) : (a :> s) 4 = s 3 := rfl

@[simp] lemma cons_app_five {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ → α) : (a :> s) 5 = s 4 := rfl

@[simp] lemma cons_app_six {n : ℕ} (a : α) (s : Fin n.succ.succ.succ.succ.succ.succ → α) : (a :> s) 6 = s 5 := rfl

lemma eq_vecCons' (s : Fin (n + 1) → C) : s = s 0 :> (s ·.succ) :=
   funext $ Fin.cases (by simp) (by simp)

end Matrix

instance : ToString Empty := ⟨Empty.elim⟩

class Hash (α : Type*) where
  hash : α → α → α

infix:80 " # " => Hash.hash

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x

namespace LO

section

variable (F : Type*) [LogicalConnective F] {T U : Set F}

class TheoryCut [System F] where
  theoryCut {T : Set F} {U : Set F} {p : F} : T ⊢* U → U ⊢ p → T ⊢ p

variable {F}

namespace System

variable [System F]

namespace Subtheory

lemma of_theoryCut [TheoryCut F] (h : U ⊢* T) : T ≾ U := ⟨fun hf ↦ TheoryCut.theoryCut h hf⟩

end Subtheory

lemma provableTheory_iff : T ⊢*! U ↔ ∀ f ∈ U, T ⊢! f :=
  ⟨by rintro ⟨h⟩ f hf; exact ⟨h hf⟩, fun h ↦ ⟨fun hf ↦ (h _ hf).toProof⟩⟩

end System

namespace Gentzen

variable [Gentzen F] [Gentzen.Cut F]

instance : TheoryCut F := ⟨Gentzen.proofCut⟩

end Gentzen

namespace Complete

variable [𝓑 : System F] {α : Type*} [𝓢 : Semantics F α] [Complete F]

lemma provableTheory_iff : T ⊢*! U ↔ (∀ s, s ⊧* T → s ⊧* U) := by
  simp [System.provableTheory_iff, ←consequence_iff_provable]
  constructor
  · intro h s hs f hf; exact h f hf hs
  · intro h f hf s hs; exact h s hs hf

end Complete

end

namespace FirstOrder

namespace Semiterm

@[simp] lemma bshift_positive (t : Semiterm L ξ n) : Positive (Rew.bShift t) := by
  induction t <;> simp

lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_of_forall_not_mem <| by simp [Positive, Fin.eq_zero] at ht ⊢; assumption

variable {M : Type*} {s : Structure L M}

@[simp] lemma val_toS {e : Fin n → M} (t : Semiterm L (Fin n) 0) :
    bVal s e (Rew.toS t) = val s ![] e t := by
  simp[val_rew, Matrix.empty_eq]; congr

@[simp] lemma val_toF {e : Fin n → M} (t : Semiterm L Empty n) :
    val s ![] e (Rew.toF t) = bVal s e t := by
  simp[val_rew, Matrix.empty_eq]; congr
  funext i; simp; contradiction

end Semiterm

namespace Rew

lemma substs_bv (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ m) :
    (Rew.substs v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]

@[simp] lemma substs_positive (t : Semiterm L ξ n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.substs v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp [Semiterm.Positive, substs_bv]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩

lemma embSubsts_bv (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ m) :
    (Rew.embSubsts v t).bv = t.bv.biUnion (fun i ↦ (v i).bv) := by
  induction t <;> simp [Rew.func, Semiterm.bv_func, Finset.biUnion_biUnion, *]
  · contradiction

@[simp] lemma embSubsts_positive (t : Semiterm L Empty n) (v : Fin n → Semiterm L ξ (m + 1)) :
    (Rew.embSubsts v t).Positive ↔ ∀ i ∈ t.bv, (v i).Positive := by
  simp [Semiterm.Positive, embSubsts_bv]
  exact ⟨fun H i hi x hx ↦ H x i hi hx, fun H x i hi hx ↦ H i hi x hx⟩

end Rew



namespace Arith

attribute [simp] Semiformula.eval_substs Semiformula.eval_embSubsts
  Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

section ToString

variable [ToString μ]

open Semiterm Semiformula

def termToStr : Semiterm ℒₒᵣ μ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _   => "1"
  | func Language.Add.add v   => "(" ++ termToStr (v 0) ++ " + " ++ termToStr (v 1) ++ ")"
  | func Language.Mul.mul v   => "(" ++ termToStr (v 0) ++ " \\cdot " ++ termToStr (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ μ n) := ⟨fun t _ => termToStr t⟩

instance : ToString (Semiterm ℒₒᵣ μ n) := ⟨termToStr⟩

def formulaToStr : ∀ {n}, Semiformula ℒₒᵣ μ n → String
  | _, ⊤                             => "\\top"
  | _, ⊥                             => "\\bot"
  | _, rel Language.Eq.eq v          => termToStr (v 0) ++ " = " ++ termToStr (v 1)
  | _, rel Language.LT.lt v          => termToStr (v 0) ++ " < " ++ termToStr (v 1)
  | _, nrel Language.Eq.eq v         => termToStr (v 0) ++ " \\not = " ++ termToStr (v 1)
  | _, nrel Language.LT.lt v         => termToStr (v 0) ++ " \\not < " ++ termToStr (v 1)
  | _, p ⋏ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\land " ++ "[" ++ formulaToStr q ++ "]"
  | _, p ⋎ q                         => "[" ++ formulaToStr p ++ "]" ++ " \\lor "  ++ "[" ++ formulaToStr q ++ "]"
  | n, ∀' (rel Language.LT.lt v ⟶ p) => "(\\forall x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ p) => "(\\exists x_{" ++ toString n ++ "} < " ++ termToStr (v 1) ++ ") " ++ "[" ++ formulaToStr p  ++ "]"
  | n, ∀' p                          => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"
  | n, ∃' p                          => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ formulaToStr p ++ "]"

instance : Repr (Semiformula ℒₒᵣ μ n) := ⟨fun t _ => formulaToStr t⟩

instance : ToString (Semiformula ℒₒᵣ μ n) := ⟨formulaToStr⟩

end ToString

namespace Hierarchy

variable {L : Language} [L.LT]

lemma of_zero {b b'} {s : ℕ} {p : Semiformula L μ n} (hp : Hierarchy b 0 p) : Hierarchy b' s p := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp b' pos

lemma iff_iff {p q : Semiformula L μ n} :
    Hierarchy b s (p ⟷ q) ↔ (Hierarchy b s p ∧ Hierarchy b.alt s p ∧ Hierarchy b s q ∧ Hierarchy b.alt s q) := by
  simp[Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {p q : Semiformula L μ n} :
    Hierarchy b 0 (p ⟷ q) ↔ (Hierarchy b 0 p ∧ Hierarchy b 0 q) := by
  simp[Semiformula.iff_eq]; tauto

end Hierarchy

section model

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T]

variable (M : Type) [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

lemma oring_sound {σ : Sentence ℒₒᵣ} (h : T ⊢! σ) : M ⊧ₘ σ := consequence_iff'.mp (LO.Sound.sound! h) M

end model

end Arith

namespace Theory.Mod

variable (M : Type _) [Nonempty M] [Structure L M] (T U : Theory L)

lemma of_provably_subtheory (_ : T ≾ U) [U.Mod M] : T.Mod M :=
  of_subtheory M (Semantics.ofSystemSubtheory T U)

lemma of_provably_subtheory' [T ≾ U] [U.Mod M] : T.Mod M := of_provably_subtheory M T U inferInstance

lemma of_add_left [(T + U).Mod M] : T.Mod M := of_ss M (show T ⊆ T + U from by simp [Theory.add_def])

lemma of_add_right [(T + U).Mod M] : U.Mod M := of_ss M (show U ⊆ T + U from by simp [Theory.add_def])

variable [L.Eq]

-- instance of_add_left_eq [(T + 𝐄𝐪 : Theory L).Mod M] : T.Mod M := of_add_left M T 𝐄𝐪

end Theory.Mod

section

variable {L : Language}

def ballClosure : {n : ℕ} → (Fin n → Semiformula L ξ 1) → Semiformula L ξ n → Formula L ξ
  | 0,     _, q => q
  | _ + 1, p, q => ballClosure (p ·.succ) (∀[(p 0)/[#0]] q)

@[simp] lemma ball_closure_zero (p : Fin 0 → Semiformula L ξ 1) (q : Semiformula L ξ 0) : ballClosure p q = q := rfl

lemma ball_closure_succ (p : Fin (n + 1) → Semiformula L ξ 1) (q : Semiformula L ξ (n + 1)) :
    ballClosure p q = ballClosure (p ·.succ) (∀[(p 0)/[#0]] q) := rfl

def bexClosure : {n : ℕ} → (Fin n → Semiformula L ξ 1) → Semiformula L ξ n → Formula L ξ
  | 0,     _, q => q
  | _ + 1, p, q => bexClosure (p ·.succ) (∃[(p 0)/[#0]] q)

@[simp] lemma bex_closure_zero (p : Fin 0 → Semiformula L ξ 1) (q : Semiformula L ξ 0) : bexClosure p q = q := rfl

lemma bex_closure_succ (p : Fin (n + 1) → Semiformula L ξ 1) (q : Semiformula L ξ (n + 1)) :
    bexClosure p q = bexClosure (p ·.succ) (∃[(p 0)/[#0]] q) := rfl

namespace Semiformula

variable {M : Type _} [Nonempty M] {s : Structure L M}

variable {n : ℕ} {ε : ξ → M}

@[simp] lemma eval_ballClosure {p : Fin n → Semiformula L ξ 1} {q : Semiformula L ξ n} :
    Val s ε (ballClosure p q) ↔ ∀ e : Fin n → M, (∀ i, Eval s ![e i] ε (p i)) → Eval s e ε q := by
  induction' n with n IH
  · simp [Matrix.empty_eq]
  · simp [ball_closure_succ, IH]
    constructor
    · intro H e h
      simpa [←Matrix.eq_vecCons'] using H (e ·.succ) (fun i ↦ h i.succ) (e 0) (h 0)
    · intro H e h x hx
      exact H (x :> e) (Fin.cases (by simpa [Matrix.empty_eq] using hx) (fun i ↦ by simpa using h i))

@[simp] lemma eval_bexClosure {p : Fin n → Semiformula L ξ 1} {q : Semiformula L ξ n} :
    Val s ε (bexClosure p q) ↔ ∃ e : Fin n → M, (∀ i, Eval s ![e i] ε (p i)) ∧ Eval s e ε q := by
  induction' n with n IH
  · simp [Matrix.empty_eq]
  · simp [bex_closure_succ, IH]
    constructor
    · rintro ⟨e, he, x, hx, H⟩
      exact ⟨x :> e, Fin.cases hx he, H⟩
    · rintro ⟨e, h, H⟩
      exact ⟨(e ·.succ), fun i ↦ h i.succ, e 0, h 0, by simpa [←Matrix.eq_vecCons'] using H⟩

end Semiformula

namespace Arith.Hierarchy

variable [L.LT] {μ : Type v}

lemma ballClosure_iff {b s n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1} (hv : ∀ i, (v i).Positive) :
    Hierarchy b s (ballClosure (fun i ↦ “#0 < !!(v i)”) p) ↔ Hierarchy b s p := by
  induction' n with n IH <;> simp [ballClosure, ←Rew.comp_app]
  refine Iff.trans (IH (p := “∀[#0 < !!([→ #0] (v 0))] !p”) (v := (v ·.succ)) (by intro; simp [hv])) ?_
  rw [ball_iff]; simp [Semiterm.bv_eq_empty_of_positive (hv 0)]

lemma bexClosure_iff {b s n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1} (hv : ∀ i, (v i).Positive) :
    Hierarchy b s (bexClosure (fun i ↦ “#0 < !!(v i)”) p) ↔ Hierarchy b s p := by
  induction' n with n IH <;> simp [bexClosure, ←Rew.comp_app]
  refine Iff.trans (IH (p := “∃[#0 < !!([→ #0] (v 0))] !p”) (v := (v ·.succ)) (by intro; simp [hv])) ?_
  rw [bex_iff]; simp [Semiterm.bv_eq_empty_of_positive (hv 0)]

@[simp] lemma matrix_conj_iff {b s n} {p : Fin m → Semiformula L ξ n} :
    Hierarchy b s (Matrix.conj fun j ↦ p j) ↔ ∀ j, Hierarchy b s (p j) := by
  cases m <;> simp

lemma remove_forall {p : Semiformula L ξ (n + 1)} : Hierarchy b s (∀' p) → Hierarchy b s p := by
  intro h; rcases h
  case ball => simpa
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists {p : Semiformula L ξ (n + 1)} : Hierarchy b s (∃' p) → Hierarchy b s p := by
  intro h; rcases h
  case bex => simpa
  case ex => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

end Arith.Hierarchy

namespace Arith.HClassIn

variable [L.LT]

variable [DecidableEq ξ] {ξ₁ : Type*} [DecidableEq ξ₁] {ξ₂ : Type*} [DecidableEq ξ₂]

open Class

lemma hClass_domain (p : Semiformula L ξ n) : (HClass L ξ Γ s).Domain p ↔ Hierarchy Γ s p := by rfl

lemma hClass_zero_le_hClass (Γ s) : HClass L ξ Γ' 0 ≤ HClass L ξ Γ s := by
  intro _ p hp; exact Hierarchy.mono (by simpa [hClass_domain, Hierarchy.zero_iff_delta_zero] using hp) (zero_le s)

variable (T : Theory L)

lemma zero_le (Γ s) : HClassIn ξ Γ' 0 T ≤ HClassIn ξ Γ s T :=
  eqvClosure_monotone (hClass_zero_le_hClass Γ s) T

lemma deltaZeroIn_le_hClassIn (Γ s) : DeltaZeroIn ξ T ≤ HClassIn ξ Γ s T :=
  Class.eqvClosure_monotone (hClass_zero_le_hClass Γ s) T

variable {T}

lemma of_deltaZeroIn {p : Semiformula L ξ n} (hp : (DeltaZeroIn ξ T).Domain p) : (HClassIn ξ Γ s T).Domain p :=
  deltaZeroIn_le_hClassIn T Γ s hp

@[formula_class] def rew {p : Semiformula L ξ₁ n₁} (hp : (HClassIn ξ₁ Γ s T).Domain p) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    (HClassIn ξ₂ Γ s T).Domain (ω.hom p) := by
  rcases hp with ⟨p', hp', H⟩
  exact ⟨ω.hom p', Hierarchy.rew ω hp', H.rew ω⟩

lemma all {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Π (s + 1) T).Domain p → (HClassIn ξ Π (s + 1) T).Domain (∀' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, Hierarchy.all hp', H.all⟩

lemma ex {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Σ (s + 1) T).Domain p → (HClassIn ξ Σ (s + 1) T).Domain (∃' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, Hierarchy.ex hp', H.ex⟩

lemma pi {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Σ s T).Domain p → (HClassIn ξ Π (s + 1) T).Domain (∀' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, Hierarchy.pi hp', H.all⟩

lemma sigma {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Π s T).Domain p → (HClassIn ξ Σ (s + 1) T).Domain (∃' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, Hierarchy.sigma hp', H.ex⟩

lemma dummy_pi {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Σ (s + 1) T).Domain p → (HClassIn ξ Π (s + 1 + 1) T).Domain (∃' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, hp'.dummy_pi, H.ex⟩

lemma dummy_sigma {p : Semiformula L ξ (n + 1)} : (HClassIn ξ Π (s + 1) T).Domain p → (HClassIn ξ Σ (s + 1 + 1) T).Domain (∀' p) := by
  rintro ⟨p', hp', H⟩; exact ⟨_, hp'.dummy_sigma, H.all⟩

end Arith.HClassIn

namespace Class

variable [L.LT] {ξ : Type*} [DecidableEq ξ] {c : Class L ξ}

protected lemma ballClosure [c.BAll] {n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1}
    (hv : ∀ i, (v i).Positive) (H : c.Domain p) : c.Domain (ballClosure (fun i ↦ “#0 < !!(v i)”) p) := by
  induction' n with n IH <;> simp [H, ballClosure, ←Rew.comp_app]
  have : c.Domain “∀[#0 < !!([→ #0] (v 0))] !p” :=
    Class.BAll.ball (t := Rew.substs ![#0] (v 0)) H (by simp [Semiterm.bv_eq_empty_of_positive (hv 0)])
  exact IH (fun i ↦ hv i.succ) this

protected lemma bexClosure [c.BEx] {n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1}
    (hv : ∀ i, (v i).Positive) (H : c.Domain p) :
    c.Domain (bexClosure (fun i ↦ “#0 < !!(v i)”) p) := by
  induction' n with n IH <;> simp [H, bexClosure, ←Rew.comp_app]
  have : c.Domain “∃[#0 < !!([→ #0] (v 0))] !p” :=
    Class.BEx.bex (t := Rew.substs ![#0] (v 0)) H (by simp [Semiterm.bv_eq_empty_of_positive (hv 0)])
  exact IH (fun i ↦ hv i.succ) this

lemma matrix_conj [c.Atom] [c.And] {n} {p : Fin m → Semiformula L ξ n} (H : ∀ j, c.Domain (p j)) :
    c.Domain (Matrix.conj p) := by
  induction' m with m ih <;> simp [Matrix.conj]
  · exact And.and (H 0) (ih fun j ↦ by simpa using H j.succ)

end Class

end

end FirstOrder

end LO
