import Logic.FirstOrder.Arith.PeanoMinus
import Logic.FirstOrder.Arith.EA.Basic

instance [Zero α] : Nonempty α := ⟨0⟩

notation "exp " x:90 => Exp.exp x

namespace Matrix

lemma forall_iff {n : ℕ} (p : (Fin (n + 1) → α) → Prop) :
    (∀ v, p v) ↔ (∀ a, ∀ v, p (a :> v)) :=
  ⟨fun h a v ↦ h (a :> v), fun h v ↦ by simpa [←eq_vecCons v] using h (v 0) (v ∘ Fin.succ)⟩

end Matrix

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

lemma eq_vecCons' (s : Fin (n + 1) → C) : s 0 :> (s ·.succ) = s :=
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

namespace Polarity

variable {α : Type*} [SigmaSymbol α] [PiSymbol α]

protected def coe : Polarity → α
 | 𝚺 => 𝚺
 | 𝚷 => 𝚷

instance : Coe Polarity α := ⟨Polarity.coe⟩

@[simp] lemma coe_sigma : ((𝚺 : Polarity) : α) = 𝚺 := rfl

@[simp] lemma coe_pi : ((𝚷 : Polarity) : α) = 𝚷 := rfl

end Polarity

namespace SigmaPiDelta

@[simp] lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by cases Γ <;> simp

end SigmaPiDelta

namespace FirstOrder

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

section model

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T]

variable (M : Type*) [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* T]

lemma oring_sound {σ : Sentence ℒₒᵣ} (h : T ⊢! σ) : M ⊧ₘ σ := (consequence_iff' (T := T)).mp (LO.Sound.sound h) M

instance indScheme_of_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃Γ n] :
    M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) := models_indScheme_of_models_indH Γ n

end model

end Arith

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

variable {M : Type*} [Nonempty M] {s : Structure L M}

variable {n : ℕ} {ε : ξ → M}

@[simp] lemma eval_ballClosure {p : Fin n → Semiformula L ξ 1} {q : Semiformula L ξ n} :
    Evalf s ε (ballClosure p q) ↔ ∀ e : Fin n → M, (∀ i, Eval s ![e i] ε (p i)) → Eval s e ε q := by
  induction' n with n IH
  · simp [Matrix.empty_eq]
  · simp [ball_closure_succ, IH]
    constructor
    · intro H e h
      simpa [Matrix.eq_vecCons'] using H (e ·.succ) (fun i ↦ h i.succ) (e 0) (h 0)
    · intro H e h x hx
      exact H (x :> e) (Fin.cases (by simpa [Matrix.empty_eq] using hx) (fun i ↦ by simpa using h i))

@[simp] lemma eval_bexClosure {p : Fin n → Semiformula L ξ 1} {q : Semiformula L ξ n} :
    Evalf s ε (bexClosure p q) ↔ ∃ e : Fin n → M, (∀ i, Eval s ![e i] ε (p i)) ∧ Eval s e ε q := by
  induction' n with n IH
  · simp [Matrix.empty_eq]
  · simp [bex_closure_succ, IH]
    constructor
    · rintro ⟨e, he, x, hx, H⟩
      exact ⟨x :> e, Fin.cases hx he, H⟩
    · rintro ⟨e, h, H⟩
      exact ⟨(e ·.succ), fun i ↦ h i.succ, e 0, h 0, by simpa [Matrix.eq_vecCons'] using H⟩

@[simp] lemma eval_operator₃ {o : Operator L 3} {t₁ t₂ t₃ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε] := by
  simp [eval_operator]

@[simp] lemma eval_operator₄ {o : Operator L 4} {t₁ t₂ t₃ t₄ : Semiterm L ξ n} :
    Eval s e ε (o.operator ![t₁, t₂, t₃, t₄]) ↔ o.val ![t₁.val s e ε, t₂.val s e ε, t₃.val s e ε, t₄.val s e ε] := by
  simp [eval_operator]

end Semiformula

namespace Arith.Hierarchy

variable [L.LT] {μ : Type v}

lemma ballClosure_iff {b s n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1} (hv : ∀ i, (v i).Positive) :
    Hierarchy b s (ballClosure (fun i ↦ “#0 < !!(v i)”) p) ↔ Hierarchy b s p := by
  induction' n with n IH <;> simp [ballClosure, ←Rew.comp_app]
  refine Iff.trans (IH (p := “∀[#0 < !!([→ #0] (v 0))] !!p”) (v := (v ·.succ)) (by intro; simp [hv])) ?_
  rw [ball_iff]; simp [Semiterm.bv_eq_empty_of_positive (hv 0)]

lemma bexClosure_iff {b s n} {p : Semiformula L ξ n} {v : Fin n → Semiterm L ξ 1} (hv : ∀ i, (v i).Positive) :
    Hierarchy b s (bexClosure (fun i ↦ “#0 < !!(v i)”) p) ↔ Hierarchy b s p := by
  induction' n with n IH <;> simp [bexClosure, ←Rew.comp_app]
  refine Iff.trans (IH (p := “∃[#0 < !!([→ #0] (v 0))] !!p”) (v := (v ·.succ)) (by intro; simp [hv])) ?_
  rw [bex_iff]; simp [Semiterm.bv_eq_empty_of_positive (hv 0)]

end Arith.Hierarchy

end

section

variable {M : Type*} [Nonempty M] [Structure L M]

abbrev Semiterm.Rlz (t : Semiterm L M n) (e : Fin n → M) : M := t.valm M e id

abbrev Semiformula.Rlz (p : Semiformula L M n) (e : Fin n → M) : Prop := Evalm M e id p

end

namespace Arith

variable {L : Language} [L.ORing]

instance : Semiterm.Operator.GoedelNumber L ℕ := ⟨Semiterm.Operator.numeral L⟩

end Arith

end FirstOrder

end LO
