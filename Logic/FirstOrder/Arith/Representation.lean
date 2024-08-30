import Logic.FirstOrder.Arith.PeanoMinus
import Logic.Vorspiel.Arith

namespace LO.FirstOrder.Arith

open Mathlib Encodable Semiterm.Operator.GoedelNumber

open Nat.ArithPart₁

def codeAux : {k : ℕ} → Nat.ArithPart₁.Code k → Formula ℒₒᵣ (Fin (k + 1))
  | _, Code.zero _    => “&0 = 0”
  | _, Code.one _     => “&0 = 1”
  | _, Code.add i j   => “&0 = &i.succ + &j.succ”
  | _, Code.mul i j   => “&0 = &i.succ * &j.succ”
  | _, Code.equal i j => “(&i.succ = &j.succ ∧ &0 = 1) ∨ (&i.succ ≠ &j.succ ∧ &0 = 0)”
  | _, Code.lt i j    => “(&i.succ < &j.succ ∧ &0 = 1) ∨ (&i.succ ≮ &j.succ ∧ &0 = 0)”
  | _, Code.proj i    => “&0 = !!&i.succ”
  | _, Code.comp c d  =>
    exClosure (((Rew.bind ![] (&0 :> (#·))).hom (codeAux c)) ⋏
      Matrix.conj fun i => (Rew.bind ![] (#i :> (&·.succ))).hom (codeAux (d i)))
  | _, Code.rfind c   =>
    (Rew.bind ![] (‘0’ :> &0 :> (&·.succ))).hom (codeAux c) ⋏
    (∀[“z. z < &0”] ∃' “z. z ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))

def code (c : Code k) : Semisentence ℒₒᵣ (k + 1) := (Rew.bind ![] (#0 :> (#·.succ))).hom (codeAux c)

section model

open LO.Arith

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

private lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalfm M (z :> v) (codeAux c) → Semiformula.Evalfm M (z' :> v) (codeAux c) → z = z' := by
  induction c generalizing z z' <;> simp [code, codeAux]
  case zero => rintro rfl rfl; rfl
  case one  => rintro rfl rfl; rfl
  case add  => rintro rfl rfl; rfl
  case mul  => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp [hv, -not_lt, ←not_lt]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc ihd =>
    simp [Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂;
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp [Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    intro h₁ hm₁ h₂ hm₂
    by_contra hz
    wlog h : z < z' with Hz
    case inr =>
      have : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hz) this
    have : ∃ x, x ≠ 0 ∧ (Semiformula.Evalfm M (x :> z :> fun i => v i)) (codeAux c) := hm₂ z h
    rcases this with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalbm M (z :> v) (code c) → Semiformula.Evalbm M (z' :> v) (code c) → z = z' := by
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons']
  exact codeAux_uniq

end model

private lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (codeAux c) := by
  induction c <;> simp [codeAux, Matrix.fun_eq_vec₂]
  case comp c d ihc ihg =>
    exact Hierarchy.exClosure (by simp [ihc, ihg])
  case rfind k c ih => simp [ih]

lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_one c)

@[simp] lemma natCast_nat (n : ℕ) : Nat.cast n = n := by rfl

private lemma models_codeAux {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Semiformula.Evalfm ℕ (y :> v) (codeAux c) ↔ f (Vector.ofFn v) = Part.some y := by
  induction hc generalizing y <;> simp [code, codeAux, models_iff]
  case zero =>
    have : (0 : Part ℕ) = Part.some 0 := rfl
    simp [this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp [this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp [hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    by_cases hv : v i < v j <;> simp [hv, Nat.isLtNat, eq_comm]
    · simp [Nat.not_lt.mp hv]
  case add => simp [eq_comm]
  case mul => simp [eq_comm]
  case proj => simp [eq_comm]
  case comp c d f g _ _ ihf ihg =>
    simp [Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp [hg, hf]
    · intro h
      have : ∃ w, (∀ i, Vector.get w i ∈ g i (Vector.ofFn v)) ∧ y ∈ f w := by
        simpa using Part.eq_some_iff.mp h
      rcases this with ⟨w, hw, hy⟩
      exact ⟨w.get, (ihf y w.get).mpr (by simpa[Part.eq_some_iff] using hy),
        fun i => (ihg i (w.get i) v).mpr (by simpa[Part.eq_some_iff] using hw i)⟩
  case rfind c f _ ihf =>
    simp [Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons', ihf, Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩; simp [Part.eq_some_iff]
      exact ⟨by simpa using hy, by intro z hz; simpa using h z hz⟩
    · intro h; simpa using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
  simpa[code, models_iff, Semiformula.eval_rew, Matrix.empty_eq, Function.comp,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec' {k} (f : Vector ℕ k →. ℕ) : Semisentence ℒₒᵣ (k + 1) :=
  code <| Classical.epsilon (fun c ↦ ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v))

lemma codeOfPartrec'_spec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    Semiformula.Evalbm ℕ (y :> v) (codeOfPartrec' f) ↔ y ∈ f (Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

end Arith

end FirstOrder

end LO
