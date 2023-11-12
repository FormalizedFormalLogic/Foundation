import Logic.Predicate.FirstOrder.Arith.PAminus
import Logic.Vorspiel.Arith
import Logic.Predicate.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

local notation "OR" => Language.oRing

lemma Hierarchy.equal {t u : Subterm Language.oRing μ n} : Hierarchy b s “!!t = !!u” := by
  simp[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]

namespace Incompleteness

open Nat.ArithPart₁

def codeAux : {k : ℕ} → Nat.ArithPart₁.Code k → Formula OR (Fin (k + 1))
  | _, Code.zero _    => “&0 = 0”
  | _, Code.one _     => “&0 = 1”
  | _, Code.add i j   => “&0 = !!&i.succ + !!&j.succ”
  | _, Code.mul i j   => “&0 = !!&i.succ * !!&j.succ”
  | _, Code.equal i j => “(!!&i.succ = !!&j.succ ∧ &0 = 1) ∨ (!!&i.succ ≠ !!&j.succ ∧ &0 = 0)”
  | _, Code.lt i j    => “(!!&i.succ < !!&j.succ ∧ &0 = 1) ∨ (¬!!&i.succ < !!&j.succ ∧ &0 = 0)”
  | _, Code.proj i    => “&0 = !!&i.succ”
  | _, Code.comp c d  =>
    exClosure (((Rew.bind ![] (&0 :> (#·))).hom (codeAux c)) ⋏
      Matrix.conj fun i => (Rew.bind ![] (#i :> (&·.succ))).hom (codeAux (d i)))
  | _, Code.rfind c   =>
    (Rew.bind ![] (Subterm.Operator.numeral OR 0 :> &0 :> (&·.succ))).hom (codeAux c) ⋏
    (∀[“#0 < &0”] ∃' “#0 ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))

def code (c : Code k) : Subsentence OR (k + 1) := (Rew.bind ![] (#0 :> (#·.succ))).hom (codeAux c)

lemma codeAux_sigma_zero {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (codeAux c) := by
  induction c <;> simp[codeAux, Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]
  case comp c d ihc ihg =>
    exact Hierarchy.exClosure (by simp; exact ⟨Hierarchy.rew _ ihc, fun i => Hierarchy.rew _ (ihg i)⟩)
  case rfind k c ih =>
    exact ⟨Hierarchy.rew _ ih, by
      suffices : Hierarchy.Sigma 1 (n := 0) (∀[“#0 < &0”] ∃' “#0 ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))
      · simpa[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
          Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq] using this
      exact Hierarchy.ball' &0 (by simp) (Hierarchy.ex $ by
        simp[Hierarchy.neg_iff, Hierarchy.equal]; exact Hierarchy.rew _ ih)⟩

lemma code_sigma_zero {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_zero c)

lemma models_codeAux {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Subformula.Eval! ℕ ![] (y :> v) (codeAux c) ↔ f (Vector.ofFn v) = Part.some y := by
  induction hc generalizing y <;> simp[code, codeAux, models_iff]
  case zero =>
    have : (0 : Part ℕ) = Part.some 0 := rfl
    simp[this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp[this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp[hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    by_cases hv : v i < v j <;> simp[hv, Nat.isLtNat, eq_comm]
    · simp[Nat.not_le.mpr hv]
    · intro _; exact Nat.not_lt.mp hv
  case add => simp[eq_comm]
  case mul => simp[eq_comm]
  case proj => simp[eq_comm]
  case comp c d f g _ _ ihf ihg =>
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp[hg, hf]
    · intro h
      have : ∃ w, (∀ i, Vector.get w i ∈ g i (Vector.ofFn v)) ∧ y ∈ f w := by
        simpa using Part.eq_some_iff.mp h
      rcases this with ⟨w, hw, hy⟩
      exact ⟨w.get, (ihf y w.get).mpr (by simpa[Part.eq_some_iff] using hy),
        fun i => (ihg i (w.get i) v).mpr (by simpa[Part.eq_some_iff] using hw i)⟩
  case rfind c f _ ihf =>
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons', ihf, Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩; simp[Part.eq_some_iff]
      exact ⟨by simpa using hy, by intro z hz; simpa using h z hz⟩
    · intro h; simpa using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Subformula.Eval! ℕ (y :> v) Empty.elim (code c) ↔ y ∈ f (Vector.ofFn v) := by
  simpa[code, models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec {k} (f : Vector ℕ k →. ℕ) : Code k :=
  Classical.epsilon (fun c => ∀ y v, Subformula.Eval! ℕ (y :> v) Empty.elim (code c) ↔ y ∈ f (Vector.ofFn v))

lemma codeOfPartrec_spec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    Subformula.Eval! ℕ (y :> v) Empty.elim (code $ codeOfPartrec f) ↔ y ∈ f (Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Subformula.Eval! ℕ (y :> v) Empty.elim (code c) ↔ y ∈ f (Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

noncomputable def isProof (T : Theory OR) : Subsentence OR 2 :=
  (Rew.substs ![Subterm.Operator.numeral OR 1, #0, #1]).hom
    (code (k := 2) (codeOfPartrec (fun v => Part.some $ provFn T (v.get 1) (v.get 0))))

noncomputable def prv (T : Theory OR) : Subsentence OR 1 := ∃' isProof T

variable {T : Theory OR} (hT : Computable (fun x => decide (T x)))

lemma isProof_iff (σ : Sentence OR) :
    Nonempty (T ⊢ σ) ↔ ∃ b, Subformula.Eval! ℕ ![b, Encodable.encode σ] Empty.elim (isProof T) := by
  have : Nat.Partrec' fun v : Vector ℕ 2 => Part.some $ provFn T (v.get 1) (v.get 0) :=
    Nat.Partrec'.part_iff.mpr
      (Computable.partrec $ (provFn_computable hT).comp
        (Computable.vector_get.comp Computable.id (Computable.const 1))
        (Computable.vector_get.comp Computable.id (Computable.const 0)))
  simp[isProof, Subformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, provable_iff_provFn]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by
      simpa using (codeOfPartrec_spec this (y := 1) (v := ![b, Encodable.encode σ])).mpr (by simp[hb])⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by
      symm; simpa using (codeOfPartrec_spec this (y := 1) (v := ![b, Encodable.encode σ])).mp (by simp[hb])⟩

lemma prv_iff_provable (σ : Sentence OR) :
    Nonempty (T ⊢ σ) ↔ Subformula.Eval! ℕ ![Encodable.encode σ] Empty.elim (prv T) := by
  simp[prv, isProof_iff hT]

lemma prv_iff_provable' (σ : Sentence OR) :
    ℕ ⊧ ([→ Subterm.Operator.numeral OR (Encodable.encode σ)].hom $ prv T) ↔ Nonempty (T ⊢ σ) := by
  simp[models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton, prv_iff_provable hT]

end Incompleteness

end Arith

end FirstOrder

end LO
