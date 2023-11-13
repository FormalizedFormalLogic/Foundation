import Logic.Predicate.FirstOrder.Arith.PAminus
import Logic.Vorspiel.Arith
import Logic.Predicate.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

open Encodable

section

variable {L} [(k : ℕ) → DecidableEq (L.func k)] [(k : ℕ) → DecidableEq (L.rel k)]
  [ORing L] [Structure L ℕ]

abbrev SigmaOneSound (T : Theory L) := Sound T (Hierarchy.Sigma 1)

lemma consistent_of_sigmaOneSound (T : Theory L) [SigmaOneSound T] :
    Logic.System.Consistent T := consistent_of_sound T (Hierarchy.Sigma 1) (by simp)

end

lemma Hierarchy.equal {t u : Subterm Language.oRing μ n} : Hierarchy b s “!!t = !!u” := by
  simp[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]

abbrev godelNumber {α : Type*} [Primcodable α] (a : α) : Subterm.Const ℒₒᵣ := Subterm.Operator.numeral ℒₒᵣ (encode a)

notation: max "⸢" a "⸣" => godelNumber a

open Nat.ArithPart₁

def codeAux : {k : ℕ} → Nat.ArithPart₁.Code k → Formula ℒₒᵣ (Fin (k + 1))
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
    (Rew.bind ![] (⸢0⸣ :> &0 :> (&·.succ))).hom (codeAux c) ⋏
    (∀[“#0 < &0”] ∃' “#0 ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))

def code (c : Code k) : Subsentence ℒₒᵣ (k + 1) := (Rew.bind ![] (#0 :> (#·.succ))).hom (codeAux c)

lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (codeAux c) := by
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

lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_one c)

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

namespace FirstIncompleteness

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

section graph

lemma provable_iff_mem_partrec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (T ⊢! (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)) ↔ y ∈ f (Vector.ofFn v) := by
  let σ : Sentence ℒₒᵣ := (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)
  have sigma : Hierarchy.Sigma 1 σ :=
    (Hierarchy.rew (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣) (code_sigma_one (codeOfPartrec f)))
  constructor
  · rintro ⟨b⟩
    have : Subformula.Eval! ℕ (y :> v) Empty.elim (code $ codeOfPartrec f) := by
      simpa[models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons'] using
        Arith.Sound.sound sigma ⟨b⟩
    exact (codeOfPartrec_spec hf).mp this
  · intro h
    exact ⟨PAminus.sigma_one_completeness (T := T) sigma (by
      simp[models_iff, Subformula.eval_rew, Matrix.empty_eq,
        Function.comp, Matrix.comp_vecCons', codeOfPartrec_spec hf, h])⟩

section

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

noncomputable def graph (f : α →. σ) : Subsentence ℒₒᵣ 2 :=
  code (codeOfPartrec fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode)

theorem representation {f : α →. σ} (hf : Partrec f) {x y} :
    T ⊢! [→ ⸢y⸣, ⸢x⸣].hom (graph f) ↔ y ∈ f x := by
  let f' : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode
  have : Nat.Partrec' f' :=
    Nat.Partrec'.part_iff.mpr
      (Partrec.bind (Computable.ofOption $ Primrec.to_comp $ Primrec.decode.comp Primrec.vector_head)
      (Partrec.to₂ <| Partrec.map (hf.comp .snd) (Computable.encode.comp₂ .right)))
  simpa[Matrix.constant_eq_singleton] using
    provable_iff_mem_partrec this (y := encode y) (v := ![encode x])

end

end graph

variable (A : Logic.System.Complete T)

attribute [instance] Classical.propDecidable

variable (T)

noncomputable def diag : Subsentence ℒₒᵣ 1 → Bool := fun σ => T ⊢! [→ ⸢σ⸣].hom σ

local notation "d" => diag T

noncomputable def diagRefutation : Subsentence ℒₒᵣ 1 := [→ ⸢false⸣, #0].hom (graph (diag T : Subsentence ℒₒᵣ 1 →. Bool))

local notation "ρ" => diagRefutation T

variable {T}

lemma d_computable : Computable d := by
  let pr : Sentence ℒₒᵣ →. Bool := fun σ => (provableFn T σ).map (fun _ => true)
  let rf : Sentence ℒₒᵣ →. Bool := fun σ => (provableFn T (~σ)).map (fun _ => false)
  let d' : Subsentence ℒₒᵣ 1 →. Bool := fun σ => PFun.merge pr rf ([→ ⸢σ⸣].hom σ)
  have hpr : Partrec pr := Partrec.map provableFn_partrec (Computable.const true)
  have hrf : Partrec rf := Partrec.map
    ((provableFn_partrec (L := ℒₒᵣ)).comp $ Primrec.to_comp Subformula.neg_primrec) (Computable.const false)
  have H : ∀ σ b, b ∈ pr σ → ∀ b', b' ∈ rf σ → b = b' := by
    simp; rintro σ ⟨⟩ hp ⟨⟩ hr
    have bp : T ⊢ σ := Classical.choice <| (provable_iff_provableFn (L := ℒₒᵣ)).mpr hp
    have br : T ⊢ ~σ := Classical.choice <| (provable_iff_provableFn (L := ℒₒᵣ)).mpr hr
    exact inconsistent_of_provable_and_refutable bp br (consistent_of_sigmaOneSound T)
  have : Partrec (PFun.merge pr rf) := Partrec.mergep hpr hrf H
  have : Partrec d' :=
    this.comp (Primrec.to_comp $
      (Subformula.substs₁_primrec (L := ℒₒᵣ)).comp
        ((Subterm.Operator.const_primrec (L := ℒₒᵣ)).comp $
          (Subterm.Operator.numeral_primrec (L := ℒₒᵣ)).comp .encode) Primrec.id)
  exact this.of_eq <| by
    intro σ
    simp[Part.eq_some_iff, Partrec.merge_iff hpr hrf H, ←provable_iff_provableFn, diag]
    rcases A ([→ ⸢σ⸣].hom σ) with (hσ | bσ)
    · exact Or.inl hσ
    · exact Or.inr ⟨bσ, ⟨fun b => by
        rcases bσ with ⟨bσ⟩
        exact inconsistent_of_provable_and_refutable b bσ (consistent_of_sigmaOneSound T)⟩⟩

lemma diagRefutation_spec (σ : Subsentence ℒₒᵣ 1) :
  d σ = false ↔ T ⊢! [→ ⸢σ⸣].hom ρ := by
  have : T ⊢! [→ ⸢false⸣, ⸢σ⸣].hom (graph (diag T : Subsentence ℒₒᵣ 1 →. Bool)) ↔ diag T σ = false := by
    simpa[@eq_comm _ false] using representation (d_computable A) (x := σ) (y := false)
  simp[diagRefutation, ←Rew.hom_comp_app, Rew.substs_comp_substs, this]

theorem contrad : False := by
  have hd : d ρ = true  ↔ T ⊢! [→ ⸢ρ⸣].hom ρ := by simp[diag]
  have hρ : d ρ = false ↔ T ⊢! [→ ⸢ρ⸣].hom ρ := diagRefutation_spec A (diagRefutation T)
  rw[←hd, Bool.eq_false_iff] at hρ
  exact not_iff_self hρ

end FirstIncompleteness

attribute [-instance] Classical.propDecidable

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T]

theorem firstIncompleteness [SigmaOneSound T] [Theory.Computable T] [Theory.Computable T] : ¬Logic.System.Complete T :=
  FirstIncompleteness.contrad

lemma exists_undecidable_sentence [SigmaOneSound T] [Theory.Computable T] [Theory.Computable T] :
    ∃ σ : Sentence ℒₒᵣ, ¬T ⊢! σ ∧ ¬T ⊢! ~σ := by
  simpa[Logic.System.Complete, not_or] using firstIncompleteness (T := T)

end Arith

end FirstOrder

end LO
