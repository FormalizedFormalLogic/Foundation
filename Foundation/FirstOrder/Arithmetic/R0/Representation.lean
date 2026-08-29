module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.Arithmetic.R0.Basic
public import Foundation.Vorspiel.Arithmetic
public import Foundation.Vorspiel.Computability

@[expose] public section
open Encodable Denumerable

namespace LO.FirstOrder.Arithmetic

open Mathlib Encodable Semiterm.Operator.GödelNumber

section

lemma term_primrec {k f} : (t : ArithmeticSemiterm ξ k) → Primrec (fun v : List.Vector ℕ k ↦ t.val v.get f)
  |                         #x => by simpa using Primrec.vector_get.comp .id (.const _)
  |                         &x => by simpa using Primrec.const _
  | .func Language.Zero.zero _ => by simpa using Primrec.const 0
  |   .func Language.One.one _ => by simpa using Primrec.const 1
  |   .func Language.Add.add v => by
    simpa [Semiterm.val_func] using Primrec.nat_add.comp (term_primrec (v 0)) (term_primrec (v 1))
  |   .func Language.Mul.mul v => by
    simpa [Semiterm.val_func] using Primrec.nat_mul.comp (term_primrec (v 0)) (term_primrec (v 1))

lemma sigma1_re (ε : ξ → ℕ) {k} {φ : ArithmeticSemiformula ξ k} (hp : Hierarchy 𝚺 1 φ) :
    REPred fun v : List.Vector ℕ k ↦ φ.Eval v.get ε := by
  apply sigma₁_induction' hp
  case hVerum => simp;
  case hFalsum => simp
  case hEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.val v.get ε = t₂.val v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp (Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hNEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.val v.get ε = t₂.val v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.not.comp (Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.val v.get ε < t₂.val v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp (Primrec.nat_lt.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hNLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.val v.get ε < t₂.val v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.not.comp (Primrec.nat_lt.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hAnd =>
    intro n φ ψ _ _ ihp ihq
    exact REPred.of_eq (ihp.and ihq) fun v ↦ by simp
  case hOr =>
    intro n φ ψ _ _ ihp ihq
    exact REPred.of_eq (ihp.or ihq) fun v ↦ by simp
  case hBall =>
    intro n t φ _ ih
    rcases REPred.iff'.mp ih with ⟨f, hf, H⟩
    let g : List.Vector ℕ n →. Unit := fun v ↦
      Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) (t.val v.get ε)
    have : Partrec g :=
      Partrec.nat_rec (term_primrec t).to_comp (Computable.const ())
        (Partrec.to₂ <| hf.comp (Primrec.to_comp <| Primrec.vector_cons.comp (Primrec.fst.comp .snd) .fst))
    refine REPred.iff.mpr ⟨_, this, ?_⟩
    funext v
    suffices ∀ k : ℕ, (∀ x < k, φ.Eval (x :> v.get) ε) ↔
      Part.Dom (Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) k) by simpa [g] using this _
    intro k; induction k
    case zero => simp
    case succ k ih =>
      suffices
        (∀ x < k + 1, φ.Eval (x :> v.get) ε)
        ↔ (∀ x < k, φ.Eval (x :> v.get) ε) ∧ (f (k ::ᵥ v)).Dom by simpa [←ih]
      constructor
      · intro h
        exact ⟨fun x hx ↦ h x (lt_trans hx (by simp)),
          (H (k ::ᵥ v)).mp (by simpa [List.Vector.cons_get] using h k (by simp))⟩
      · rintro ⟨hs, hd⟩ x hx
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hx) with (hx | rfl)
        · exact hs x hx
        · simpa [List.Vector.cons_get] using (H (x ::ᵥ v)).mpr hd
  case hExs =>
    intro n φ _ ih
    rcases REPred.iff'.mp ih with ⟨f, _, _⟩
    have : REPred fun vx : List.Vector ℕ n × ℕ ↦ φ.Eval (vx.2 :> vx.1.get) ε := by
      simpa [List.Vector.cons_get] using ih.comp (Primrec.to_comp <| Primrec.vector_cons.comp .snd .fst)
    simpa using this.projection

end

open Nat.ArithPart₁

def codeAux {k : ℕ} : Nat.ArithPart₁.Code k → ArithmeticFormula (Fin (k + 1))
  |        Code.zero _ => “&0 = 0”
  |         Code.one _ => “&0 = 1”
  |       Code.add i j => “&0 = &i.succ + &j.succ”
  |       Code.mul i j => “&0 = &i.succ * &j.succ”
  |     Code.equal i j => “(&i.succ = &j.succ ∧ &0 = 1) ∨ (&i.succ ≠ &j.succ ∧ &0 = 0)”
  |        Code.lt i j => “(&i.succ < &j.succ ∧ &0 = 1) ∨ (&i.succ ≮ &j.succ ∧ &0 = 0)”
  |        Code.proj i => “&0 = !!&i.succ”
  | @Code.comp _ n c d =>
    exsClosure ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (n + 1)) ![] (&0 :> (#·)) ▹ (codeAux c)) ⋏
      Matrix.conj fun i ↦ Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1)) ![] (#i :> (&·.succ)) ▹ codeAux (d i))
  |       Code.rfind c =>
    (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1 + 1)) ![] (‘0’ :> &0 :> (&·.succ)) ▹ codeAux c) ⋏
    (∀¹[“z. z < &0”] ∃¹ “z. z ≠ 0” ⋏ ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1 + 1)) ![] (#0 :> #1 :> (&·.succ)) ▹ codeAux c)))

def code (c : Code k) : ArithmeticSemisentence (k + 1) := (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1)) ![] (#0 :> (#·.succ))) ▹ (codeAux c)

section model

open PeanoMinus

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

-- Each case below rewrites hypotheses with `simp [...] at h h'` and then destructures the
-- normalized hypotheses; the flexible-tactic linter cannot see that the later tactics only
-- depend on the (already fully simplified) shape of `h`/`h'`, not on the exact simp set used.
set_option linter.flexible false in
private lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    (codeAux c).Evalf (M := M) (z :> v) → (codeAux c).Evalf (M := M) (z' :> v) → z = z' := by
  induction c generalizing z z' with
  | zero _ => intro h h'; simp [codeAux] at h h'; rw [h, h']
  | one _ => intro h h'; simp [codeAux] at h h'; rw [h, h']
  | add i j => intro h h'; simp [codeAux] at h h'; rw [h, h']
  | mul i j => intro h h'; simp [codeAux] at h h'; rw [h, h']
  | proj i => intro h h'; simp [codeAux] at h h'; rw [h, h']
  | equal i j =>
    intro h h'
    by_cases hv : v i = v j <;> simp [codeAux, hv] at h h' <;> rw [h, h']
  | lt i j =>
    intro h h'
    by_cases hv : v i < v j <;> simp [codeAux, hv] at h h' <;> rw [h, h']
  | comp c d ihc ihd =>
    intro h h'
    simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
      Matrix.comp_vecCons'] at h h'
    obtain ⟨w₁, hc₁, hd₁⟩ := h
    obtain ⟨w₂, hc₂, hd₂⟩ := h'
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  | rfind c ih =>
    intro H₁ H₂
    simp [codeAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq,
      Matrix.comp_vecCons'] at H₁ H₂
    obtain ⟨h₁, hm₁⟩ := H₁
    obtain ⟨h₂, hm₂⟩ := H₂
    by_contra hz
    wlog h : z < z' with Hz
    case inr =>
      have : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hz) this
    have : ∃ x, x ≠ 0 ∧ (codeAux c).Evalf (M := M) (x :> z :> fun i => v i) := hm₂ z h
    rcases this with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

-- `simp ... at h h'` normalizes the two hypotheses to the `codeAux_uniq` shape before
-- `exact`; the flexible-tactic linter cannot see that `exact` only depends on that final shape.
set_option linter.flexible false in
lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    (code c).Evalb (M := M) (z :> v) → (code c).Evalb (M := M) (z' :> v) → z = z' := by
  intro h h'
  simp [code, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq] at h h'
  exact codeAux_uniq h h'

end model

private lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (codeAux c) := by
  induction c
  case zero => simp [codeAux]
  case one => simp [codeAux]
  case add => simp [codeAux]
  case mul => simp [codeAux]
  case lt => simp [codeAux, Matrix.fun_eq_vec_two]
  case equal => simp [codeAux, Matrix.fun_eq_vec_two]
  case proj => simp [codeAux]
  case comp c d ihc ihg =>
    exact Hierarchy.exsClosure (by simp [ihc, ihg])
  case rfind k c ih => simp [codeAux, Matrix.fun_eq_vec_two]; simp [ih]

@[simp] lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_one c)

@[simp] lemma natCast_nat' (n : ℕ) : Nat.cast n = n := by rfl

private lemma models_codeAux {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    (codeAux c).Evalf (y :> v) ↔ f (List.Vector.ofFn v) = Part.some y := by
  induction hc generalizing y
  case zero =>
    have : (0 : Part ℕ) = Part.some 0 := rfl
    simp [codeAux, this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp [codeAux, this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp [codeAux, hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    simp [codeAux]
    by_cases hv : v i < v j <;> simp [hv, Nat.isLtNat, eq_comm, Nat.not_lt.mp]
  case add => simp [codeAux, eq_comm]
  case mul => simp [codeAux, eq_comm]
  case proj => simp [codeAux, eq_comm]
  case comp m n c d f g _ _ ihf ihg =>
    suffices
      (∃ e' : Fin n → ℕ, (codeAux c).Evalf (y :> e') ∧ ∀ i, (codeAux (d i)).Evalf (e' i :> v))
      ↔ (List.Vector.mOfFn (g · (List.Vector.ofFn v))).bind f = Part.some y by
        simp [codeAux]
        simpa [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (List.Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (List.Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp only [hg, Vector.mOfFn_part_some]
      exact (Part.bind_some (List.Vector.ofFn e) f).trans hf
    · intro h
      have : ∃ w, (∀ i, List.Vector.get w i ∈ g i (List.Vector.ofFn v)) ∧ y ∈ f w := by
        obtain ⟨w, hw, hy⟩ := Part.mem_bind_iff.mp (Part.eq_some_iff.mp h)
        exact ⟨w, Part.mem_vector_mOfFn.mp hw, hy⟩
      rcases this with ⟨w, hw, hy⟩
      exact ⟨w.get, (ihf y w.get).mpr (by simpa [Part.eq_some_iff] using hy),
        fun i ↦ (ihg i (w.get i) v).mpr (by simpa [Part.eq_some_iff] using hw i)⟩
  case rfind c f _ ihf =>
    suffices
      (f (y ::ᵥ List.Vector.ofFn v) = 0 ∧ ∀ x < y, 0 < f (x ::ᵥ List.Vector.ofFn v))
      ↔ (Nat.rfind fun n ↦ Part.some (decide (f (n ::ᵥ List.Vector.ofFn v) = 0))) = Part.some y by
      simp [codeAux]
      simpa [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons', ihf, List.Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩
      exact Part.eq_some_iff.mpr (Nat.mem_rfind.mpr ⟨by simp [hy], fun hz => by simp [Nat.ne_zero_of_lt (h _ hz)]⟩)
    · intro h; simpa [pos_iff_ne_zero] using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    (code c).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v) := by
  simpa [code, models_iff, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec' {k} (f : List.Vector ℕ k →. ℕ) : ArithmeticSemisentence (k + 1) :=
  code <| Classical.epsilon fun c ↦ ∀ y v, (code c).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v)

lemma codeOfPartrec'_spec {k} {f : List.Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (codeOfPartrec' f).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v) := by
  have : ∃ c, ∀ y v, (code c).Evalb (y :> v) ↔ y ∈ f (List.Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

open Classical

noncomputable def codeOfREPred (p : ℕ → Prop) : ArithmeticSemisentence 1 :=
  let f : ℕ →. Unit := fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f (v.get 0)).map fun _ ↦ 0))/[‘0’, #0]

lemma codeOfREPred_spec {p : ℕ → Prop} (hp : REPred p) {x : ℕ} :
    (codeOfREPred p).Evalb ![x] ↔ p x := by
  let f : ℕ →. Unit := fun a ↦ Part.assert (p a) fun _ ↦ Part.some ()
  suffices (codeOfPartrec' fun v ↦ Part.map (fun _ ↦ 0) (f (v.get 0)))/[‘0’, #0].Evalb (![x]) ↔ p x from this
  have : Partrec fun v : List.Vector ℕ 1 ↦ (f (v.get 0)).map fun _ ↦ 0 := by
    refine Partrec.map (Partrec.comp hp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const 0))) (Computable.const 0).to₂
  simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
    using (codeOfPartrec'_spec (Nat.Partrec'.of_part this) (v := ![x]) (y := 0)).trans (by simp [f])

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- Weak representation of a r.e. predicate -/
theorem rePred_weak_representation {p : ℕ → Prop} (hp : REPred p) {x : ℕ} :
    p x ↔ T ⊢ (codeOfREPred p)/[x] := Iff.trans
  (by simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using (codeOfREPred_spec hp (x := x)).symm)
  (sigma_one_completeness_iff <| by simp [codeOfREPred, codeOfPartrec'])

theorem rePred_iff_sigma1 {p : ℕ → Prop} : REPred p ↔ 𝚺₁-Predicate p := by
  constructor
  · intro h
    refine ⟨.mkSigma (codeOfREPred p) (by simp [codeOfREPred, codeOfPartrec']), ?_⟩
    intro v
    simpa [←Matrix.fun_eq_vec_one] using codeOfREPred_spec h (x := v 0)
  · rintro ⟨φ, hφ⟩
    have : REPred fun x ↦ (Semiformula.Eval (x ::ᵥ List.Vector.nil).get id) _ :=
      (sigma1_re id (φ.sigma_prop)).comp
        (Primrec.to_comp <| Primrec.vector_cons.comp .id <| .const _)
    exact this.of_eq <| by intro x; simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![x]

theorem computablePred_iff_delta1 {p : ℕ → Prop} : ComputablePred p ↔ 𝚫₁-Predicate p := by
  classical
  constructor
  · intro hp
    change 𝚫₁.Definable (fun v : Fin 1 → ℕ ↦ p (v 0))
    rw [HierarchySymbol.Definable.delta_iff_sigma_and_pi]
    rcases ComputablePred.computable_iff_re_compl_re'.mp hp with ⟨hp, hnp⟩
    exact ⟨(rePred_iff_sigma1.mp hnp).notSigma.of_iff (by intro v; simp), rePred_iff_sigma1.mp hp⟩
  · intro h
    change 𝚫₁.Definable (fun v : Fin 1 → ℕ ↦ p (v 0)) at h
    rw [HierarchySymbol.Definable.delta_iff_sigma_and_pi] at h
    exact ComputablePred.computable_iff_re_compl_re'.mpr
      ⟨rePred_iff_sigma1.mpr h.2, rePred_iff_sigma1.mpr h.1.notPi⟩

theorem computable_iff_sigma1 {f : ℕ → ℕ} : Computable f ↔ 𝚺₁-Function₁ f := by
  constructor
  · intro hf
    let F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (f (v.get 0))
    have hF : Partrec F := by
      change Partrec fun v : List.Vector ℕ 1 ↦ Part.some (f (v.get 0))
      exact hf.comp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const (0 : Fin 1)))
    refine ⟨.mkSigma (codeOfPartrec' F) (by simp [codeOfPartrec']), ?_⟩
    intro v
    simpa [F, ←Matrix.fun_eq_vec_two]
      using codeOfPartrec'_spec (Nat.Partrec'.of_part hF) (y := v 0) (v := ![v 1])
  · rintro ⟨φ, hφ⟩
    have hRe : REPred fun p : ℕ × ℕ ↦
        φ.val.Eval (p.2 ::ᵥ p.1 ::ᵥ List.Vector.nil : List.Vector ℕ 2).get id :=
      (sigma1_re id φ.sigma_prop).comp
        (Primrec.to_comp <| Primrec.vector_cons.comp .snd
          (Primrec.vector_cons.comp .fst (.const List.Vector.nil)))
    exact ComputablePred.of_graph_rePred <| hRe.of_eq <| by
      intro p
      simpa [List.Vector.cons_get] using hφ ![p.2, p.1]

theorem computable₂_iff_sigma1 {f : ℕ → ℕ → ℕ} : Computable₂ f ↔ 𝚺₁-Function₂ f := by
  constructor
  · intro hf
    let F : List.Vector ℕ 2 →. ℕ := fun v ↦ Part.some (f (v.get 0) (v.get 1))
    have hF : Partrec F := by
      have hArg : Computable fun v : List.Vector ℕ 2 ↦ (v.get 0, v.get 1) :=
        (Primrec.vector_get.comp .id (.const (0 : Fin 2))).to_comp.pair
          (Primrec.vector_get.comp .id (.const (1 : Fin 2))).to_comp
      have hf' : Computable fun p : ℕ × ℕ ↦ f p.1 p.2 := hf
      change Partrec fun v : List.Vector ℕ 2 ↦ Part.some (f (v.get 0) (v.get 1))
      exact hf'.comp hArg
    refine ⟨.mkSigma (codeOfPartrec' F) (by simp [codeOfPartrec']), ?_⟩
    intro v
    simpa [F, ←Matrix.fun_eq_vec_three]
      using codeOfPartrec'_spec (Nat.Partrec'.of_part hF) (y := v 0) (v := ![v 1, v 2])
  · rintro ⟨φ, hφ⟩
    have hRe : REPred fun p : (ℕ × ℕ) × ℕ ↦
        φ.val.Eval
          (p.2 ::ᵥ p.1.1 ::ᵥ p.1.2 ::ᵥ List.Vector.nil : List.Vector ℕ 3).get id :=
      (sigma1_re id φ.sigma_prop).comp
        (Primrec.to_comp <| Primrec.vector_cons.comp .snd
          (Primrec.vector_cons.comp (Primrec.fst.comp .fst)
            (Primrec.vector_cons.comp (Primrec.snd.comp .fst) (.const List.Vector.nil))))
    exact ComputablePred.of_graph_rePred <| hRe.of_eq <| by
      intro p
      simpa [List.Vector.cons_get] using hφ ![p.2, p.1.1, p.1.2]

end LO.FirstOrder.Arithmetic
