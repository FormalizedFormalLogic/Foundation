module

public import Foundation.FirstOrder.Arithmetic.R0.Basic
public import Foundation.Vorspiel.Arithmetic
public import Foundation.Vorspiel.Computability

@[expose] public section
open Encodable Denumerable

namespace LO.FirstOrder.Arithmetic

open Mathlib Encodable Semiterm.Operator.GödelNumber

section

lemma term_primrec {k f} : (t : ArithmeticSemiterm ξ k) → Primrec (fun v : List.Vector ℕ k ↦ t.valm ℕ v.get f)
  |                         #x => by simpa using Primrec.vector_get.comp .id (.const _)
  |                         &x => by simpa using Primrec.const _
  | .func Language.Zero.zero _ => by simpa using Primrec.const 0
  |   .func Language.One.one _ => by simpa using Primrec.const 1
  |   .func Language.Add.add v => by
    simpa [Semiterm.val_func] using Primrec.nat_add.comp (term_primrec (v 0)) (term_primrec (v 1))
  |   .func Language.Mul.mul v => by
    simpa [Semiterm.val_func] using Primrec.nat_mul.comp (term_primrec (v 0)) (term_primrec (v 1))

lemma sigma1_re (ε : ξ → ℕ) {k} {φ : ArithmeticSemiformula ξ k} (hp : Hierarchy 𝚺 1 φ) :
    REPred fun v : List.Vector ℕ k ↦ Semiformula.Evalm ℕ v.get ε φ := by
  apply sigma₁_induction' hp
  case hVerum => simp;
  case hFalsum => simp
  case hEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.valm ℕ v.get ε = t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp (Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hNEQ =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.valm ℕ v.get ε = t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp <| Primrec.not.comp (Primrec.eq.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ decide (t₁.valm ℕ v.get ε < t₂.valm ℕ v.get ε), ?_, ?_⟩
    · apply Primrec.to_comp (Primrec.nat_lt.comp (term_primrec t₁) (term_primrec t₂)).decide
    · simp
  case hNLT =>
    intro n t₁ t₂
    refine ComputablePred.to_re <| ComputablePred.computable_iff.mpr
      <| ⟨fun v : List.Vector ℕ n ↦ !decide (t₁.valm ℕ v.get ε < t₂.valm ℕ v.get ε), ?_, ?_⟩
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
      Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) (t.valm ℕ v.get ε)
    have : Partrec g :=
      Partrec.nat_rec (term_primrec t).to_comp (Computable.const ())
        (Partrec.to₂ <| hf.comp (Primrec.to_comp <| Primrec.vector_cons.comp (Primrec.fst.comp .snd) .fst))
    refine REPred.iff.mpr ⟨_, this, ?_⟩
    funext v
    suffices ∀ k : ℕ, (∀ x < k, Semiformula.Evalm ℕ (x :> v.get) ε φ) ↔
      Part.Dom (Nat.rec (.some ()) (fun x ih ↦ ih.bind fun _ ↦ f (x ::ᵥ v)) k) by simpa [g] using this _
    intro k; induction k
    case zero => simp
    case succ k ih =>
      suffices
        (∀ x < k + 1, (Semiformula.Evalm ℕ (x :> v.get) ε) φ)
        ↔ (∀ x < k, (Semiformula.Evalm ℕ (x :> v.get) ε) φ) ∧ (f (k ::ᵥ v)).Dom by simpa [←ih]
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
    have : REPred fun vx : List.Vector ℕ n × ℕ ↦ Semiformula.Evalm ℕ (vx.2 :> vx.1.get) ε φ := by
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
    (∀⁰[“z. z < &0”] ∃⁰ “z. z ≠ 0” ⋏ ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1 + 1)) ![] (#0 :> #1 :> (&·.succ)) ▹ codeAux c)))

def code (c : Code k) : ArithmeticSemisentence (k + 1) := (Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k + 1)) ![] (#0 :> (#·.succ))) ▹ (codeAux c)

/-
section model

open LO.Arithmetic

variable {M : Type*} [ORingStructure M] [M ⊧ₘ* 𝗥₀]

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
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂;
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
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
  simp [code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def, Matrix.comp_vecCons']
  exact codeAux_uniq

end model
-/

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
    Semiformula.Evalfm ℕ (y :> v) (codeAux c) ↔ f (List.Vector.ofFn v) = Part.some y := by
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
      (∃ e' : Fin n → ℕ, (Semiformula.Evalfm ℕ (y :> e')) (codeAux c) ∧
        ∀ i, (Semiformula.Evalfm ℕ (e' i :> v)) (codeAux (d i)))
      ↔ (List.Vector.mOfFn (g · (List.Vector.ofFn v))).bind f = Part.some y by
        simp [codeAux]
        simpa [Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (List.Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (List.Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp [hg, hf]
    · intro h
      have : ∃ w, (∀ i, List.Vector.get w i ∈ g i (List.Vector.ofFn v)) ∧ y ∈ f w := by
        simpa using Part.eq_some_iff.mp h
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
      simpa [Part.eq_some_iff] using ⟨by simpa using hy, by intro z hz; exact Nat.ne_zero_of_lt (h z hz)⟩
    · intro h; simpa [pos_iff_ne_zero] using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : List.Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v) := by
  simpa [code, models_iff, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec' {k} (f : List.Vector ℕ k →. ℕ) : ArithmeticSemisentence (k + 1) :=
  code <| Classical.epsilon fun c ↦ ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v)

lemma codeOfPartrec'_spec {k} {f : List.Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    ℕ ⊧/(y :> v) (codeOfPartrec' f) ↔ y ∈ f (List.Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Semiformula.Evalbm ℕ (y :> v) (code c) ↔ y ∈ f (List.Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

open Classical

noncomputable def codeOfREPred (A : ℕ → Prop) : ArithmeticSemisentence 1 :=
  let f : ℕ →. Unit := fun a ↦ Part.assert (A a) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f (v.get 0)).map fun _ ↦ 0))/[‘0’, #0]

lemma codeOfREPred_spec {A : ℕ → Prop} (hp : REPred A) {x : ℕ} :
    ℕ ⊧/![x] (codeOfREPred A) ↔ A x := by
  let f : ℕ →. Unit := fun a ↦ Part.assert (A a) fun _ ↦ Part.some ()
  suffices ℕ ⊧/![x] ((codeOfPartrec' fun v ↦ Part.map (fun _ ↦ 0) (f (v.get 0)))/[‘0’, #0]) ↔ A x from this
  have : Partrec fun v : List.Vector ℕ 1 ↦ (f (v.get 0)).map fun _ ↦ 0 := by
    refine Partrec.map (Partrec.comp hp (Primrec.to_comp <| Primrec.vector_get.comp .id (.const 0))) (Computable.const 0).to₂
  simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
    using (codeOfPartrec'_spec (Nat.Partrec'.of_part this) (v := ![x]) (y := 0)).trans (by simp [f])

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- Weak representation of a r.e. predicate -/
theorem re_complete {A : ℕ → Prop} (hp : REPred A) {x : ℕ} :
    A x ↔ T ⊢ (codeOfREPred A)/[‘↑x’] := Iff.trans
  (by simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using (codeOfREPred_spec hp (x := x)).symm)
  (sigma_one_completeness_iff <| by simp [codeOfREPred, codeOfPartrec'])

end LO.FirstOrder.Arithmetic
