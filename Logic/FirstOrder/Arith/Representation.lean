import Logic.FirstOrder.Arith.PeanoMinus
import Logic.Vorspiel.Arith
import Logic.FirstOrder.Computability.Calculus

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
    (∀[“z | z < &0”] ∃' “z | z ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))

def code (c : Code k) : Semisentence ℒₒᵣ (k + 1) := (Rew.bind ![] (#0 :> (#·.succ))).hom (codeAux c)

section model

open LO.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

private lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Semiformula.Evalfm M (z :> v) (codeAux c) → Semiformula.Evalfm M (z' :> v) (codeAux c) → z = z' := by
  induction c generalizing z z' <;> simp[code, codeAux]
  case zero => rintro rfl rfl; rfl
  case one  => rintro rfl rfl; rfl
  case add  => rintro rfl rfl; rfl
  case mul  => rintro rfl rfl; rfl
  case proj => rintro rfl rfl; rfl
  case equal i j =>
    by_cases hv : v i = v j <;> simp[hv]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case lt i j =>
    by_cases hv : v i < v j <;> simp[hv, -not_lt, ←not_lt]
    · rintro rfl rfl; rfl
    · rintro rfl rfl; rfl
  case comp m n c d ihc ihd =>
    simp[Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂;
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp[Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
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
  simp[code, Semiformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons']
  exact codeAux_uniq

end model

private lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy 𝚺 1 (codeAux c) := by
  induction c <;> simp[codeAux, Matrix.fun_eq_vec₂]
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
    simp[this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp[this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp[hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    by_cases hv : v i < v j <;> simp[hv, Nat.isLtNat, eq_comm]
    · simp [Nat.not_lt.mp hv]
  case add => simp[eq_comm]
  case mul => simp[eq_comm]
  case proj => simp[eq_comm]
  case comp c d f g _ _ ihf ihg =>
    simp[Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
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
    simp[Semiformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons', ihf, Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩; simp[Part.eq_some_iff]
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

namespace FirstIncompleteness

attribute [-instance]
  LO.FirstOrder.Semiterm.encodable
  LO.FirstOrder.Semiformula.encodable

open Mathlib Encodable Semiterm.Operator.GoedelNumber

variable {T : Theory ℒₒᵣ} [𝐄𝐐 ≼ T] [𝐏𝐀⁻ ≼ T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

open LO.Arith

lemma provable_iff_mem_partrec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (T ⊢! (Rew.substs $ ‘↑y’ :> fun i ↦ ‘↑(v i)’).hom (codeOfPartrec' f)) ↔ y ∈ f (Vector.ofFn v) := by
  let σ : Sentence ℒₒᵣ := (Rew.substs $ ‘↑y’ :> fun i => ‘↑(v i)’).hom (codeOfPartrec' f)
  have sigma : Hierarchy 𝚺 1 σ :=
    (Hierarchy.rew (Rew.substs $ ‘↑y’ :> fun i => ‘↑(v i)’) (code_sigma_one _))
  constructor
  · rintro ⟨b⟩
    have : Semiformula.Evalbm ℕ (y :> v) (codeOfPartrec' f) := by
      simpa [σ, models_iff, Semiformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons'] using
        Arith.SoundOn.sound sigma ⟨b⟩
    exact (codeOfPartrec'_spec hf).mp this
  · intro h
    exact Arith.sigma_one_completeness sigma (by
      simp [models_iff, Semiformula.eval_rew, Matrix.empty_eq,
        Function.comp, Matrix.comp_vecCons', codeOfPartrec'_spec hf, h])

variable (T)

lemma provable_iff_computable {k} {f : Vector ℕ k → ℕ}
    (hf : Nat.Partrec' (f : Vector ℕ k →. ℕ)) (v : Fin k → ℕ) :
    T ⊢! (Rew.substs $ ‘↑(f (Vector.ofFn v))’ :> fun x ↦ ‘↑(v x)’).hom (codeOfPartrec' f) :=
  (provable_iff_mem_partrec hf (T := T) (y := f (Vector.ofFn v)) (v := v)).mpr (by simp)

lemma provable_computable_code_uniq {k} {f : Vector ℕ k → ℕ}
    (hf : Nat.Partrec' (f : Vector ℕ k →. ℕ)) (v : Fin k → ℕ) :
    T ⊢! ∀' ((Rew.substs $ #0 :> fun x ↦ ‘↑(v x)’).hom (codeOfPartrec' f)
      ⟷ “x | x = ↑(f (Vector.ofFn v))”) :=
  complete (oRing_consequence_of _ _ (fun M _ _ ↦ by
    haveI : M ⊧ₘ* 𝐏𝐀⁻ :=
      ModelsTheory.of_provably_subtheory M 𝐏𝐀⁻ T inferInstance (by assumption)
    have Hfv : Semiformula.Evalbm M (f (Vector.ofFn v) :> (v ·)) ((codeOfPartrec' f)) := by
      simpa [Arith.numeral_eq_natCast, models_iff, Semiformula.eval_substs, Matrix.comp_vecCons'] using
        consequence_iff'.mp (sound₀! (provable_iff_computable T hf v)) M
    simp [Arith.numeral_eq_natCast, models_iff, Semiformula.eval_substs, Matrix.comp_vecCons']
    intro x; constructor
    · intro H; exact code_uniq H Hfv
    · rintro rfl; simpa))

/-- This instance is scoped since we will define canonical Gödel numbering when formalizing G2.  -/
scoped instance {α} [Primcodable α] : Semiterm.Operator.GoedelNumber ℒₒᵣ α :=
  Semiterm.Operator.GoedelNumber.ofEncodable

lemma goedelNumber_def {α} [Primcodable α] (a : α) :
  goedelNumber a = Semiterm.Operator.encode ℒₒᵣ a := rfl

lemma goedelNumber'_def {α} [Primcodable α] (a : α) :
  (⌜a⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.encode ℒₒᵣ a := rfl

@[simp] lemma encode_encode_eq {α} [Primcodable α] (a : α) :
    (goedelNumber (encode a) : Semiterm.Const ℒₒᵣ) = goedelNumber a := by simp [Semiterm.Operator.encode, goedelNumber_def]

variable {α β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

noncomputable def graph (f : α →. σ) : Semisentence ℒₒᵣ 2 :=
  codeOfPartrec' fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode

noncomputable def graphTotal (f : α → σ) : Semisentence ℒₒᵣ 2 :=
  codeOfPartrec' (fun x => Option.get! ((decode x.head).map (encode $ f ·)) : Vector ℕ 1 → ℕ)

noncomputable def graphTotal₂ (f : α → β → σ) : Semisentence ℒₒᵣ 3 :=
  codeOfPartrec' (fun x =>
    Option.get! ((decode x.head).bind fun y => (decode x.tail.head).map fun z =>
       (encode $ f y z)) : Vector ℕ 2 → ℕ)

def toVecFun (f : α →. σ) : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode

theorem representation {f : α →. σ} (hf : Partrec f) {x y} :
    T ⊢! (graph f)/[⌜y⌝, ⌜x⌝] ↔ y ∈ f x := by
  let f' : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode
  have : Nat.Partrec' f' :=
    Nat.Partrec'.part_iff.mpr
      (Partrec.bind (Computable.ofOption $ Primrec.to_comp $ Primrec.decode.comp Primrec.vector_head)
      (Partrec.to₂ <| Partrec.map (hf.comp .snd) (Computable.encode.comp₂ .right)))
  simpa [f', Matrix.constant_eq_singleton] using
    provable_iff_mem_partrec this (y := encode y) (v := ![encode x])

theorem representation_computable {f : α → σ} (hf : Computable f) (a) :
    T ⊢! ∀' ((graphTotal f)/[#0, ⌜a⌝] ⟷ “x | x = !!⌜f a⌝”) := by
  let f' : Vector ℕ 1 → ℕ := fun x => Option.get! ((decode x.head).map (encode $ f ·))
  have : Nat.Partrec' (f' : Vector ℕ 1 →. ℕ) :=
    Nat.Partrec'.part_iff.mpr <| Computable.partrec <|
        (Primrec.option_get!).to_comp.comp <|
          Computable.option_map
            (Computable.decode.comp .vector_head) <|
              Computable.encode.comp₂ <| hf.comp₂ .right
  simpa [f', Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    provable_computable_code_uniq T this ![encode a]

theorem representation_computable₂ {f : α → β → σ} (hf : Computable₂ f) (a b) :
    T ⊢! ∀' ((graphTotal₂ f)/[#0, ⌜a⌝, ⌜b⌝] ⟷ “x | x = !!⌜f a b⌝”) := by
  let f' : Vector ℕ 2 → ℕ := fun v =>
    Option.get! ((decode v.head).bind fun x => (decode v.tail.head).map fun y => (encode $ f x y))
  have : Nat.Partrec' (f' : Vector ℕ 2 →. ℕ) :=
    Nat.Partrec'.part_iff.mpr <| Computable.partrec <|
        (Primrec.option_get!).to_comp.comp <|
          Computable.option_bind
            (Computable.decode.comp .vector_head) <|
              Computable.option_map
                (Computable.decode.comp $ Computable.vector_head.comp $ Computable.vector_tail.comp .fst) <|
                  Computable.encode.comp₂ <| hf.comp₂ (Computable.snd.comp₂ .left) .right
  simpa [f', Matrix.comp_vecCons' (fun x : ℕ => (‘↑x’ : Semiterm ℒₒᵣ Empty 1)),
    Matrix.constant_eq_singleton, graphTotal₂] using
      provable_computable_code_uniq T this ![encode a, encode b]

noncomputable def pred (p : α → Prop) : Semisentence ℒₒᵣ 1 :=
  (graph (fun a => Part.assert (p a) fun _ => Part.some ()))/[⌜()⌝, #0]

theorem pred_representation {p : α → Prop} (hp : RePred p) {x} :
    T ⊢! (pred p)/[⌜x⌝] ↔ p x := by
  simpa [goedelNumber'_def, pred, ←Rew.hom_comp_app, Rew.substs_comp_substs] using
    representation hp (T := T) (x := x) (y := ())

end FirstIncompleteness

end Arith

end FirstOrder

end LO
