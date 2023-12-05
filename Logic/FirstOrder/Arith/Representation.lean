import Logic.FirstOrder.Arith.PAminus
import Logic.Vorspiel.Arith
import Logic.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

open Encodable

lemma Hierarchy.equal {t u : Subterm ℒₒᵣ μ n} : Hierarchy b s “!!t = !!u” := by
  simp[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]

scoped notation: max "⸢" a "⸣" => Subterm.Operator.godelNumber ℒₒᵣ a

@[simp] lemma godelNumber_encode_eq {α} [Primcodable α] (a : α) :
    (⸢encode a⸣ : Subterm.Const ℒₒᵣ) = ⸢a⸣ := by simp[Subterm.Operator.godelNumber]

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

section model

variable
  {M : Type} [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [Theory.Mod M (Theory.PAminus ℒₒᵣ)]

lemma codeAux_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Subformula.Val! M (z :> v) (codeAux c) → Subformula.Val! M (z' :> v) (codeAux c) → z = z' := by
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
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    intro w₁ hc₁ hd₁ w₂ hc₂ hd₂;
    have : w₁ = w₂ := funext fun i => ihd i (hd₁ i) (hd₂ i)
    rcases this with rfl
    exact ihc hc₁ hc₂
  case rfind c ih =>
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    intro h₁ hm₁ h₂ hm₂
    by_contra hz
    wlog h : z < z' with Hz
    case inr =>
      have : z' < z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz)
      exact Hz (k := k) c ih h₂ hm₂ h₁ hm₁ (Ne.symm hz) this
    have : ∃ x, x ≠ 0 ∧ (Subformula.Val! M (x :> z :> fun i => v i)) (codeAux c) := hm₂ z h
    rcases this with ⟨x, xz, hx⟩
    exact xz (ih hx h₁)

lemma code_uniq {k} {c : Code k} {v : Fin k → M} {z z' : M} :
    Subformula.PVal! M (z :> v) (code c) → Subformula.PVal! M (z' :> v) (code c) → z = z' := by
  simp[code, Subformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons']
  exact codeAux_uniq

end model

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
    Subformula.Val! ℕ (y :> v) (codeAux c) ↔ f (Vector.ofFn v) = Part.some y := by
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
    Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
  simpa[code, models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec {k} (f : Vector ℕ k →. ℕ) : Code k :=
  Classical.epsilon (fun c => ∀ y v, Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v))

lemma codeOfPartrec_spec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    Subformula.PVal! ℕ (y :> v) (code $ codeOfPartrec f) ↔ y ∈ f (Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

section representation

lemma provable_iff_mem_partrec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (T ⊢! (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)) ↔ y ∈ f (Vector.ofFn v) := by
  let σ : Sentence ℒₒᵣ := (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)
  have sigma : Hierarchy.Sigma 1 σ :=
    (Hierarchy.rew (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣) (code_sigma_one (codeOfPartrec f)))
  constructor
  · rintro ⟨b⟩
    have : Subformula.PVal! ℕ (y :> v) (code $ codeOfPartrec f) := by
      simpa[models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons'] using
        Arith.Sound.sound sigma ⟨b⟩
    exact (codeOfPartrec_spec hf).mp this
  · intro h
    exact ⟨PAminus.sigma_one_completeness sigma (by
      simp[models_iff, Subformula.eval_rew, Matrix.empty_eq,
        Function.comp, Matrix.comp_vecCons', codeOfPartrec_spec hf, h])⟩

variable (T)

lemma provable_iff_computable {k} {f : Vector ℕ k → ℕ}
    (hf : Nat.Partrec' (f : Vector ℕ k →. ℕ)) (v : Fin k → ℕ) :
    T ⊢! (Rew.substs $ ⸢f (Vector.ofFn v)⸣ :> (⸢v ·⸣)).hom (code $ codeOfPartrec f) :=
  (provable_iff_mem_partrec hf (T := T) (y := f (Vector.ofFn v)) (v := v)).mpr (by simp)

lemma provable_computable_code_uniq {k} {f : Vector ℕ k → ℕ}
    (hf : Nat.Partrec' (f : Vector ℕ k →. ℕ)) (v : Fin k → ℕ) :
    T ⊢! ∀' ((Rew.substs $ #0 :> (⸢v ·⸣)).hom (code $ codeOfPartrec f)
      ⟷ “#0 = !!(⸢f (Vector.ofFn v)⸣)”) :=
  Complete.consequence_iff_provable.mp (consequence_of _ _ (fun M _ _ _ _ _ => by
    haveI : Theory.Mod M (Theory.PAminus ℒₒᵣ) :=
      Theory.Mod.of_subtheory (T₁ := T) M (Semantics.ofSystemSubtheory _ _)
    have Hfv : Subformula.PVal! M (f (Vector.ofFn v) :> (v ·)) (code (codeOfPartrec f)) := by
      simpa[models_iff, Subformula.eval_substs, Matrix.comp_vecCons'] using
        consequence_iff'.mp (Sound.sound' (provable_iff_computable T hf v)) M
    simp[models_iff, Subformula.eval_substs, Matrix.comp_vecCons']
    intro x; constructor
    · intro H; exact code_uniq H Hfv
    · rintro rfl; simpa))

variable {α β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

noncomputable def graph (f : α →. σ) : Subsentence ℒₒᵣ 2 :=
  code (codeOfPartrec fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode)

noncomputable def graphTotal (f : α → σ) : Subsentence ℒₒᵣ 2 :=
  code (codeOfPartrec (fun x => Option.get! ((decode x.head).map (encode $ f ·)) : Vector ℕ 1 → ℕ))

noncomputable def graphTotal₂ (f : α → β → σ) : Subsentence ℒₒᵣ 3 :=
  code (codeOfPartrec (fun x =>
    Option.get! ((decode x.head).bind fun y => (decode x.tail.head).map fun z =>
       (encode $ f y z)) : Vector ℕ 2 → ℕ))

def toVecFun (f : α →. σ) : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode

theorem representation {f : α →. σ} (hf : Partrec f) {x y} :
    T ⊢! (graph f)/[⸢y⸣, ⸢x⸣] ↔ y ∈ f x := by
  let f' : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode
  have : Nat.Partrec' f' :=
    Nat.Partrec'.part_iff.mpr
      (Partrec.bind (Computable.ofOption $ Primrec.to_comp $ Primrec.decode.comp Primrec.vector_head)
      (Partrec.to₂ <| Partrec.map (hf.comp .snd) (Computable.encode.comp₂ .right)))
  simpa[Matrix.constant_eq_singleton] using
    provable_iff_mem_partrec this (y := encode y) (v := ![encode x])

theorem representation_computable {f : α → σ} (hf : Computable f) (a) :
    T ⊢! ∀' ((graphTotal f)/[#0, ⸢a⸣] ⟷ “#0 = !!⸢f a⸣”) := by
  let f' : Vector ℕ 1 → ℕ := fun x => Option.get! ((decode x.head).map (encode $ f ·))
  have : Nat.Partrec' (f' : Vector ℕ 1 →. ℕ) :=
    Nat.Partrec'.part_iff.mpr <| Computable.partrec <|
        (Primrec.option_get!).to_comp.comp <|
          Computable.option_map
            (Computable.decode.comp .vector_head) <|
              Computable.encode.comp₂ <| hf.comp₂ .right
  simpa[Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    provable_computable_code_uniq T this ![encode a]

theorem representation_computable₂ {f : α → β → σ} (hf : Computable₂ f) (a b) :
    T ⊢! ∀' ((graphTotal₂ f)/[#0, ⸢a⸣, ⸢b⸣] ⟷ “#0 = !!⸢f a b⸣”) := by
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
  simpa[Matrix.comp_vecCons' (fun x : ℕ => (⸢x⸣ : Subterm ℒₒᵣ Empty 1)),
    Matrix.constant_eq_singleton, graphTotal₂] using
      provable_computable_code_uniq T this ![encode a, encode b]

noncomputable def pred (p : α → Prop) : Subsentence ℒₒᵣ 1 :=
  (graph (fun a => Part.assert (p a) fun _ => Part.some ()))/[⸢()⸣, #0]

theorem pred_representation {p : α → Prop} (hp : RePred p) {x} :
    T ⊢! (pred p)/[⸢x⸣] ↔ p x := by
  simpa[pred, ←Rew.hom_comp_app, Rew.substs_comp_substs] using
    representation hp (T := T) (x := x) (y := ())

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [(k : ℕ) → Primcodable (L.func k)] [(k : ℕ) → Primcodable (L.rel k)]
  [UniformlyPrimcodable L.func] [UniformlyPrimcodable L.rel]

noncomputable def provableSentence (U : Theory L) : Subsentence ℒₒᵣ 1 := pred (U ⊢! ·)

theorem provableSentence_representation (U : Theory L) [DecidablePred U] [Theory.Computable U] {σ} :
    T ⊢! (provableSentence U)/[⸢σ⸣] ↔ U ⊢! σ := by
  simpa using pred_representation (T := T) (provable_RePred U) (x := σ)

end representation

end Arith

end FirstOrder

end LO
