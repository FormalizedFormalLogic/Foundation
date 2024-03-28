import Logic.FirstOrder.Arith.Model

namespace LO.FirstOrder

namespace Arith

variable {L : Language} [L.ORing] (T : Theory L) [𝐄𝐪 ≾ T] [L.Exp]

instance : Language.ORing ℒₒᵣ(exp) := Language.ORing.mk

lemma consequence_of_exp (σ : Sentence L)
  (H : ∀ (M : Type u)
         [Zero M] [One M] [Add M] [Mul M] [Exp M] [LT M]
         [Structure L M]
         [Structure.ORing L M]
         [Structure.Exp L M]
         [Theory.Mod M T],
         M ⊧ₘ σ) :
    T ⊨ σ := consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Theory.Mod (Structure.Model L M) T :=
    ⟨((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)⟩
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
    (H (Structure.Model L M))

namespace Theory

variable (L)

notation "𝐈open(exp)" => IOpen ℒₒᵣ(exp)

notation "𝐈𝚫₀(exp)" => ISigma ℒₒᵣ(exp) 0

inductive Exponential : Theory L
  | zero : Exponential “exp 0 = 1”
  | succ : Exponential “∀ exp (#0 + 1) = 2 * exp #0”

notation "𝐄𝐗𝐏" => Exponential ℒₒᵣ(exp)

abbrev ElementaryArithmetic : Theory L := Semiformula.lMap Language.oringEmb '' 𝐏𝐀⁻ + Exponential L + ISigma L 0

notation "𝐄𝐀" => ElementaryArithmetic ℒₒᵣ(exp)

end Theory

section model

variable (M : Type*) [Zero M] [One M] [Add M] [Exp M] [Mul M] [LT M]

instance standardModelExp : Structure ℒₒᵣ(exp) M where
  func := fun _ f =>
    match f with
    | Language.ORingExp.Func.zero => fun _ => 0
    | Language.ORingExp.Func.one  => fun _ => 1
    | Language.ORingExp.Func.exp  => fun v => Exp.exp (v 0)
    | Language.ORingExp.Func.add  => fun v => v 0 + v 1
    | Language.ORingExp.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | Language.ORingExp.Rel.eq => fun v => v 0 = v 1
    | Language.ORingExp.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ(exp) M :=
  ⟨by intro a b; simp[standardModelExp, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel]⟩

instance : Structure.Zero ℒₒᵣ(exp) M := ⟨rfl⟩

instance : Structure.One ℒₒᵣ(exp) M := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ(exp) M := ⟨fun _ _ => rfl⟩

instance : Structure.Mul ℒₒᵣ(exp) M := ⟨fun _ _ => rfl⟩

instance : Structure.Exp ℒₒᵣ(exp) M := ⟨fun _ => rfl⟩

instance : Structure.Eq ℒₒᵣ(exp) M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ(exp) M := ⟨fun _ _ => iff_of_eq rfl⟩

lemma standardModelExp_unique' (s : Structure ℒₒᵣ(exp) M)
    (hZero : Structure.Zero ℒₒᵣ(exp) M) (hOne : Structure.One ℒₒᵣ(exp) M)
    (hAdd : Structure.Add ℒₒᵣ(exp) M) (hMul : Structure.Mul ℒₒᵣ(exp) M) (hExp : Structure.Exp ℒₒᵣ(exp) M)
    (hEq : Structure.Eq ℒₒᵣ(exp) M) (hLT : Structure.LT ℒₒᵣ(exp) M) : s = standardModelExp M := Structure.ext _ _
  (funext₃ fun k f _ =>
    match k, f with
    | _, Language.Zero.zero => by simp[Matrix.empty_eq]
    | _, Language.One.one   => by simp[Matrix.empty_eq]
    | _, Language.Add.add   => by simp
    | _, Language.Mul.mul   => by simp
    | _, Language.Exp.exp   => by simp)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.LT.lt => by simp)

lemma standardModelExp_unique (s : Structure ℒₒᵣ(exp) M)
    [hZero : Structure.Zero ℒₒᵣ(exp) M] [hOne : Structure.One ℒₒᵣ(exp) M]
    [hAdd : Structure.Add ℒₒᵣ(exp) M] [hMul : Structure.Mul ℒₒᵣ(exp) M] [hExp : Structure.Exp ℒₒᵣ(exp) M]
    [hEq : Structure.Eq ℒₒᵣ(exp) M] [hLT : Structure.LT ℒₒᵣ(exp) M] : s = standardModelExp M :=
  standardModelExp_unique' M s hZero hOne hAdd hMul hExp hEq hLT

namespace Standard

lemma modelsTheoryExponential : ℕ ⊧ₘ* 𝐄𝐗𝐏 := by
  intro σ h
  rcases h <;> simp[models_def, Structure.Exp.exp, Nat.exp_succ]

lemma modelsSuccInd_exp (p : Semiformula ℒₒᵣ(exp) ℕ 1) : ℕ ⊧ₘ (∀ᶠ* succInd p) := by
  simp [Empty.eq_elim, succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiformula.eval_substs, Semiformula.eval_rew_q Rew.toS, Function.comp]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsTheoryElementaryArithmetic : ℕ ⊧ₘ* 𝐄𝐀 := by
  simp [Theory.ElementaryArithmetic, Theory.add_def, Theory.ISigma, Theory.IndScheme]
  exact ⟨⟨by intro σ hσ; simpa [models_iff] using modelsTheoryPAminus hσ, modelsTheoryExponential⟩,
    by rintro σ p _ rfl; exact modelsSuccInd_exp p⟩

end Standard

end model

noncomputable section

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [Exp M] [LT M] [𝐄𝐀.Mod M]

open Language

namespace Model

instance : 𝐏𝐀⁻.Mod M :=
  haveI : Theory.Mod M (Semiformula.lMap Language.oringEmb '' 𝐏𝐀⁻ : Theory ℒₒᵣ(exp)) :=
    Theory.Mod.of_add_left_left M (Semiformula.lMap Language.oringEmb '' 𝐏𝐀⁻) 𝐄𝐗𝐏 𝐈𝚫₀(exp)
  ⟨by intro σ hσ;
      simpa [models_iff] using
        @Theory.Mod.models ℒₒᵣ(exp) M _ _ _ this _ (Set.mem_image_of_mem (Semiformula.lMap Language.oringEmb) hσ)⟩

instance : 𝐄𝐗𝐏.Mod M := Theory.Mod.of_add_left_right M (Semiformula.lMap Language.oringEmb '' 𝐏𝐀⁻) 𝐄𝐗𝐏 𝐈𝚫₀(exp)

instance : 𝐈𝚫₀(exp).Mod M := Theory.Mod.of_add_right M (Semiformula.lMap Language.oringEmb '' 𝐏𝐀⁻ + 𝐄𝐗𝐏) 𝐈𝚫₀(exp)

lemma ISigma₀_subset_IDelta₀Exp : (𝐈𝚺₀ : Theory ℒₒᵣ(exp)) ⊆ 𝐈𝚫₀(exp) :=
  Theory.coe_IHierarchy_subset_IHierarchy

instance : 𝐈𝚺₀.Mod M := ⟨by
  intro σ hσ
  have : (𝐈𝚺₀ : Theory ℒₒᵣ(exp)) ⊆ 𝐈𝚫₀(exp) := Theory.coe_IHierarchy_subset_IHierarchy
  have : M ⊧ₘ (σ : Sentence ℒₒᵣ(exp)) :=
    Theory.Mod.models M (show (σ : Sentence ℒₒᵣ(exp)) ∈ 𝐈𝚫₀(exp) from this (Set.mem_image_of_mem _ hσ))
  simpa [models_iff] using this⟩

end Model

end

end Arith

end LO.FirstOrder
