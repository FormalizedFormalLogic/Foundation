import Arithmetization.Lemmata
import Arithmetization.Vorspiel.Graph
import Logic.FirstOrder.Arith.StrictHierarchy
import Aesop

lemma Matrix.succ_pred {n : ℕ} (P : Fin n.succ → Prop) : (∀ i, P i) ↔ (P 0 ∧ ∀ i : Fin n, P i.succ) :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, fun h ↦ Fin.cases h.1 h.2⟩

namespace LO.FirstOrder

namespace Arith

section

variable {L : Language} [L.Eq] [L.LT] (ξ : Type*) [DecidableEq ξ]

abbrev HClassInWithEq (Γ s) (T : Theory L) := HClassIn ξ Γ s (T + 𝐄𝐪)

abbrev DeltaZeroInWithEq (T : Theory L) := DeltaZeroIn ξ (T + 𝐄𝐪)

notation Γ "ᴴ("s")[" T "]" => HClassInWithEq _ Γ s T

notation "Δ₀[" T "]" => DeltaZeroInWithEq _ T

end

namespace Definability

variable {T : Theory ℒₒᵣ}

structure DeltaZeroRelation (T : Theory ℒₒᵣ) (k : ℕ) where
  definition : Semisentence ℒₒᵣ k
  definition_deltaZero : Δ₀[T].Domain definition

namespace DeltaZeroRelation

def eq : DeltaZeroRelation T 2 := ⟨“#0 = #1”, by simp⟩

def lt : DeltaZeroRelation T 2 := ⟨“#0 < #1”, by simp⟩

def le : DeltaZeroRelation T 2 := ⟨“#0 ≤ #1”, by simp⟩

variable {M : Type*} [Structure ℒₒᵣ M]

abbrev eval (p : DeltaZeroRelation T k) (v : Fin k → M) : Prop :=
  Semiformula.PVal! M v p.definition

end DeltaZeroRelation

structure DeltaZeroFunction (T : Theory ℒₒᵣ) (k : ℕ) where
  charactor : DeltaZeroRelation T (k + 1)
  total : T + 𝐄𝐪 ⊢! ∀* ∃! charactor.definition

namespace DeltaZeroFunction

def polynomial {k} (t : Polynomial k) : DeltaZeroFunction T k where
  charactor := ⟨“#0 = !!(Rew.bShift t)”, by simp⟩
  total := Complete.consequence_iff_provable.mp
    <| oRing_consequence_of _ _ <| fun M _ _ _ _ _ _ => by simp [models_iff]

abbrev definition (f : DeltaZeroFunction T k) : Semisentence ℒₒᵣ (k + 1) := f.charactor.definition

lemma polynomial_definition {k} (t : Polynomial k) :
    (polynomial t : DeltaZeroFunction T k).definition = “#0 = !!(Rew.bShift t)” := rfl

def zero : DeltaZeroFunction T 0 := polynomial ᵀ“0”

def one : DeltaZeroFunction T 0 := polynomial ᵀ“1”

def add : DeltaZeroFunction T 2 := polynomial ᵀ“#0 + #1”

def mul : DeltaZeroFunction T 2 := polynomial ᵀ“#0 * #1”

section realize

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

lemma realize_exists_unique (f : DeltaZeroFunction T k) (v : Fin k → M) : ∃! y, Semiformula.PVal! M (y :> v) f.definition := by
  have : ∀ e, ∃! x, (Semiformula.PVal! M (x :> e)) f.definition := by simpa [models_iff] using oring_sound M f.total
  exact this v

noncomputable def realize (f : DeltaZeroFunction T k) (v : Fin k → M) : M := Classical.choose! (realize_exists_unique f v)

lemma realize_graph {f : DeltaZeroFunction T k} {y : M} {v : Fin k → M} :
    y = f.realize v ↔ Semiformula.PVal! M (y :> v) f.definition :=
  Classical.choose!_eq_iff (x := y) <| realize_exists_unique f v

lemma realize_eq_of {f : DeltaZeroFunction T k} {y : M} {v : Fin k → M}
    (H : Semiformula.PVal! M (y :> v) f.definition) : f.realize v = y :=
  Eq.symm <| realize_graph.mpr H

lemma pval_realize_definition (f : DeltaZeroFunction T k) (v : Fin k → M) :
    Semiformula.PVal! M (f.realize v :> v) f.definition := realize_graph.mp rfl

@[simp] lemma zero_realize : (zero : DeltaZeroFunction T 0).realize ![] = (0 : M) :=
  DeltaZeroFunction.realize_eq_of (by simp [zero, polynomial_definition])

@[simp] lemma one_realize : (one : DeltaZeroFunction T 0).realize ![] = (1 : M) :=
  DeltaZeroFunction.realize_eq_of (by simp [one, polynomial_definition])

@[simp] lemma add_realize (a b : M) : (add : DeltaZeroFunction T 2).realize ![a, b] = a + b :=
  DeltaZeroFunction.realize_eq_of (by simp [add, polynomial_definition])

@[simp] lemma mul_realize (a b : M) : (mul : DeltaZeroFunction T 2).realize ![a, b] = a * b :=
  DeltaZeroFunction.realize_eq_of (by simp [mul, polynomial_definition])

end realize

end DeltaZeroFunction

structure BoundedDeltaZeroFunction (T : Theory ℒₒᵣ) (k : ℕ) where
  function : DeltaZeroFunction T k
  bound : Polynomial k
  bounded : T + 𝐏𝐀⁻ + 𝐄𝐪 ⊢! ∀* (function.definition ⟶ “#0 ≤ !!(Rew.bShift bound)”)

namespace BoundedDeltaZeroFunction

def polynomial {k} (t : Polynomial k) : BoundedDeltaZeroFunction T k where
  function := DeltaZeroFunction.polynomial t
  bound := t
  bounded := Complete.consequence_iff_provable.mp
    <| oRing_consequence_of _ _ <| fun M _ _ _ _ _ _ => by
      haveI : T.Mod M := Theory.Mod.of_ss M (T₁ := T + 𝐏𝐀⁻ + 𝐄𝐪) (by simp [Theory.add_def])
      haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_ss M (T₁ := T + 𝐏𝐀⁻ + 𝐄𝐪) (by simp [Theory.add_def])
      simp [models_iff, DeltaZeroFunction.polynomial_definition, Semiterm.val_bShift']
      intro v e; simp [e]

def zero : BoundedDeltaZeroFunction T 0 := polynomial ᵀ“0”

def one : BoundedDeltaZeroFunction T 0 := polynomial ᵀ“1”

def add : BoundedDeltaZeroFunction T 2 := polynomial ᵀ“#0 + #1”

def mul : BoundedDeltaZeroFunction T 2 := polynomial ᵀ“#0 * #1”

section realize

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

noncomputable abbrev realize (f : BoundedDeltaZeroFunction T k) (v : Fin k → M) := f.function.realize v

@[simp] lemma zero_realize : (zero : BoundedDeltaZeroFunction T 0).realize ![] = (0 : M) :=
  Eq.trans rfl DeltaZeroFunction.zero_realize

@[simp] lemma one_realize : (one : BoundedDeltaZeroFunction T 0).realize ![] = (1 : M) :=
  Eq.trans rfl DeltaZeroFunction.one_realize

@[simp] lemma add_realize (a b : M) : (add : BoundedDeltaZeroFunction T 2).realize ![a, b] = a + b :=
  Eq.trans rfl (DeltaZeroFunction.add_realize a b)

@[simp] lemma mul_realize (a b : M) : (mul : BoundedDeltaZeroFunction T 2).realize ![a, b] = a * b :=
  Eq.trans rfl (DeltaZeroFunction.mul_realize a b)

variable [𝐏𝐀⁻.Mod M]

lemma realize_le_bound (f : BoundedDeltaZeroFunction T k) (v : Fin k → M) :
    f.realize v ≤ Semiterm.bVal! M v f.bound := by
  have : ∀ v : Fin (k + 1) → M,
      (Semiformula.PVal! M v) f.function.definition → v 0 ≤ Semiterm.bVal! M (v ·.succ) f.bound := by
    simpa [models_def, Semiterm.val_bShift'] using oring_sound M f.bounded
  simpa using this (f.function.realize v :> v) (DeltaZeroFunction.pval_realize_definition _ _)

end realize

end BoundedDeltaZeroFunction

def boundedLanguage (T : Theory ℒₒᵣ) : Language where
  Func := BoundedDeltaZeroFunction T
  Rel := DeltaZeroRelation T

notation "ℒₒᵣ[" T "]" => boundedLanguage T

namespace boundedLanguage

def _root_.LO.FirstOrder.Arith.Definition.BoundedDeltaZeroFunction.toFunc {k} (f : BoundedDeltaZeroFunction T k) : ℒₒᵣ[T].Func k := f

def _root_.LO.FirstOrder.Arith.FormulaHierarchy.toRel {k} (r : DeltaZeroRelation T k) : ℒₒᵣ[T].Rel k := r

instance : Language.Eq ℒₒᵣ[T] := ⟨DeltaZeroRelation.eq⟩

instance : Language.LT ℒₒᵣ[T] := ⟨DeltaZeroRelation.lt⟩

instance : Language.Zero ℒₒᵣ[T] := ⟨BoundedDeltaZeroFunction.zero⟩

instance : Language.One ℒₒᵣ[T] := ⟨BoundedDeltaZeroFunction.one⟩

instance : Language.Add ℒₒᵣ[T] := ⟨BoundedDeltaZeroFunction.add⟩

instance : Language.Mul ℒₒᵣ[T] := ⟨BoundedDeltaZeroFunction.mul⟩

instance : Language.ORing ℒₒᵣ[T] where

def polybound {n : ℕ} : Semiterm ℒₒᵣ[T] ξ n → Semiterm ℒₒᵣ ξ n
  | #x                => #x
  | &x                => &x
  | Semiterm.func f v => Rew.embSubsts (fun i ↦ polybound (v i)) f.bound

lemma polybound_positive {t : Semiterm ℒₒᵣ[T] ξ (n + 1)} :
    t.Positive → (polybound t).Positive := by
  induction t <;> simp [polybound, *]
  case func t v ih =>
    intro h i _; exact ih i (h i)

lemma polybound_bShift (t : Semiterm ℒₒᵣ[T] ξ n) :
    polybound (Rew.bShift t) = Rew.bShift (polybound t) := by
  induction t <;> simp [polybound]
  case func f v ih =>
    show (Rew.embSubsts fun i => polybound (Rew.bShift (v i))) f.bound =
      Rew.bShift ((Rew.embSubsts fun i => polybound (v i)) f.bound)
    simp [ih, ←Rew.comp_app]; congr 1
    ext <;> simp [Rew.comp_app]; { contradiction }

variable (T)

inductive Denotation : ℕ → Type
  | var {n} : Fin n → Denotation n
  | comp {arity n : ℕ} :
    DeltaZeroRelation T (arity + 1) → (Fin arity → Denotation n) → (Fin arity → Polynomial n) → Denotation n

variable {T}

namespace Denotation

def bShift : Denotation T n → Denotation T (n + 1)
  | var x      => var x.succ
  | comp p v t => comp p (fun i ↦ bShift (v i)) (fun i ↦ Rew.bShift (t i))

def toFormula : Denotation T n → Semisentence ℒₒᵣ (n + 1)
  | var x                   => “#0 = !!#x.succ”
  | comp (arity := k) p v b =>
      Rew.toS.hom
        <| bexClosure (fun i ↦ “#0 < !!(Rew.bShift $ Rew.toF $ Rew.bShift $ b i) + 1”)
        <| (Matrix.conj fun i : Fin k ↦ (Rew.embSubsts (#i :> (& ·.succ))).hom (v i).toFormula) ⋏ (Rew.embSubsts (&0 :> (# ·))).hom p.definition

def ofTerm : Semiterm ℒₒᵣ[T] Empty n → Denotation T n
  | #x                                                 => var x
  | Semiterm.func (f : BoundedDeltaZeroFunction T _) v =>
      comp f.function.charactor (fun i ↦ ofTerm (v i)) (fun i ↦ polybound (v i))

def atom {k n} (p : DeltaZeroRelation T k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) : Semisentence ℒₒᵣ n :=
  Rew.toS.hom
    <| bexClosure (fun i ↦ “#0 < !!(Rew.bShift $ Rew.toF $ polybound (v i)) + 1”)
      <| (Matrix.conj fun i : Fin k ↦ (Rew.embSubsts (#i :> (& ·))).hom (ofTerm $ v i).toFormula) ⋏ Rew.emb.hom p.definition

lemma toFormula_deltaZero (d : Denotation T n) : Δ₀[T].Domain d.toFormula := by
  induction d <;> simp [Denotation.toFormula]
  case comp p d t IH =>
    exact HClassIn.rew
      (Class.bexClosure (by simp)
        (Class.And.and (Class.matrix_conj fun j ↦ HClassIn.rew (IH j) _) (HClassIn.rew p.definition_deltaZero _))) _

lemma atom_deltaZero {k n} (p : DeltaZeroRelation T k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    Δ₀[T].Domain (Denotation.atom p v) := by
  simp [Denotation.atom]
  exact HClassIn.rew (Class.bexClosure (by simp)
    <| Class.And.and (Class.matrix_conj fun _ ↦ HClassIn.rew (toFormula_deltaZero _) _) (HClassIn.rew p.definition_deltaZero _)) _

end Denotation

def arithmetizeAux {n : ℕ} : Semisentence ℒₒᵣ[T] n → Semisentence ℒₒᵣ n
  | Semiformula.rel (p : DeltaZeroRelation T _) v  => Denotation.atom p v
  | Semiformula.nrel (p : DeltaZeroRelation T _) v => ~Denotation.atom p v
  | ⊤                                => ⊤
  | ⊥                                => ⊥
  | p ⋏ q                            => arithmetizeAux p ⋏ arithmetizeAux q
  | p ⋎ q                            => arithmetizeAux p ⋎ arithmetizeAux q
  | ∀' p                             => ∀' arithmetizeAux p
  | ∃' p                             => ∃' arithmetizeAux p

lemma arithmetize_aux_not_not (p : Semisentence ℒₒᵣ[T] n) : arithmetizeAux (~p) = ~arithmetizeAux p := by
  induction p using Semiformula.rec' <;> simp [arithmetizeAux, ←Semiformula.neg_eq, *]

def arithmetize : Semisentence ℒₒᵣ[T] n →ˡᶜ Semisentence ℒₒᵣ n where
  toTr := arithmetizeAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := fun _ ↦ by simp [arithmetize_aux_not_not]
  map_imply' := fun _ _ ↦ by simp [Semiformula.imp_eq, ←Semiformula.neg_eq, arithmetizeAux, arithmetize_aux_not_not]

@[simp] lemma arithmetize_rel {k} (p : DeltaZeroRelation T k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    arithmetize (Semiformula.rel p v) = Denotation.atom p v := rfl

@[simp] lemma arithmetize_nrel {k} (p : DeltaZeroRelation T k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    arithmetize (Semiformula.nrel p v) = ~Denotation.atom p v := rfl

@[simp] lemma arithmetize_all (p : Semisentence ℒₒᵣ[T] (n + 1)) : arithmetize (∀' p) = ∀' arithmetize p := rfl

@[simp] lemma arithmetize_ex (p : Semisentence ℒₒᵣ[T] (n + 1)) : arithmetize (∃' p) = ∃' arithmetize p := rfl

/-
lemma arithmetize_hierarsssschy {p : Semisentence ℒₒᵣ[T] n} (hp : Hierarchy b s p) :
    Hierarchy b s (arithmetize p) := by {
  induction p using Semiformula.rec' <;> simp [*]
  case hand ihp ihq => simp at hp; exact ⟨ihp hp.1, ihq hp.2⟩
  case hor ihp ihq => simp at hp; exact ⟨ihp hp.1, ihq hp.2⟩
  case hall ih =>
    have := ih hp.remove_forall
   }

lemma arithmetize_hierarchy (p : Semisentence ℒₒᵣ[T] n) :
    Hierarchy b s (arithmetize p) ↔ Hierarchy b s p := by {
  induction p using Semiformula.rec' <;> simp [*]
   }
-/

section semantics

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

noncomputable instance semantics : Structure ℒₒᵣ[T] M where
  func := fun k (f : BoundedDeltaZeroFunction T k) v ↦ f.function.realize v
  rel := fun k (p : DeltaZeroRelation T k) v ↦ p.eval v

@[simp] lemma semantics_func {k} (f : BoundedDeltaZeroFunction T k) (v : Fin k → M) :
    semantics.func f v = f.function.realize v := rfl

@[simp] lemma semantics_rel {k} (p : DeltaZeroRelation T k) (v : Fin k → M) :
    semantics.rel (L := ℒₒᵣ[T]) p v ↔ p.eval v := iff_of_eq rfl

instance : Structure.Zero ℒₒᵣ[T] M :=
  ⟨by simp[Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Language.Zero.zero]⟩

instance : Structure.One ℒₒᵣ[T] M :=
  ⟨by simp[Semiterm.Operator.val, Semiterm.Operator.One.one, Language.One.one]⟩

instance : Structure.Add ℒₒᵣ[T] M :=
  ⟨by intro a b; simp[Semiterm.Operator.val, Semiterm.val_func, Semiterm.Operator.Add.add, Language.Add.add]⟩

instance : Structure.Mul ℒₒᵣ[T] M :=
  ⟨by intro a b; simp[Semiterm.Operator.val, Semiterm.val_func, Semiterm.Operator.Mul.mul, Language.Mul.mul]⟩

instance : Structure.Eq ℒₒᵣ[T] M :=
  ⟨by intro a b
      simp[DeltaZeroRelation.eval, Semiformula.Operator.val,
        Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel, Language.Eq.eq]
      simp [DeltaZeroRelation.eq]⟩

instance : Structure.LT ℒₒᵣ[T] M :=
  ⟨by intro a b
      simp [DeltaZeroRelation.eval, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, Semiformula.eval_rel, Language.LT.lt]
      simp [DeltaZeroRelation.lt]⟩

variable [𝐏𝐀⁻.Mod M]

lemma le_bound (t : Semiterm ℒₒᵣ[T] ξ n) (ε v) :
    Semiterm.val! M v ε t ≤ Semiterm.val! M v ε (polybound t) := by
  induction t
  case bvar => simp [polybound]
  case fvar => simp [polybound]
  case func f v IH =>
    simp [Semiterm.val_func, polybound, Semiterm.val_embSubsts]
    exact le_trans (f.realize_le_bound _) (Model.polynomial_mono _ IH (by simp))

lemma pval_of_term_to_formula {t : Semiterm ℒₒᵣ[T] Empty n} {y : M} {v} :
    Semiformula.PVal! M (y :> v) (Denotation.ofTerm t).toFormula ↔ y = Semiterm.bVal! M v t := by
  induction t generalizing y v <;> try simp [Denotation.ofTerm, Denotation.toFormula, Model.lt_succ_iff_le]
  case fvar x =>
    contradiction
  case func f w IH =>
    simp [Denotation.toFormula, Matrix.succ_pred, Matrix.comp_vecCons', Semiterm.val_func, DeltaZeroFunction.realize_graph, IH]
    constructor
    · rintro ⟨e, _, he, H⟩
      rcases show e = fun x ↦ Semiterm.bVal! M v (w x) from funext he
      exact H
    · intro H
      exact ⟨fun x ↦ Semiterm.bVal! M v (w x), fun i ↦ le_bound (w i) _ _, fun i ↦ rfl, H⟩

lemma pval_atom_iff {k n} (e : Fin n → M) (p : DeltaZeroRelation T k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    Semiformula.PVal! M e (Denotation.atom p v) ↔ p.eval fun i => (v i).bVal! M e := by
  simp [Denotation.atom, Denotation.toFormula, Model.lt_succ_iff_le]
  constructor
  · rintro ⟨w, bw, hw, H⟩
    suffices w = fun i ↦ (v i).bVal! M e by
      rcases this; exact H
    funext i
    exact pval_of_term_to_formula.mp (hw i)
  · intro H
    exact ⟨fun i ↦ (v i).bVal! M e, fun i ↦ by simp [le_bound], fun i ↦ pval_of_term_to_formula.mpr (by simp), H⟩

@[simp] lemma arithmetize_iff {n} (v : Fin n → M) (p : Semisentence ℒₒᵣ[T] n) :
    Semiformula.PVal! M v (arithmetize p) ↔ Semiformula.PVal! M v p := by
  induction p using Semiformula.rec' <;> try simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, pval_atom_iff]

end semantics

section hierarchy

abbrev HClassInBL (ξ : Type*) [DecidableEq ξ] (Γ : Polarity) (s : ℕ) (T : Theory ℒₒᵣ) : Class ℒₒᵣ[T] ξ :=
    HClassIn ξ Γ s (T.lMap Language.oringEmb + 𝐄𝐪)

abbrev DeltaZeroInBL (ξ : Type*) [DecidableEq ξ] (T : Theory ℒₒᵣ) : Class ℒₒᵣ[T] ξ :=
    HClassInBL ξ Σ 0 T

notation Γ "ᴴ'("s")[" T "]" => HClassInBL _ Γ s T

notation "Δ₀'[" T "]" => DeltaZeroInBL _ T

namespace HClassInBL

variable {T : Theory ℒₒᵣ} [𝐄𝐪 ≾ T] [𝐏𝐀⁻ ≾ T] {ξ : Type*} [DecidableEq ξ]

@[formula_class] lemma ball_le {n} {p : Semiformula ℒₒᵣ[T] ξ (n + 1)} {t} (hp : (HClassInBL ξ Γ s T).Domain p) (ht : t.Positive) :
    (HClassInBL ξ Γ s T).Domain (∀[“#0 ≤ !!t”] p) := by
  have : (HClassInBL ξ Γ s T).Domain (∀[“#0 < !!t + 1”] p) := Class.BAll.ball hp (by simp [ht])
  exact Class.domain_eqvClosure this (by
    unfold Semiformula.Equivalent
    apply consequence_of
    intro M _ _ _ _ _ _ _ instMod
    haveI : T.Mod M := (mod_lMap_oringEmb T).mp (@Theory.Mod.of_add_left _ M _ _ _ _ instMod)
    haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M 𝐏𝐀⁻ T
    simp [models_iff, Model.le_iff_lt_succ])

@[formula_class] lemma bex_le {n} {p : Semiformula ℒₒᵣ[T] ξ (n + 1)} {t} (hp : (HClassInBL ξ Γ s T).Domain p) (ht : t.Positive) :
    (HClassInBL ξ Γ s T).Domain (∃[“#0 ≤ !!t”] p) := by
  have : (HClassInBL ξ Γ s T).Domain (∃[“#0 < !!t + 1”] p) := Class.BEx.bex hp (by simp [ht])
  exact Class.domain_eqvClosure this (by
    apply consequence_of
    intro M _ _ _ _ _ _ _ instMod
    haveI : T.Mod M := (mod_lMap_oringEmb T).mp (@Theory.Mod.of_add_left _ M _ _ _ _ instMod)
    haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M 𝐏𝐀⁻ T
    simp [models_iff, Model.le_iff_lt_succ])

end HClassInBL

example : (Δ₀'[𝐏𝐀⁻] : Class ℒₒᵣ[𝐏𝐀⁻] ℕ).Domain (“∀[#0 ≤ 5] !(Rew.bShift.hom “0 < #3”)” : Semiformula ℒₒᵣ[𝐏𝐀⁻] ℕ 8) := by
  formula_class

end hierarchy

variable {T : Theory ℒₒᵣ} [𝐏𝐀⁻ ≾ T]

lemma arithmetize_lt_deltaZero (t u : Semiterm ℒₒᵣ[T] Empty n) :
    Δ₀[T].Domain (arithmetize “!!t < !!u”) := by
  simp [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq, Rew.rel]
  exact Denotation.atom_deltaZero _ _

lemma arithmetize_le_deltaZero (t u : Semiterm ℒₒᵣ[T] Empty n) :
    Δ₀[T].Domain (arithmetize “!!t ≤ !!u”) := by
  simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.LE.sentence_eq, Rew.rel]
  exact Class.Or.or (Denotation.atom_deltaZero _ _) (Denotation.atom_deltaZero _ _)

lemma arithmetize_hClassIn_of_hierarchy {p : Semisentence ℒₒᵣ[T] n} (hp : Hierarchy Γ s p) :
    Γᴴ(s)[T].Domain (arithmetize p) := by
  induction hp <;> try simp
  case rel p v =>
    exact HClassIn.of_deltaZeroIn (Denotation.atom_deltaZero p v)
  case nrel p v =>
    exact HClassIn.of_deltaZeroIn (Class.Not.not $ Denotation.atom_deltaZero p v)
  case and ihp ihq => exact Class.And.and ihp ihq
  case or ihp ihq => exact Class.Or.or ihp ihq
  case ball p t ht _ ih =>
    have : arithmetize “∀[#0 < !!t] !p” ↔[T + 𝐄𝐪] (∀[“#0 < !!(polybound t)”] (arithmetize (“!!t ≤ #0”) ⋎ arithmetize p)) := by
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      apply oRing_consequence_of
      intro M _ _ _ _ _ mod
      haveI : T.Mod M := Theory.Mod.of_add_left M T 𝐄𝐪
      haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M 𝐏𝐀⁻ T
      simp [models_iff, Empty.eq_elim, polybound_bShift]
      intro e; constructor
      · intro h x _; simpa [imp_iff_not_or] using h x
      · intro h x hx
        exact Classical.or_iff_not_imp_left.mp (h x $ lt_of_lt_of_le hx (le_bound t Empty.elim e)) (by simpa using hx)
    exact Class.domain_eqvClosure
      (Class.BAll.ball (Class.Or.or (HClassIn.of_deltaZeroIn $ arithmetize_le_deltaZero _ _) ih) (polybound_positive ht)) this.symm
  case bex p t ht _ ih =>
    have : arithmetize “∃[#0 < !!t] !p” ↔[T + 𝐄𝐪] (∃[“#0 < !!(polybound t)”] (arithmetize (“#0 < !!t”) ⋏ arithmetize p)) := by
      rcases Rew.positive_iff.mp ht with ⟨t, rfl⟩
      apply oRing_consequence_of
      intro M _ _ _ _ _ mod
      haveI : T.Mod M := Theory.Mod.of_add_left M T 𝐄𝐪
      haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M 𝐏𝐀⁻ T
      simp [models_iff, Empty.eq_elim, polybound_bShift]
      intro e; constructor
      · rintro ⟨x, hx, hp⟩
        exact ⟨x, lt_of_lt_of_le hx (le_bound t Empty.elim e), hx, hp⟩
      · rintro ⟨x, _, hx, hp⟩; exact ⟨x, hx, hp⟩
    exact Class.domain_eqvClosure
      (Class.BEx.bex (Class.And.and (HClassIn.of_deltaZeroIn $ arithmetize_lt_deltaZero _ _) ih) (polybound_positive ht)) this.symm
  case all p _ ih => exact HClassIn.all ih
  case ex p _ ih => exact HClassIn.ex ih
  case pi p _ ih => exact HClassIn.pi ih
  case sigma p _ ih => exact HClassIn.sigma ih
  case dummy_pi p _ ih => exact HClassIn.dummy_pi ih
  case dummy_sigma p _ ih => exact HClassIn.dummy_sigma ih

lemma arithmetize_hClassIn {p : Semisentence ℒₒᵣ[T] n} (hp : Γᴴ'(s)[T].Domain p) :
    Γᴴ(s)[T].Domain (arithmetize p) := by
  rcases hp with ⟨p', hp', H⟩
  exact Class.domain_eqvClosure (arithmetize_hClassIn_of_hierarchy hp') (by
    apply oRing_consequence_of
    intro M _ _ _ _ _ mod
    haveI : T.Mod M := Theory.Mod.of_add_left M T 𝐄𝐪
    haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M 𝐏𝐀⁻ T
    have : M ⊧ₘ (∀ᶠ* ∀* (p' ⟷ p)) := consequence_iff.mp H M (by simp [Theory.add_def, Theory.Mod.modelsTheory])
    simp [models_iff, Empty.eq_elim] at this ⊢; intro e; exact this e)

lemma arithmetize_deltaZero {p : Semisentence ℒₒᵣ[T] n} (hp : Δ₀'[T].Domain p) :
    Δ₀[T].Domain (arithmetize p) := arithmetize_hClassIn hp

end boundedLanguage

abbrev HSemiformulaIn (T : Theory ℒₒᵣ) (Γ : Polarity) (s : ℕ) (ξ : Type*) [DecidableEq ξ] (n : ℕ) : Type _ :=
  { p : Semiformula ℒₒᵣ ξ n // Γᴴ(s)[T].Domain p }

abbrev HSemisentenceIn (T : Theory ℒₒᵣ) (Γ : Polarity) (s : ℕ) (n : ℕ) : Type _ := HSemiformulaIn T Γ s Empty n

abbrev HSemiformulaΔ₀In (T : Theory ℒₒᵣ) (ξ : Type*) [DecidableEq ξ] (n : ℕ) : Type _ := HSemiformulaIn T Σ 0 ξ n

abbrev HSemisentenceΔ₀In (T : Theory ℒₒᵣ) (n : ℕ) : Type _ := HSemiformulaΔ₀In T Empty n

abbrev BSemiformula (T : Theory ℒₒᵣ) (Γ : Polarity) (s : ℕ) (ξ : Type*) [DecidableEq ξ] (n : ℕ) : Type _ :=
  { p : Semiformula ℒₒᵣ[T] ξ n // Γᴴ'(s)[T].Domain p }

abbrev BSemisentence (T : Theory ℒₒᵣ) (Γ : Polarity) (s : ℕ) (n : ℕ) : Type _ := BSemiformula T Γ s Empty n

abbrev BSemiformulaΔ₀ (T : Theory ℒₒᵣ) (ξ : Type*) [DecidableEq ξ] (n : ℕ) : Type _ :=
  { p : Semiformula ℒₒᵣ[T] ξ n // Δ₀'[T].Domain p }

abbrev BSemisentenceΔ₀ (T : Theory ℒₒᵣ) (n : ℕ) : Type _ := BSemiformulaΔ₀ T Empty n

namespace BSemiformula

variable {Γ : Polarity} {s : ℕ} {T : Theory ℒₒᵣ} {ξ : Type*} [DecidableEq ξ] {n : ℕ}

@[simp] lemma hClassInBL_val (p : BSemiformula T Γ s ξ n) : Γᴴ'(s)[T].Domain p.val := p.property

@[simp] lemma deltaZeroInBL_val (p : BSemiformulaΔ₀ T ξ n) : Δ₀'[T].Domain p.val := p.property

end BSemiformula

open boundedLanguage

variable {T : Theory ℒₒᵣ} [𝐏𝐀⁻ ≾ T]

def toDeltaZeroRelation (σ : Semisentence ℒₒᵣ[T] k)
    (hσ : Δ₀'[T].Domain σ) : DeltaZeroRelation T k where
  definition := arithmetize σ
  definition_deltaZero := arithmetize_deltaZero hσ

def toBoundedDeltaZeroFunction (σ : Semisentence ℒₒᵣ[T] (k + 1))
    (hσ : Δ₀'[T].Domain σ)
    (total : T + 𝐄𝐪 ⊢! ∀* ∃! arithmetize σ)
    (bound : Polynomial k)
    (bounded : T + 𝐏𝐀⁻ + 𝐄𝐪 ⊢! ∀* “!(arithmetize σ) → #0 ≤ !!(Rew.bShift bound)”) : BoundedDeltaZeroFunction T k where
  function := ⟨toDeltaZeroRelation σ hσ, total⟩
  bound := bound
  bounded := by simpa [DeltaZeroFunction.definition, toDeltaZeroRelation]

section semantics

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

variable {σ : Semisentence ℒₒᵣ[T] (k + 1)}
    {hσ : Δ₀'[T].Domain σ}
    {total : T + 𝐄𝐪 ⊢! ∀* ∃! arithmetize σ}
    {bound : Polynomial k}
    {bounded : T + 𝐏𝐀⁻ + 𝐄𝐪 ⊢! ∀* “!(arithmetize σ) → #0 ≤ !!(Rew.bShift bound)”}

lemma toBoundedDeltaZeroFunction_realize_iff {a : M} {v : Fin k → M} :
    a = (toBoundedDeltaZeroFunction σ hσ total bound bounded).realize v ↔ Semiformula.PVal! M (a :> v) σ := by
  haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_provably_subtheory' M _ T
  simp [DeltaZeroFunction.realize_graph, toBoundedDeltaZeroFunction, toDeltaZeroRelation, DeltaZeroFunction.definition]

lemma toBoundedDeltaZeroFunction_realize_iff' {v : Fin (k + 1) → M} :
    Semiformula.PVal! M v σ ↔ v 0 = (toBoundedDeltaZeroFunction σ hσ total bound bounded).realize (v ·.succ) := by
  simp [toBoundedDeltaZeroFunction_realize_iff, Matrix.eq_vecCons']

end semantics

end Definability

end Arith

end LO.FirstOrder
