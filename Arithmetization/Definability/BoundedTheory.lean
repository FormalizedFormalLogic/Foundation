import Arithmetization.Definability.Definability

lemma Matrix.succ_pred {n : ℕ} (P : Fin n.succ → Prop) : (∀ i, P i) ↔ (P 0 ∧ ∀ i : Fin n, P i.succ) :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, fun h ↦ Fin.cases h.1 h.2⟩

namespace LO.FirstOrder

namespace Arith

namespace Definability

namespace FormulaHierarchy

variable {L : Language} [L.LT] [Structure L M]

def eval (p : SentenceHierarchy b s L k) (v : Fin k → M) : Prop :=
  Semiformula.PVal! M v p.val

end FormulaHierarchy

variable {T : Theory ℒₒᵣ}

structure Function (T : Theory ℒₒᵣ) (k : ℕ) where
  definition : Σᴬ[0] (k + 1)
  total : T + 𝐄𝐪 ⊢! ∀* ∃! definition.val

namespace Function

def polynomial {k} (t : Polynomial k) : Function T k where
  definition := ⟨“#0 = !!(Rew.bShift t)”, by simp⟩
  total := Complete.consequence_iff_provable.mp
    <| oRing_consequence_of _ _ <| fun M _ _ _ _ _ _ => by simp [models_iff]

lemma polynomial_definition {k} (t : Polynomial k) :
    (polynomial (T := T) t).definition.val = “#0 = !!(Rew.bShift t)” := rfl

def zero : Function T 0 := polynomial ᵀ“0”

def one : Function T 0 := polynomial ᵀ“1”

def add : Function T 2 := polynomial ᵀ“#0 + #1”

def mul : Function T 2 := polynomial ᵀ“#0 * #1”

section realize

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

lemma realize_exists_unique (f : Function T k) (v : Fin k → M) : ∃! y, Semiformula.PVal! M (y :> v) f.definition.val := by
  have : ∀ e, ∃! x, (Semiformula.PVal! M (x :> e)) f.definition.val := by simpa [models_iff] using oring_sound M f.total
  exact this v

noncomputable def realize (f : Function T k) (v : Fin k → M) : M := Classical.choose! (realize_exists_unique f v)

lemma realize_graph {f : Function T k} {y : M} {v : Fin k → M} :
    y = f.realize v ↔ Semiformula.PVal! M (y :> v) f.definition.val :=
  Classical.choose!_eq_iff (x := y) <| realize_exists_unique f v

lemma realize_eq_of {f : Function T k} {y : M} {v : Fin k → M}
    (H : Semiformula.PVal! M (y :> v) f.definition.val) : f.realize v = y :=
  Eq.symm <| realize_graph.mpr H

lemma pval_realize_definition (f : Function T k) (v : Fin k → M) :
    Semiformula.PVal! M (f.realize v :> v) f.definition.val := realize_graph.mp rfl

@[simp] lemma zero_realize : (zero : Function T 0).realize ![] = (0 : M) :=
  Function.realize_eq_of (by simp [zero, polynomial_definition])

@[simp] lemma one_realize : (one : Function T 0).realize ![] = (1 : M) :=
  Function.realize_eq_of (by simp [one, polynomial_definition])

@[simp] lemma add_realize (a b : M) : (add : Function T 2).realize ![a, b] = a + b :=
  Function.realize_eq_of (by simp [add, polynomial_definition])

@[simp] lemma mul_realize (a b : M) : (mul : Function T 2).realize ![a, b] = a * b :=
  Function.realize_eq_of (by simp [mul, polynomial_definition])

end realize

end Function

structure BoundedFunction (T : Theory ℒₒᵣ) (k : ℕ) where
  function : Function T k
  bound : Polynomial k
  bounded : T + 𝐏𝐀⁻ + 𝐄𝐪 ⊢! ∀* (function.definition.val ⟶ “#0 ≤ !!(Rew.bShift bound)”)

namespace BoundedFunction

def polynomial {k} (t : Polynomial k) : BoundedFunction T k where
  function := Function.polynomial t
  bound := t
  bounded := Complete.consequence_iff_provable.mp
    <| oRing_consequence_of _ _ <| fun M _ _ _ _ _ _ => by
      haveI : T.Mod M := Theory.Mod.of_ss M (T₁ := T + 𝐏𝐀⁻ + 𝐄𝐪) (by simp [Theory.add_def])
      haveI : 𝐏𝐀⁻.Mod M := Theory.Mod.of_ss M (T₁ := T + 𝐏𝐀⁻ + 𝐄𝐪) (by simp [Theory.add_def])
      simp [models_iff, Function.polynomial_definition, Semiterm.val_bShift']
      intro v e; simp [e]

def zero : BoundedFunction T 0 := polynomial ᵀ“0”

def one : BoundedFunction T 0 := polynomial ᵀ“1”

def add : BoundedFunction T 2 := polynomial ᵀ“#0 + #1”

def mul : BoundedFunction T 2 := polynomial ᵀ“#0 * #1”

section realize

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

@[simp] lemma zero_realize : (zero : BoundedFunction T 0).function.realize ![] = (0 : M) :=
  Eq.trans rfl Function.zero_realize

@[simp] lemma one_realize : (one : BoundedFunction T 0).function.realize ![] = (1 : M) :=
  Eq.trans rfl Function.one_realize

@[simp] lemma add_realize (a b : M) : (add : BoundedFunction T 2).function.realize ![a, b] = a + b :=
  Eq.trans rfl (Function.add_realize a b)

@[simp] lemma mul_realize (a b : M) : (mul : BoundedFunction T 2).function.realize ![a, b] = a * b :=
  Eq.trans rfl (Function.mul_realize a b)

variable [𝐏𝐀⁻.Mod M]

lemma realize_le_bound (f : BoundedFunction T k) (v : Fin k → M) :
    f.function.realize v ≤ Semiterm.bVal! M v f.bound := by
  have : ∀ v : Fin (k + 1) → M,
      (Semiformula.PVal! M v) f.function.definition.val → v 0 ≤ Semiterm.bVal! M (v ·.succ) f.bound := by
    simpa [models_def, Semiterm.val_bShift'] using oring_sound M f.bounded
  simpa using this (f.function.realize v :> v) (Function.pval_realize_definition _ _)

end realize

end BoundedFunction

def boundedLanguage (T : Theory ℒₒᵣ) : Language where
  Func := BoundedFunction T
  Rel := Σᴬ[0]

notation "ℒₒᵣ[" T "]" => boundedLanguage T

namespace boundedLanguage

def _root_.LO.FirstOrder.Arith.Definition.BoundedFunction.toFunc {k} (f : BoundedFunction T k) : ℒₒᵣ[T].Func k := f

def _root_.LO.FirstOrder.Arith.FormulaHierarchy.toRel {k} (r : Σᴬ[0] k) : ℒₒᵣ[T].Rel k := r

instance : Language.Eq ℒₒᵣ[T] := ⟨SentenceHierarchy.eq⟩

instance : Language.LT ℒₒᵣ[T] := ⟨SentenceHierarchy.lt⟩

instance : Language.Zero ℒₒᵣ[T] := ⟨BoundedFunction.zero⟩

instance : Language.One ℒₒᵣ[T] := ⟨BoundedFunction.one⟩

instance : Language.Add ℒₒᵣ[T] := ⟨BoundedFunction.add⟩

instance : Language.Mul ℒₒᵣ[T] := ⟨BoundedFunction.mul⟩

def polybound {n : ℕ} : Semiterm ℒₒᵣ[T] ξ n → Semiterm ℒₒᵣ ξ n
  | #x                => #x
  | &x                => &x
  | Semiterm.func f v => Rew.embSubsts (fun i ↦ polybound (v i)) f.bound

inductive Denotation : ℕ → Type
  | var {n} : Fin n → Denotation n
  | comp {arity n : ℕ} : Σᴬ[0] (arity + 1) → (Fin arity → Denotation n) → (Fin arity → Polynomial n) → Denotation n

namespace Denotation

def bShift : Denotation n → Denotation (n + 1)
  | var x      => var x.succ
  | comp p v t => comp p (fun i ↦ bShift (v i)) (fun i ↦ Rew.bShift (t i))

def toFormula : Denotation n → Semisentence ℒₒᵣ (n + 1)
  | var x                   => “#0 = !!#x.succ”
  | comp (arity := k) p v b =>
      Rew.toS.hom
        <| bexClosure (fun i ↦ “#0 < !!(Rew.bShift $ Rew.toF $ Rew.bShift $ b i) + 1”)
        <| (Matrix.conj fun i : Fin k ↦ (Rew.embSubsts (#i :> (& ·.succ))).hom (v i).toFormula) ⋏ (Rew.embSubsts (&0 :> (# ·))).hom p.val

def ofTerm : Semiterm ℒₒᵣ[T] Empty n → Denotation n
  | #x                                        => var x
  | Semiterm.func (f : BoundedFunction T _) v =>
      comp f.function.definition (fun i ↦ ofTerm (v i)) (fun i ↦ polybound (v i))

def atom {k n} (p : Σᴬ[0] k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) : Semisentence ℒₒᵣ n :=
  Rew.toS.hom
    <| bexClosure (fun i ↦ “#0 < !!(Rew.bShift $ Rew.toF $ polybound (v i)) + 1”)
      <| (Matrix.conj fun i : Fin k ↦ (Rew.embSubsts (#i :> (& ·))).hom (ofTerm $ v i).toFormula) ⋏ Rew.emb.hom p.val

@[simp] lemma hierarchy (d : Denotation n) :
    Hierarchy b s d.toFormula := by
  induction d <;> simp [Denotation.toFormula]
  case comp p d t IH =>
    rw [Hierarchy.bexClosure_iff]
    · simp [IH]
    · simp

@[simp] lemma atom_hierarchy {k n} (p : Σᴬ[0] k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    Hierarchy b s (Denotation.atom p v) := by
  simp [Denotation.atom]; rw [Hierarchy.bexClosure_iff] <;> simp [Denotation.ofTerm]

end Denotation

def arithmetizeAux {n : ℕ} : Semisentence ℒₒᵣ[T] n → Semisentence ℒₒᵣ n
  | Semiformula.rel (p : Σᴬ[0] _) v  => Denotation.atom p v
  | Semiformula.nrel (p : Σᴬ[0] _) v => ~Denotation.atom p v
  | ⊤                                => ⊤
  | ⊥                                => ⊥
  | p ⋏ q                            => arithmetizeAux p ⋏ arithmetizeAux q
  | p ⋎ q                            => arithmetizeAux p ⋎ arithmetizeAux q
  | ∀' p                             => ∀' arithmetizeAux p
  | ∃' p                             => ∃' arithmetizeAux p

lemma arithmetize_aux_not_not (p : Semisentence ℒₒᵣ[T] n) : arithmetizeAux (~p) = ~arithmetizeAux p := by
  induction p using Semiformula.rec' <;> simp [arithmetizeAux, ←Semiformula.neg_eq, *]

def arithmetize : Semisentence ℒₒᵣ[T] n →L Semisentence ℒₒᵣ n where
  toTr := arithmetizeAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := fun _ ↦ by simp [arithmetize_aux_not_not]
  map_imply' := fun _ _ ↦ by simp [Semiformula.imp_eq, ←Semiformula.neg_eq, arithmetizeAux, arithmetize_aux_not_not]

@[simp] lemma arithmetize_rel {k} (p : Σᴬ[0] k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    arithmetize (Semiformula.rel p v) = Denotation.atom p v := rfl

@[simp] lemma arithmetize_nrel {k} (p : Σᴬ[0] k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
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
  func := fun k (f : BoundedFunction T k) v ↦ f.function.realize v
  rel := fun k (p : Σᴬ[0] k) v ↦ FormulaHierarchy.eval p v

@[simp] lemma semantics_func {k} (f : BoundedFunction T k) (v : Fin k → M) :
    semantics.func f v = f.function.realize v := rfl

@[simp] lemma semantics_rel {k} (p : Σᴬ[0] k) (v : Fin k → M) :
    semantics.rel (L := ℒₒᵣ[T]) p v ↔ FormulaHierarchy.eval p v := iff_of_eq rfl

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
      simp[FormulaHierarchy.eval, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel, Language.Eq.eq]
      simp [SentenceHierarchy.eq]⟩

instance : Structure.LT ℒₒᵣ[T] M :=
  ⟨by intro a b
      simp[FormulaHierarchy.eval, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, Semiformula.eval_rel, Language.LT.lt]
      simp [SentenceHierarchy.lt]⟩

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
    simp [Denotation.toFormula, Matrix.succ_pred, Matrix.comp_vecCons', Semiterm.val_func, Function.realize_graph, IH]
    constructor
    · rintro ⟨e, _, he, H⟩
      rcases show e = fun x ↦ Semiterm.bVal! M v (w x) from funext he
      exact H
    · intro H
      exact ⟨fun x ↦ Semiterm.bVal! M v (w x), fun i ↦ le_bound (w i) _ _, fun i ↦ rfl, H⟩

lemma pval_atom_iff {k n} (e : Fin n → M) (p : Σᴬ[0] k) (v : Fin k → Semiterm ℒₒᵣ[T] Empty n) :
    Semiformula.PVal! M e (Denotation.atom p v) ↔ FormulaHierarchy.eval p fun i => (v i).bVal! M e := by
  simp [FormulaHierarchy.eval, Denotation.atom, Denotation.toFormula, Model.lt_succ_iff_le]
  constructor
  · rintro ⟨w, bw, hw, H⟩
    suffices : w = fun i ↦ (v i).bVal! M e
    · rcases this; exact H
    funext i
    exact pval_of_term_to_formula.mp (hw i)
  · intro H
    exact ⟨fun i ↦ (v i).bVal! M e, fun i ↦ by simp [le_bound], fun i ↦ pval_of_term_to_formula.mpr (by simp), H⟩

@[simp] lemma arithmetize_iff {n} (v : Fin n → M) (p : Semisentence ℒₒᵣ[T] n) :
    Semiformula.PVal! M v (arithmetize p) ↔ Semiformula.PVal! M v p := by
  induction p using Semiformula.rec' <;> try simp [*, Semiformula.eval_rel, Semiformula.eval_nrel, pval_atom_iff]

end semantics

end boundedLanguage

end Definability

end Arith

end LO.FirstOrder
