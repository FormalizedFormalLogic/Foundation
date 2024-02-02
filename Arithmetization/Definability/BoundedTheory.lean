import Arithmetization.Definability.Definability

namespace LO.FirstOrder

namespace Arith

namespace Definition

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

end realize

end BoundedFunction

def boundedLanguage (T : Theory ℒₒᵣ) : Language where
  Func := BoundedFunction T
  Rel := Σᴬ[0]

namespace boundedLanguage

def _root_.LO.FirstOrder.Arith.Definition.BoundedFunction.toFunc {k} (f : BoundedFunction T k) : (boundedLanguage T).Func k := f

def _root_.LO.FirstOrder.Arith.FormulaHierarchy.toRel {k} (r : Σᴬ[0] k) : (boundedLanguage T).Rel k := r

instance : Language.Eq (boundedLanguage T) := ⟨SentenceHierarchy.eq⟩

instance : Language.LT (boundedLanguage T) := ⟨SentenceHierarchy.lt⟩

instance : Language.Zero (boundedLanguage T) := ⟨BoundedFunction.zero⟩

instance : Language.One (boundedLanguage T) := ⟨BoundedFunction.one⟩

instance : Language.Add (boundedLanguage T) := ⟨BoundedFunction.add⟩

instance : Language.Mul (boundedLanguage T) := ⟨BoundedFunction.mul⟩

section semantics

variable {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [T.Mod M]

noncomputable instance semantics : Structure (boundedLanguage T) M where
  func := fun k (f : BoundedFunction T k) v ↦ f.function.realize v
  rel := fun k (p : Σᴬ[0] k) v ↦ Semiformula.PVal! M v p.val

@[simp] lemma semantics_func {k} (f : BoundedFunction T k) (v : Fin k → M) :
    semantics.func f v = f.function.realize v := rfl

@[simp] lemma semantics_rel {k} (p : Σᴬ[0] k) (v : Fin k → M) :
    semantics.rel (L := boundedLanguage T) p v ↔ Semiformula.PVal! M v p.val := iff_of_eq rfl

instance : Structure.Zero (boundedLanguage T) M :=
  ⟨by simp[Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Language.Zero.zero]⟩

instance : Structure.One (boundedLanguage T) M :=
  ⟨by simp[Semiterm.Operator.val, Semiterm.Operator.One.one, Language.One.one]⟩

instance : Structure.Add (boundedLanguage T) M :=
  ⟨by intro a b; simp[Semiterm.Operator.val, Semiterm.val_func, Semiterm.Operator.Add.add, Language.Add.add]⟩

instance : Structure.Mul (boundedLanguage T) M :=
  ⟨by intro a b; simp[Semiterm.Operator.val, Semiterm.val_func, Semiterm.Operator.Mul.mul, Language.Mul.mul]⟩

instance : Structure.Eq (boundedLanguage T) M :=
  ⟨by intro a b
      simp[Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel, Language.Eq.eq]
      simp [SentenceHierarchy.eq]⟩

instance : Structure.LT (boundedLanguage T) M :=
  ⟨by intro a b
      simp[Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, Semiformula.eval_rel, Language.LT.lt]
      simp [SentenceHierarchy.lt]⟩

end semantics

end boundedLanguage



end Definition




end Arith

end LO.FirstOrder
