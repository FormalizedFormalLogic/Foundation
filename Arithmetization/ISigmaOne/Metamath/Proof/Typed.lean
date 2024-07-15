import Arithmetization.ISigmaOne.Metamath.Formula.Typed
import Arithmetization.ISigmaOne.Metamath.Proof.Theory

/-!

# Typed Formalized Tait-Calculus

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section typed_formula

def Language.TSemiformula.substs₁ (p : L.TSemiformula (0 + 1)) (t : L.TTerm) : L.TFormula := p.substs (t ∷ᵗ .nil L 0)

def Language.TSemiformula.free (p : L.TSemiformula (0 + 1)) : L.TFormula := p.shift.substs₁ (L.fvar 0)

@[simp] lemma Language.TSemiformula.val_substs₁ (p : L.TSemiformula (0 + 1)) (t : L.TTerm) :
    (p.substs₁ t).val = L.substs 0 ?[t.val] p.val := by simp [substs₁, substs]

@[simp] lemma Language.TSemiformula.val_free (p : L.TSemiformula (0 + 1)) :
    p.free.val = L.substs 0 ?[^&0] (L.shift p.val) := by simp [free, substs₁, substs, shift, fvar]

end typed_formula

section typed_sequent

variable (L)

structure Language.Sequent where
  val : V
  val_formulaSet : L.FormulaSet val

attribute [simp] Language.Sequent.val_formulaSet

variable {L}

instance : EmptyCollection L.Sequent := ⟨⟨∅, by simp⟩⟩

instance : Singleton L.TFormula L.Sequent := ⟨fun p ↦ ⟨{p.val}, by simp⟩⟩

instance : Insert L.TFormula L.Sequent := ⟨fun p Γ ↦ ⟨insert p.val Γ.val, by simp⟩⟩

instance : Union L.Sequent := ⟨fun Γ Δ ↦ ⟨Γ.val ∪ Δ.val, by simp⟩⟩

instance : Membership L.TFormula L.Sequent := ⟨(·.val ∈ ·.val)⟩

instance : HasSubset L.Sequent := ⟨(·.val ⊆ ·.val)⟩

namespace Language.Sequent

variable {Γ Δ : L.Sequent} {p q : L.TFormula}

lemma mem_iff : p ∈ Γ ↔ p.val ∈ Γ.val := iff_of_eq rfl

lemma subset_iff : Γ ⊆ Δ ↔ Γ.val ⊆ Δ.val := iff_of_eq rfl

@[simp] lemma val_empty : (∅ : L.Sequent).val = ∅ := rfl

@[simp] lemma val_singleton (p : L.TFormula) : ({p} : L.Sequent).val = {p.val} := rfl

@[simp] lemma val_insert (p : L.TFormula) (Γ : L.Sequent) : (insert p Γ).val = insert p.val Γ.val := rfl

@[simp] lemma val_union (Γ Δ : L.Sequent) : (Γ ∪ Δ).val = Γ.val ∪ Δ.val := rfl

@[simp] lemma not_mem_empty (p : L.TFormula) : p ∉ (∅ : L.Sequent) := by simp [mem_iff]

@[simp] lemma mem_singleton_iff : p ∈ ({q} : L.Sequent) ↔ p = q := by simp [mem_iff, Language.TSemiformula.val_inj]

@[simp] lemma mem_insert_iff : p ∈ insert q Γ ↔ p = q ∨ p ∈ Γ := by simp [mem_iff, Language.TSemiformula.val_inj]

@[simp] lemma mem_union_iff : p ∈ Γ ∪ Δ ↔ p ∈ Γ ∨ p ∈ Δ := by simp [mem_iff, Language.TSemiformula.val_inj]

end Language.Sequent

def Language.Sequent.shift (s : L.Sequent) : L.Sequent := ⟨L.setShift s.val, by simp⟩

end typed_sequent

section typed_derivation

structure Language.Theory.TDerivation (T : L.Theory) (Γ : L.Sequent) where
  antecedents : V
  antecedents_fvFree : ∀ p ∈ antecedents, L.neg p ∈ T
  derivation : V
  derivationOf : L.DerivationOf derivation (antecedents ∪ Γ.val)

scoped infix:45 " ⊢ₜ " => Language.Theory.TDerivation

def Language.Theory.Derivable.toTDerivation {T : L.Theory} (Γ : L.Sequent) (h : T.Derivable Γ.val) : T ⊢ₜ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

def Language.Theory.TDerivation.toDerivable {T : L.Theory} {Γ : L.Sequent} (d : T ⊢ₜ Γ) : T.Derivable Γ.val :=
  ⟨d.antecedents, d.antecedents_fvFree, d.derivation, d.derivationOf⟩

namespace Language.Theory.TDerivation

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT] {Γ Δ : L.Sequent} {p q : L.TFormula}

def em (p) (h : p ∈ Γ) (hn : ~p ∈ Γ) : T ⊢ₜ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.em (by simp) p.val (Language.Sequent.mem_iff.mp h) (by simpa using Language.Sequent.mem_iff.mp hn)

def verum (h : ⊤ ∈ Γ) : T ⊢ₜ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.verum (by simp) (by simpa using Language.Sequent.mem_iff.mp h)

def and (dp : T ⊢ₜ insert p Γ) (dq : T ⊢ₜ insert q Γ) : T ⊢ₜ insert (p ⋏ q) Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| by simpa using Language.Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

def or_m (dpq : T ⊢ₜ insert p (insert q Γ)) : T ⊢ₜ insert (p ⋎ q) Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by simpa using Language.Theory.Derivable.or (by simpa using dpq.toDerivable)

def all_m {p : L.TSemiformula (0 + 1)} (dp : T ⊢ₜ insert p.free Γ.shift) : T ⊢ₜ insert p.all Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.all (by simpa using p.prop) (by simpa using dp.toDerivable)

def ex_m {p : L.TSemiformula (0 + 1)} (t : L.TTerm) (dp : T ⊢ₜ insert (p.substs₁ t) Γ) : T ⊢ₜ insert p.ex Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.ex (by simpa using p.prop) t.prop (by simpa using dp.toDerivable)

def wk (d : T ⊢ₜ Δ) (h : Δ ⊆ Γ) : T ⊢ₜ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.wk (by simp) (Language.Sequent.subset_iff.mp h) (by simpa using d.toDerivable)

def cut (d₁ : T ⊢ₜ insert p Γ) (d₂ : T ⊢ₜ insert (~p) Γ) : T ⊢ₜ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.cut p.val (by simpa using d₁.toDerivable) (by simpa using d₂.toDerivable)

def cut' (d₁ : T ⊢ₜ insert p Γ) (d₂ : T ⊢ₜ insert (~p) Δ) : T ⊢ₜ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

def conj (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ₜ insert (ps.nth i hi) Γ) : T ⊢ₜ insert ps.conj Γ := by
  have : ∀ i < len ps.val, T.Derivable (insert (ps.val.[i]) Γ.val) := by intro i hi; simpa using (ds i hi).toDerivable
  have : T.Derivable (insert (^⋀ ps.val) Γ.val) := Language.Theory.Derivable.conj ps.val (by simp) this
  exact Language.Theory.Derivable.toTDerivation _ (by simpa using this)

end Language.Theory.TDerivation

end typed_derivation
