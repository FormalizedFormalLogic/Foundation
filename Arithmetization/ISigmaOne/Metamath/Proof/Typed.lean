import Arithmetization.ISigmaOne.Metamath.Formula.Typed
import Arithmetization.ISigmaOne.Metamath.Proof.Theory
import Logic.Logic.HilbertStyle.Supplemental

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

scoped infixr:50 " ⫽ " => Insert.insert

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

@[ext] lemma ext (h : ∀ x, x ∈ Γ ↔ x ∈ Δ) : Γ = Δ := by
  rcases Γ with ⟨Γ, hΓ⟩; rcases Δ with ⟨Δ, hΔ⟩; simp
  apply mem_ext; intro x
  constructor
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΓ x hx⟩ |>.1 (by simp [mem_iff, hx]))
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΔ x hx⟩ |>.2 (by simp [mem_iff, hx]))

end Language.Sequent

def Language.Sequent.shift (s : L.Sequent) : L.Sequent := ⟨L.setShift s.val, by simp⟩

end typed_sequent

section typed_derivation

structure Language.Theory.TDerivation (T : L.Theory) (Γ : L.Sequent) where
  antecedents : V
  antecedents_fvFree : ∀ p ∈ antecedents, L.neg p ∈ T
  derivation : V
  derivationOf : L.DerivationOf derivation (antecedents ∪ Γ.val)

scoped infix:45 " ⊢¹ " => Language.Theory.TDerivation

def Language.Theory.TProof (T : L.Theory) (p : L.TFormula) := T ⊢¹ insert p ∅

instance : System L.TFormula L.Theory := ⟨Language.Theory.TProof⟩

def Language.Theory.Derivable.toTDerivation {T : L.Theory} (Γ : L.Sequent) (h : T.Derivable Γ.val) : T ⊢¹ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

def Language.Theory.TDerivation.toDerivable {T : L.Theory} {Γ : L.Sequent} (d : T ⊢¹ Γ) : T.Derivable Γ.val :=
  ⟨d.antecedents, d.antecedents_fvFree, d.derivation, d.derivationOf⟩

def Language.Theory.TDerivation.toTProof {T : L.Theory} {p} (d : T ⊢¹ insert p ∅) : T ⊢ p := d

def Language.Theory.TProof.toTDerivation {T : L.Theory} {p} (d : T ⊢ p) : T ⊢¹ insert p ∅ := d

namespace Language.Theory.TDerivation

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT] {Γ Δ : L.Sequent} {p q p₀ p₁ p₂ p₃ p₄ : L.TFormula}

def byAxm (p) (h : p.val ∈ T) (hΓ : p ∈ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.by_axm (by simp) h hΓ

def em (p) (h : p ∈ Γ := by simp) (hn : ~p ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.em (by simp) p.val (Language.Sequent.mem_iff.mp h) (by simpa using Language.Sequent.mem_iff.mp hn)

def verum (h : ⊤ ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.verum (by simp) (by simpa using Language.Sequent.mem_iff.mp h)

def and (dp : T ⊢¹ insert p Γ) (dq : T ⊢¹ insert q Γ) : T ⊢¹ insert (p ⋏ q) Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| by simpa using Language.Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

def or (dpq : T ⊢¹ insert p (insert q Γ)) : T ⊢¹ insert (p ⋎ q) Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by simpa using Language.Theory.Derivable.or (by simpa using dpq.toDerivable)

def all {p : L.TSemiformula (0 + 1)} (dp : T ⊢¹ insert p.free Γ.shift) : T ⊢¹ insert p.all Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.all (by simpa using p.prop) (by simpa using dp.toDerivable)

def ex {p : L.TSemiformula (0 + 1)} (t : L.TTerm) (dp : T ⊢¹ insert (p.substs₁ t) Γ) : T ⊢¹ insert p.ex Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.ex (by simpa using p.prop) t.prop (by simpa using dp.toDerivable)

def wk (d : T ⊢¹ Δ) (h : Δ ⊆ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.wk (by simp) (Language.Sequent.subset_iff.mp h) (by simpa using d.toDerivable)

def cut (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (~p) Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.cut p.val (by simpa using d₁.toDerivable) (by simpa using d₂.toDerivable)

def cut' (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (~p) Δ) : T ⊢¹ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

def conj (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢¹ insert (ps.nth i hi) Γ) : T ⊢¹ insert ps.conj Γ := by
  have : ∀ i < len ps.val, T.Derivable (insert (ps.val.[i]) Γ.val) := by intro i hi; simpa using (ds i hi).toDerivable
  have : T.Derivable (insert (^⋀ ps.val) Γ.val) := Language.Theory.Derivable.conj ps.val (by simp) this
  exact Language.Theory.Derivable.toTDerivation _ (by simpa using this)

def modusPonens (dpq : T ⊢¹ insert (p ⟶ q) Γ) (dp : T ⊢¹ insert p Γ) : T ⊢¹ insert q Γ := by
  let d : T ⊢¹ insert (p ⟶ q) (insert q Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢¹ insert (~(p ⟶ q)) (insert q Γ) := by
    simp only [TSemiformula.imp_def, TSemiformula.neg_or, TSemiformula.neg_neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em q (by simp) (by simp))
  exact cut d b

def ofEq (d : T ⊢¹ Γ) (h : Γ = Δ) : T ⊢¹ Δ := h ▸ d

def rotate₁ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ Γ) : T ⊢¹ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₂ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ p₂ ⫽ Γ) : T ⊢¹ p₂ ⫽ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₃ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ p₂ ⫽ p₃ ⫽ Γ) : T ⊢¹ p₃ ⫽ p₁ ⫽ p₂ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

end Language.Theory.TDerivation

namespace Language.Theory.TProof

variable {T : L.Theory} {pT : pL.TDef} [T.Defined pT] {p q : L.TFormula}

/-- Condition D1 -/
def modusPonens (d : T ⊢ p ⟶ q) (b : T ⊢ p) : T ⊢ q := TDerivation.modusPonens d b

instance : System.ModusPonens T := ⟨modusPonens⟩

instance : System.NegationEquiv T where
  neg_equiv p := by
    simp [Axioms.NegEquiv, LO.LogicalConnective.iff, TSemiformula.imp_def]
    apply TDerivation.and
    · apply TDerivation.or
      apply TDerivation.rotate₁
      apply TDerivation.or
      exact TDerivation.em p
    · apply TDerivation.or
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.verum

instance : System.Minimal T where
  verum := TDerivation.toTProof <| TDerivation.verum
  imply₁ (p q) := by
    simp only [Axioms.Imply₁, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  imply₂ (p q r) := by
    simp only [Axioms.Imply₂, TSemiformula.imp_def, TSemiformula.neg_or, TSemiformula.neg_neg]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₂
    apply TDerivation.and
    · exact TDerivation.em p
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · apply TDerivation.and
        · exact TDerivation.em q
        · exact TDerivation.em r
  and₁ (p q) := by
    simp only [Axioms.AndElim₁, TSemiformula.imp_def, TSemiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em p
  and₂ (p q) := by
    simp only [Axioms.AndElim₂, TSemiformula.imp_def, TSemiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em q
  and₃ (p q) := by
    simp only [Axioms.AndInst, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em p
    · exact TDerivation.em q
  or₁ (p q) := by
    simp only [Axioms.OrInst₁, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  or₂ (p q) := by
    simp [Axioms.OrInst₂, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em q
  or₃ (p q r) := by
    simp [Axioms.OrElim, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.and
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.em r
    · apply TDerivation.rotate₂
      apply TDerivation.and
      · exact TDerivation.em q
      · exact TDerivation.em r

instance : System.Classical T where
  dne p := by
    simp [Axioms.DNE, TSemiformula.imp_def]
    apply TDerivation.or
    exact TDerivation.em p

end Language.Theory.TProof

end typed_derivation
