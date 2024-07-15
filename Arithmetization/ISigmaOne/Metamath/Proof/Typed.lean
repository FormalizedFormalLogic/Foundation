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

structure Language.Theory.TDerivation (Γ : L.Sequent) where
  antecedents : V

  derivation : V
  derivationOf : L.DerivationOf derivation Γ.val

scoped prefix:45 "⊢ₜ " => Language.TDerivation

def Language.Derivable.toTDerivation (Γ : L.Sequent) (h : L.Derivable Γ.val) : ⊢ₜ Γ := by
  choose d hd using h
  exact ⟨d, hd⟩

namespace Language.TDerivation

variable {Γ Δ : L.Sequent} {p q : L.TFormula}

protected def axL (h : p ∈ Γ) (hn : ~p ∈ Γ) : ⊢ₜ Γ where
  derivation := axL Γ.val p.val
  derivationOf := ⟨by simp, Language.Derivation.axL (by simp) h hn⟩
/--/
def verum (h : ⊤ ∈ Γ) : ⊢ₜ Γ where
  derivation := verumIntro Γ.val
  derivationOf := ⟨by simp, Language.Derivation.verumIntro (by simp) h⟩

def and_m (dp : ⊢ₜ insert p Γ) (dq : ⊢ₜ insert q Γ) (h : p ⋏ q ∈ Γ) : ⊢ₜ Γ where
  derivation := andIntro Γ.val p.val q.val dp.derivation dq.derivation
  derivationOf := ⟨by simp, Language.Derivation.andIntro h dp.derivationOf dq.derivationOf⟩

def or_m (dpq : ⊢ₜ insert p (insert q Γ)) (h : p ⋎ q ∈ Γ) : ⊢ₜ Γ where
  derivation := orIntro Γ.val p.val q.val dpq.derivation
  derivationOf := ⟨by simp, Language.Derivation.orIntro h dpq.derivationOf⟩

def all_m {p : L.TSemiformula (0 + 1)} (dp : ⊢ₜ insert p.free Γ.shift) (h : p.all ∈ Γ) : ⊢ₜ Γ where
  derivation := allIntro Γ.val p.val dp.derivation
  derivationOf := ⟨by simp, Language.Derivation.allIntro h (by simpa using dp.derivationOf)⟩

def ex_m {p : L.TSemiformula (0 + 1)} (t : L.TTerm) (dp : ⊢ₜ insert (p.substs₁ t) Γ) (h : p.ex ∈ Γ) : ⊢ₜ Γ where
  derivation := exIntro Γ.val p.val t.val dp.derivation
  derivationOf := ⟨by simp, Language.Derivation.exIntro h (by simp) dp.derivationOf⟩

def wk (d : ⊢ₜ Δ) (h : Δ ⊆ Γ) : ⊢ₜ Γ where
  derivation := wkRule Γ.val d.derivation
  derivationOf := ⟨by simp, Language.Derivation.wkRule (by simp) h d.derivationOf⟩

def cut (d₁ : ⊢ₜ insert p Γ) (d₂ : ⊢ₜ insert (~p) Γ) : ⊢ₜ Γ where
  derivation := cutRule Γ.val p.val d₁.derivation d₂.derivation
  derivationOf := ⟨by simp, Language.Derivation.cutRule d₁.derivationOf d₂.derivationOf⟩

/-- TODO: move-/
lemma insert_subset_iff_insert {s t : V} (h : s ⊆ t) (x : V) : insert x s ⊆ insert x t := by
  intro z hz
  rcases mem_bitInsert_iff.mp hz with (rfl | hz)
  · simp
  · simp [h hz]

def cut' (d₁ : ⊢ₜ insert p Γ) (d₂ : ⊢ₜ insert (~p) Δ) : ⊢ₜ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (insert_subset_iff_insert (by simp) _)) (d₂.wk (insert_subset_iff_insert (by simp) _))

def and (dp : ⊢ₜ insert p Γ) (dq : ⊢ₜ insert q Γ) : ⊢ₜ insert (p ⋏ q) Γ := and_m (p := p) (q := q)
  (dp.wk <| by intro x; simp; tauto) (dq.wk <| by intro x; simp; tauto) (by simp)

lemma toDerivable (d : ⊢ₜ Γ) : L.Derivable Γ.val := ⟨d.derivation, d.derivationOf⟩

def conj (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → ⊢ₜ insert (ps.nth i hi) Γ) : ⊢ₜ insert ps.conj Γ := by
  have : ∀ i < len ps.val, L.Derivable (insert (ps.val.[i]) Γ.val) := by intro i hi; simpa using (ds i hi).toDerivable
  have : L.Derivable (insert (^⋀ ps.val) Γ.val) := Language.Derivable.conj ps.val (by simp) this
  exact Language.Derivable.toTDerivation _ (by simpa using this)

end Language.TDerivation

end typed_derivation
