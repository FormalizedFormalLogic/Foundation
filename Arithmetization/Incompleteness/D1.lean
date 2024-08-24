import Arithmetization.Incompleteness.Theory

noncomputable section

open Classical

namespace LO.FirstOrder

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

namespace Derivation3

def Sequent.codeIn (Γ : Finset (SyntacticFormula L)) : V := ∑ p ∈ Γ, exp (⌜p⌝ : V)

instance : GoedelQuote (Finset (SyntacticFormula L)) V := ⟨Sequent.codeIn V⟩

lemma Sequent.codeIn_def (Γ : Finset (SyntacticFormula L)) : ⌜Γ⌝ = ∑ p ∈ Γ, exp (⌜p⌝ : V) := rfl

variable {V}

open Classical

@[simp] lemma Sequent.codeIn_empty : (⌜(∅ : Finset (SyntacticFormula L))⌝ : V) = ∅ := by
  simp [Sequent.codeIn_def, emptyset_def]

lemma Sequent.mem_codeIn_iff {Γ : Finset (SyntacticFormula L)} {p} : ⌜p⌝ ∈ (⌜Γ⌝ : V) ↔ p ∈ Γ := by
  induction Γ using Finset.induction generalizing p
  case empty => simp [Sequent.codeIn_def]
  case insert a Γ ha ih =>
    have : exp ⌜a⌝ + ∑ p ∈ Γ, exp (⌜p⌝ : V) = insert (⌜a⌝ : V) (⌜Γ⌝ : V) := by
      simp [insert, bitInsert, (not_iff_not.mpr ih.symm).mp ha, add_comm]
      rw [Sequent.codeIn_def]
    simp [ha, Sequent.codeIn_def]
    rw [this]
    simp [←ih]

@[simp] lemma Sequent.codeIn_singleton (p : SyntacticFormula L) :
    (⌜({p} : Finset (SyntacticFormula L))⌝ : V) = {⌜p⌝} := by simp [Sequent.codeIn_def]; rfl

@[simp] lemma Sequent.codeIn_insert (Γ : Finset (SyntacticFormula L)) (p) : (⌜(insert p Γ)⌝ : V) = insert ⌜p⌝ ⌜Γ⌝ := by
  by_cases hp : p ∈ Γ
  · simp [Sequent.mem_codeIn_iff, hp, insert_eq_self_of_mem]
  · have : (⌜insert p Γ⌝ : V) = exp ⌜p⌝ + ⌜Γ⌝ := by simp [Sequent.codeIn_def, hp]
    simp [Sequent.mem_codeIn_iff, this, insert_eq, bitInsert, hp, add_comm]

lemma Sequent.mem_codeIn {Γ : Finset (SyntacticFormula L)} (hx : x ∈ (⌜Γ⌝ : V)) : ∃ p ∈ Γ, x = ⌜p⌝ := by
  induction Γ using Finset.induction
  case empty => simp at hx
  case insert a Γ _ ih =>
    have : x = ⌜a⌝ ∨ x ∈ (⌜Γ⌝ : V) := by simpa using hx
    rcases this with (rfl | hx)
    · exact ⟨a, by simp⟩
    · rcases ih hx with ⟨p, hx, rfl⟩
      exact ⟨p, by simp [*]⟩

variable (V)

variable {T : SyntacticTheory L} [T.Δ₁Definable]

def codeIn : {Γ : Finset (SyntacticFormula L)} → T ⊢₃ Γ → V
  | _, closed Δ p _ _                         => Arith.axL ⌜Δ⌝ ⌜p⌝
  | _, root (Δ := Δ) p _ _                    => Arith.root ⌜Δ⌝ ⌜p⌝
  | _, verum (Δ := Δ) _                       => Arith.verumIntro ⌜Δ⌝
  | _, and (Δ := Δ) _ (p := p) (q := q) bp bq => Arith.andIntro ⌜Δ⌝ ⌜p⌝ ⌜q⌝ bp.codeIn bq.codeIn
  | _, or (Δ := Δ) (p := p) (q := q) _ d      => Arith.orIntro ⌜Δ⌝ ⌜p⌝ ⌜q⌝ d.codeIn
  | _, all (Δ := Δ) (p := p) _ d              => Arith.allIntro ⌜Δ⌝ ⌜p⌝ d.codeIn
  | _, ex (Δ := Δ) (p := p) _ t d             => Arith.exIntro ⌜Δ⌝ ⌜p⌝ ⌜t⌝ d.codeIn
  | _, wk (Γ := Γ) d _                        => Arith.wkRule ⌜Γ⌝ d.codeIn
  | _, shift (Δ := Δ) d                       => Arith.shiftRule ⌜Δ.image Rew.shift.hom⌝ d.codeIn
  | _, cut (Δ := Δ) (p := p) d dn             => Arith.cutRule ⌜Δ⌝ ⌜p⌝ d.codeIn dn.codeIn

instance (Γ : Finset (SyntacticFormula L)) : GoedelQuote (T ⊢₃ Γ) V := ⟨codeIn V⟩

lemma quote_derivation_def {Γ : Finset (SyntacticFormula L)} (d : T ⊢₃ Γ) : (⌜d⌝ : V) = d.codeIn V := rfl

@[simp] lemma fstidx_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₃ Γ) : fstIdx (⌜d⌝ : V) = ⌜Γ⌝ := by
  induction d <;> simp [quote_derivation_def, codeIn]

end Derivation3

end LO.FirstOrder

namespace LO.Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable {T : SyntacticTheory L} [T.Δ₁Definable]

open Classical

@[simp] lemma formulaSet_codeIn_finset (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).IsFormulaSet ⌜Γ⌝ := by
  intro x hx
  rcases Derivation3.Sequent.mem_codeIn hx with ⟨p, _, rfl⟩;
  apply semiformula_quote (n := 0)

open Derivation3

lemma quote_image_shift (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).setShift (⌜Γ⌝ : V) = ⌜Γ.image Rew.shift.hom⌝ := by
  induction Γ using Finset.induction
  case empty => simp
  case insert p Γ _ ih => simp [shift_quote, ih]

@[simp] lemma derivation_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₃ Γ) : (T.codeIn V).Derivation ⌜d⌝ := by
  induction d
  case closed p hp hn =>
    exact Language.Theory.Derivation.axL (by simp)
      (by simp [Sequent.mem_codeIn_iff, hp])
      (by simp [Sequent.mem_codeIn_iff, neg_quote, hn])
  case root Δ p hT hp =>
    apply Language.Theory.Derivation.root (by simp)
      (by simp [Sequent.mem_codeIn_iff, hp])
      (mem_coded_theory hT)
  case verum Δ h =>
    exact Language.Theory.Derivation.verumIntro (by simp)
      (by simpa [quote_verum] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
  case and Δ p q hpq dp dq ihp ihq =>
    apply Language.Theory.Derivation.andIntro
      (by simpa [quote_and] using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ihp⟩
      ⟨by simp [fstidx_quote], ihq⟩
  case or Δ p q hpq d ih =>
    apply Language.Theory.Derivation.orIntro
      (by simpa [quote_or] using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ih⟩
  case all Δ p h d ih =>
    apply Language.Theory.Derivation.allIntro
      (by simpa [quote_all] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      ⟨by simp [fstidx_quote, quote_image_shift, free_quote], ih⟩
  case ex Δ p h t d ih =>
    apply Language.Theory.Derivation.exIntro
      (by simpa [quote_ex] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      (semiterm_codeIn t)
      ⟨by simp [fstidx_quote, ←substs_quote, Language.substs₁], ih⟩
  case wk Δ Γ d h ih =>
    apply Language.Theory.Derivation.wkRule (s' := ⌜Δ⌝)
      (by simp)
      (by intro x hx; rcases Sequent.mem_codeIn hx with ⟨p, hp, rfl⟩
          simp [Sequent.mem_codeIn_iff, h hp])
      ⟨by simp [fstidx_quote], ih⟩
  case shift Δ d ih =>
    simp [quote_derivation_def, Derivation3.codeIn, ←quote_image_shift]
    apply Language.Theory.Derivation.shiftRule
      ⟨by simp [fstidx_quote], ih⟩
  case cut Δ p d dn ih ihn =>
    apply Language.Theory.Derivation.cutRule
      ⟨by simp [fstidx_quote], ih⟩
      ⟨by simp [fstidx_quote, neg_quote], ihn⟩

@[simp] lemma derivationOf_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₃ Γ) : (T.codeIn V).DerivationOf ⌜d⌝ ⌜Γ⌝ :=
  ⟨by simp, by simp⟩

lemma derivable_of_quote {Γ : Finset (SyntacticFormula L)} (d : T ⊢₃ Γ) : (T.codeIn V).Derivable ⌜Γ⌝ :=
  ⟨⌜d⌝, by simp⟩

section

variable [L.ConstantInhabited] {T : Theory L} [T.Δ₁Definable]

theorem provable_of_provable {σ} : T ⊢! σ → (T.codeIn V).Provable ⌜σ⌝ := fun h ↦ by
  simpa using derivable_of_quote (V := V) (provable_iff_derivable3'.mp h).some

/-- Hilbert–Bernays provability condition D1 -/
theorem tprovable_of_provable {σ} : T ⊢! σ → T.tCodeIn V ⊢! ⌜σ⌝ := fun h ↦ by
  simpa [Language.Theory.TProvable.iff_provable] using provable_of_provable (V := V) h

end

section

variable {T : Theory ℒₒᵣ} [T.Δ₁Definable]

theorem provableₐ_of_provable {σ} : T ⊢! σ → T.Provableₐ (⌜σ⌝ : V) := fun h ↦
  Language.Theory.Derivable.of_ss (by simp) (provable_of_provable h)

end

end LO.Arith
