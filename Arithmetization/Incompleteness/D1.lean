import Arithmetization.Incompleteness.Theory

noncomputable section

open Classical

namespace LO.FirstOrder

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

namespace Derivation3

def cast (d : T ⊢₃ Γ) (h : Γ = Δ) : T ⊢₃ Δ := h ▸ d

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

lemma Sequent.quote_inj {Γ Δ : Finset (SyntacticFormula L)} : (⌜Γ⌝ : V) = ⌜Δ⌝ → Γ = Δ := fun h ↦ by
  ext p; simp [←Sequent.mem_codeIn_iff (V := V), h]

lemma Sequent.subset_of_quote_subset_quote {Γ Δ : Finset (SyntacticFormula L)} :
    (⌜Γ⌝ : V) ⊆ ⌜Δ⌝ → Γ ⊆ Δ := fun h _ hp ↦
  Sequent.mem_codeIn_iff.mp <| h <| Sequent.mem_codeIn_iff.mpr hp

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

lemma Sequent.mem_codeIn_iff' {Γ : Finset (SyntacticFormula L)} : x ∈ (⌜Γ⌝ : V) ↔ (∃ p ∈ Γ, x = ⌜p⌝) := by
  constructor
  · intro h; exact Sequent.mem_codeIn h
  · rintro ⟨p, hp, rfl⟩; simp [Sequent.mem_codeIn_iff, hp]

lemma setShift_quote (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).setShift ⌜Γ⌝ = ⌜Finset.image (Rew.hom Rew.shift) Γ⌝ := by
  apply mem_ext
  intro x; simp [mem_setShift_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Sequent.mem_codeIn hx with ⟨p, _, rfl⟩
    simp [shift_quote, Sequent.mem_codeIn_iff]
    exact ⟨p, by simpa [Sequent.mem_codeIn_iff] using hx, rfl⟩
  · intro hx
    rcases Sequent.mem_codeIn hx with ⟨p', hp', rfl⟩
    rcases by simpa using hp' with ⟨p, hp, rfl⟩
    exact ⟨⌜p⌝, by simpa [Sequent.mem_codeIn_iff] using hp, by simp [shift_quote]⟩

variable (V)

variable {T : SyntacticTheory L} [T.Delta1Definable]

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

variable {T : SyntacticTheory L} [T.Delta1Definable]

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
      (mem_coded_theory_iff.mpr hT)
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

variable [L.ConstantInhabited] {T : Theory L} [T.Delta1Definable]

theorem provable_of_provable {σ} : T ⊢! σ → (T.codeIn V).Provable ⌜σ⌝ := fun h ↦ by
  simpa using derivable_of_quote (V := V) (provable_iff_derivable3'.mp h).some

/-- Hilbert–Bernays provability condition D1 -/
theorem tprovable_of_provable {σ} : T ⊢! σ → T.tCodeIn V ⊢! ⌜σ⌝ := fun h ↦ by
  simpa [Language.Theory.TProvable.iff_provable] using provable_of_provable (V := V) h

end

section

variable {T : Theory ℒₒᵣ} [T.Delta1Definable]

theorem provableₐ_of_provable {σ} : T ⊢! σ → T.Provableₐ (⌜σ⌝ : V) := fun h ↦
  Language.Theory.Derivable.of_ss (by simp) (provable_of_provable h)

end

end LO.Arith

namespace Nat

lemma double_add_one_div_of_double (n m : ℕ) : (2 * n + 1) / (2 * m) = n / m := calc
      (2 * n + 1) / (2 * m)
    = (1 + 2 * n) / 2 / m := by simp [add_comm, Nat.div_div_eq_div_mul]
  _ = n / m := by simp [Nat.add_mul_div_left]

lemma mem_bitIndices_iff {x s : ℕ} : x ∈ s.bitIndices ↔ Odd (s / 2 ^ x) := by
  induction s using Nat.binaryRec generalizing x
  case z => simp [Nat.dvd_zero]
  case f b s ih =>
    cases b <;> simp [ih]
    · constructor
      · rintro ⟨x, hx, rfl⟩
        rw [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm], Nat.mul_div_mul_left _ _ (by simp)]
        exact hx
      · intro h
        cases' x with x
        · simp at h
        · refine ⟨x, ?_, rfl⟩
          rwa [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm], Nat.mul_div_mul_left _ _ (by simp)] at h
    · constructor
      · rintro (rfl | ⟨x, hx, rfl⟩)
        · simp
        · rw [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm], double_add_one_div_of_double]
          exact hx
      · intro h
        cases' x with x
        · simp
        · right; refine ⟨x, ?_, rfl⟩
          rwa [show 2 ^ (x + 1) = 2 * 2 ^ x by simp [Nat.pow_add_one, mul_comm], double_add_one_div_of_double] at h

end Nat

namespace LO.FirstOrder

variable {L : Language} {T : SyntacticTheory L}

end LO.FirstOrder

namespace LO.Arith

open FirstOrder Encodable

lemma mem_iff_mem_bitIndices {x s : ℕ} : x ∈ s ↔ x ∈ s.bitIndices := by
  induction s using Nat.binaryRec generalizing x
  case z => simp
  case f b s ih =>
    cases b <;> simp
    · cases' x with x <;> simp [ih]
    · cases' x with x <;> simp [ih]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

lemma Language.IsSemiterm.sound {n t : ℕ} (ht : (L.codeIn ℕ).IsSemiterm n t) : ∃ T : FirstOrder.SyntacticSemiterm L n, ⌜T⌝ = t := by
  induction t using Nat.strongRec
  case ind t ih =>
    rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · exact ⟨#⟨z, hz⟩, by simp [Semiterm.quote_bvar]⟩
    · exact ⟨&x, by simp [Semiterm.quote_fvar]⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦
        ih v.[i] (nth_lt_qqFunc_of_lt (by simp [hv.lh])) (hv.nth i.prop)
      choose v' hv' using this
      have : ∃ F, encode F = f := codeIn_func_quote_iff (V := ℕ) (L := L) (x := f) (k := k) |>.mp (by simp [hf])
      rcases this with ⟨f, rfl⟩
      refine ⟨Semiterm.func f v', ?_⟩
      simp [Semiterm.quote_func, quote_func_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩

lemma Language.IsSemiformula.sound {n p : ℕ} (h : (L.codeIn ℕ).IsSemiformula n p) : ∃ F : FirstOrder.SyntacticSemiformula L n, ⌜F⌝ = p := by
  induction p using Nat.strongRec generalizing n
  case ind p ih =>
    rcases Language.IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := codeIn_rel_quote_iff (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.rel R v', ?_⟩
      simp [Semiformula.quote_rel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := codeIn_rel_quote_iff (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.nrel R v', ?_⟩
      simp [Semiformula.quote_nrel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · exact ⟨⊤, by simp [Semiformula.quote_verum]⟩
    · exact ⟨⊥, by simp [Semiformula.quote_falsum]⟩
    · rcases ih p (by simp) hp with ⟨p, rfl⟩
      rcases ih q (by simp) hq with ⟨q, rfl⟩
      exact ⟨p ⋏ q, by simp [Semiformula.quote_and]⟩
    · rcases ih p (by simp) hp with ⟨p, rfl⟩
      rcases ih q (by simp) hq with ⟨q, rfl⟩
      exact ⟨p ⋎ q, by simp [Semiformula.quote_or]⟩
    · rcases ih p (by simp) hp with ⟨p, rfl⟩
      exact ⟨∀' p, by simp [Semiformula.quote_all]⟩
    · rcases ih p (by simp) hp with ⟨p, rfl⟩
      exact ⟨∃' p, by simp [Semiformula.quote_ex]⟩

lemma isFormulaSet_sound {s : ℕ} : (L.codeIn ℕ).IsFormulaSet s → ∃ S : Finset (SyntacticFormula L), ⌜S⌝ = s := by
  intro h
  have : ∀ x, ∃ p : SyntacticFormula L, x ∈ s → ⌜p⌝ = x := by
    intro x;
    by_cases hx : x ∈ s <;> simp [hx]
    exact (h x hx).sound
  choose ps hps using this
  exact ⟨(s.bitIndices.map ps).toFinset, by
    apply mem_ext
    intro x
    constructor
    · intro h
      rcases Derivation3.Sequent.mem_codeIn h with ⟨p, hp, rfl⟩
      rcases by simpa using hp with ⟨x, hx, rfl⟩
      simpa [hps x (mem_iff_mem_bitIndices.mpr hx)] using mem_iff_mem_bitIndices.mpr hx
    · intro h
      rw [←hps x h]
      simp [Derivation3.Sequent.mem_codeIn_iff, ←mem_iff_mem_bitIndices]
      exact ⟨x, h, rfl⟩⟩

section

variable {T : SyntacticTheory L} [T.Delta1Definable]

open Derivation3

lemma Language.Theory.Derivation.sound {d : ℕ} (h : (T.codeIn ℕ).Derivation d) : ∃ Γ, ⌜Γ⌝ = fstIdx d ∧ T ⊢₃! Γ := by
  induction d using Nat.strongRec
  case ind d ih =>
  rcases h.case with ⟨hs, H⟩
  rcases isFormulaSet_sound hs with ⟨Γ, hΓ⟩
  refine ⟨Γ, hΓ, ?_⟩
  rcases H with (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, p, q, dp, dq, rfl, hpq, ⟨hp, hdp⟩, ⟨hq, hdq⟩⟩ | ⟨s, p, q, d, rfl, hpq, ⟨h, hd⟩⟩ |
    ⟨s, p, d, rfl, hps, hd, dd⟩ | ⟨s, p, t, d, rfl, hps, ht, hd, dd⟩ |
    ⟨s, d, rfl, hs, dd⟩ | ⟨s, d, rfl, rfl, dd⟩ |
    ⟨s, p, d₁, d₂, rfl, ⟨h₁, dd₁⟩, ⟨h₂, dd₂⟩⟩ | ⟨s, p, rfl, hs, hT⟩)
  · rcases (hs p (by simp [hp])).sound with ⟨p, rfl⟩
    refine ⟨Derivation3.closed Γ p
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ, hp])
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ, hp, ←neg_quote, hnp])⟩
  · refine ⟨Derivation3.verum (by simp [←Sequent.mem_codeIn_iff (V := ℕ), hΓ, Semiformula.quote_verum, hv])⟩
  · have fpq : (L.codeIn ℕ).IsFormula p ∧ (L.codeIn ℕ).IsFormula q := by simpa using hs (p ^⋏ q) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨p, rfl⟩
    rcases fpq.2.sound with ⟨q, rfl⟩
    rcases ih dp (by simp) hdp with ⟨Γp, hΓp, ⟨bp⟩⟩
    rcases ih dq (by simp) hdq with ⟨Γq, hΓq, ⟨bq⟩⟩
    refine ⟨Derivation3.and (p := p) (q := q)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_and, hpq])
      (bp.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓp, hp]))
      (bq.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓq, hq]))⟩
  · have fpq : (L.codeIn ℕ).IsFormula p ∧ (L.codeIn ℕ).IsFormula q := by simpa using hs (p ^⋎ q) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨p, rfl⟩
    rcases fpq.2.sound with ⟨q, rfl⟩
    rcases ih d (by simp) hd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation3.or (p := p) (q := q)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_or, hpq])
      (b.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΔ, h]))⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsSemiformula 1 p := by simpa using hs (^∀ p) (by simp [hps])
    rcases this.sound with ⟨p, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation3.all (p := p)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_all, hps])
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by simp [hΔ, hd, ←free_quote, setShift_quote])⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsSemiformula 1 p := by simpa using hs (^∃ p) (by simp [hps])
    rcases this.sound with ⟨p, rfl⟩
    rcases ht.sound with ⟨t, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation3.ex (p := p)
      (by simp [←Sequent.mem_codeIn_iff (V := ℕ), Semiformula.quote_ex, hps]) t
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by simp [hΔ, hd, ←substs_quote, Language.substs₁])⟩
  · rcases by simpa using hΓ
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation3.wk (Δ := Δ) b
      (Sequent.subset_of_quote_subset_quote (V := ℕ) <| by simp [hΔ, hs])⟩
  · rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    have : Γ = Finset.image (Rew.hom Rew.shift) Δ :=
      Sequent.quote_inj <| by simpa [←hΔ, setShift_quote] using hΓ
    rcases this
    refine ⟨Derivation3.shift b⟩
  · rcases by simpa using hΓ
    have : (L.codeIn ℕ).IsFormula p := dd₁.isFormulaSet p (by simp [h₁])
    rcases this.sound with ⟨p, rfl⟩
    rcases ih d₁ (by simp) dd₁ with ⟨Δ₁, hΔ₁, ⟨b₁⟩⟩
    have : Δ₁ = (p ⫽ Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₁, h₁]
    rcases this
    rcases ih d₂ (by simp) dd₂ with ⟨Δ₂, hΔ₂, ⟨b₂⟩⟩
    have : Δ₂ = (~p ⫽ Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₂, h₂, neg_quote]
    rcases this
    refine ⟨Derivation3.cut b₁ b₂⟩
  · rcases by simpa using hΓ
    rcases Sequent.mem_codeIn hs with ⟨p, hp, rfl⟩
    refine ⟨Derivation3.root p (mem_coded_theory_iff.mp hT) hp⟩

lemma Language.Theory.Provable.sound {p : SyntacticFormula L} (h : (T.codeIn ℕ).Provable ⌜p⌝) : T ⊢₃.! p := by
  rcases h with ⟨d, hp, hd⟩
  rcases hd.sound with ⟨Γ, e, b⟩
  have : Γ = {p} := Sequent.quote_inj (V := ℕ) <| by simp [e, hp]
  rcases this
  exact b

end

variable [L.ConstantInhabited] {T : Theory L} [T.Delta1Definable]

lemma Language.Theory.Provable.sound' {σ : Sentence L} (h : (T.codeIn ℕ).Provable ⌜σ⌝) : T ⊢! σ :=
  provable_iff_derivable3'.mpr <| Language.Theory.Provable.sound (p := Rew.emb.hom σ) (by simpa using h)

end LO.Arith
