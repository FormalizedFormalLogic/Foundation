import Foundation.FirstOrder.Internal.Syntax.Proof.Typed

namespace LO.FirstOrder

open Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]

variable {T : Theory L} [T.Δ₁]

namespace Derivation2

variable (V)

def cast [L.DecidableEq] {T : Theory L} (d : T ⊢₂ Γ) (h : Γ = Δ) : T ⊢₂ Δ := h ▸ d

noncomputable def Sequent.quote (Γ : Finset (SyntacticFormula L)) : V := ∑ φ ∈ Γ, Exp.exp (⌜φ⌝ : V)

noncomputable instance : GoedelQuote (Finset (SyntacticFormula L)) V := ⟨Sequent.quote V⟩

omit [L.DecidableEq] in
lemma Sequent.quote_def (Γ : Finset (SyntacticFormula L)) : ⌜Γ⌝ = ∑ φ ∈ Γ, Exp.exp (⌜φ⌝ : V) := rfl

variable {V}

omit [L.DecidableEq] in
@[simp] lemma Sequent.quote_empty : (⌜(∅ : Finset (SyntacticFormula L))⌝ : V) = ∅ := by
  simp [Sequent.quote_def, emptyset_def]

@[simp] lemma Sequent.mem_quote_iff {Γ : Finset (SyntacticFormula L)} {φ} : ⌜φ⌝ ∈ (⌜Γ⌝ : V) ↔ φ ∈ Γ := by
  induction Γ using Finset.induction generalizing φ
  case empty => simp [Sequent.quote_def]
  case insert a Γ ha ih =>
    have : Exp.exp ⌜a⌝ + ∑ φ ∈ Γ, Exp.exp (⌜φ⌝ : V) = insert (⌜a⌝ : V) (⌜Γ⌝ : V) := by
      suffices ∑ φ ∈ Γ, Exp.exp ⌜φ⌝ = ⌜Γ⌝ by
        simpa [insert, bitInsert, (not_iff_not.mpr ih.symm).mp ha, add_comm]
      rw [Sequent.quote_def]
    simp only [quote_def, ha, not_false_eq_true, Finset.sum_insert, Finset.mem_insert]
    rw [this]
    simp [←ih]

lemma Sequent.quote_inj {Γ Δ : Finset (SyntacticFormula L)} : (⌜Γ⌝ : V) = ⌜Δ⌝ → Γ = Δ := fun h ↦ by
  ext φ; rw [←Sequent.mem_quote_iff (V := V), h]; simp

omit [L.DecidableEq] in
@[simp] lemma Sequent.quote_singleton [L.DecidableEq] (φ : SyntacticFormula L) :
    (⌜({φ} : Finset (SyntacticFormula L))⌝ : V) = {⌜φ⌝} := by simp [Sequent.quote_def]; rfl

omit [L.DecidableEq] in
@[simp] lemma Sequent.quote_insert [L.DecidableEq] (Γ : Finset (SyntacticFormula L)) (φ) : (⌜(insert φ Γ)⌝ : V) = insert ⌜φ⌝ ⌜Γ⌝ := by
  by_cases hp : φ ∈ Γ
  · simp [Sequent.mem_quote_iff, hp, insert_eq_self_of_mem]
  · have : (⌜insert φ Γ⌝ : V) = Exp.exp ⌜φ⌝ + ⌜Γ⌝ := by simp [Sequent.quote_def, hp]
    simp [Sequent.mem_quote_iff, this, insert_eq, bitInsert, hp, add_comm]

omit [L.DecidableEq] in
lemma Sequent.mem_quote [L.DecidableEq] {Γ : Finset (SyntacticFormula L)} (hx : x ∈ (⌜Γ⌝ : V)) : ∃ φ ∈ Γ, x = ⌜φ⌝ := by
  induction Γ using Finset.induction
  case empty => simp at hx
  case insert a Γ _ ih =>
    have : x = ⌜a⌝ ∨ x ∈ (⌜Γ⌝ : V) := by simpa using hx
    rcases this with (rfl | hx)
    · exact ⟨a, by simp⟩
    · rcases ih hx with ⟨p, hx, rfl⟩
      exact ⟨p, by simp [*]⟩

lemma Sequent.mem_quote_iff' {Γ : Finset (SyntacticFormula L)} : x ∈ (⌜Γ⌝ : V) ↔ (∃ φ ∈ Γ, x = ⌜φ⌝) := by
  constructor
  · intro h; exact Sequent.mem_quote h
  · rintro ⟨p, hp, rfl⟩; simp [Sequent.mem_quote_iff, hp]

@[simp] lemma Sequent.quote_subset_quote {Γ Δ : Finset (SyntacticFormula L)} :
    (⌜Γ⌝ : V) ⊆ ⌜Δ⌝ ↔ Γ ⊆ Δ :=
  ⟨fun h _ hp ↦
    Sequent.mem_quote_iff.mp <| h <| Sequent.mem_quote_iff.mpr hp,
    fun h x hx ↦ by rcases Sequent.mem_quote hx with ⟨φ, hφ, rfl⟩; simp [h hφ]⟩

lemma setShift_quote (Γ : Finset (SyntacticFormula L)) :
    setShift L (⌜Γ⌝ : V) = ⌜Finset.image Rewriting.shift Γ⌝ := by
  apply mem_ext
  intro x; simp only [mem_setShift_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Sequent.mem_quote hx with ⟨p, _, rfl⟩
    rw [←Semiformula.quote_shift, Sequent.mem_quote_iff]
    simpa using ⟨p, by simpa [Sequent.mem_quote_iff] using hx, rfl⟩
  · intro hx
    rcases Sequent.mem_quote hx with ⟨p', hp', rfl⟩
    rcases by simpa using hp' with ⟨p, hp, rfl⟩
    exact ⟨⌜p⌝, by simpa [Sequent.mem_quote_iff] using hp, by simp [Semiformula.quote_def]⟩

@[simp] lemma formulaSet_quote_finset (Γ : Finset (SyntacticFormula L)) : IsFormulaSet L (⌜Γ⌝ : V) := by
  intro x hx
  rcases Derivation2.Sequent.mem_quote hx with ⟨p, _, rfl⟩
  simp [Semiformula.quote_def]

noncomputable instance : GoedelQuote (Finset (SyntacticFormula L)) (Metamath.Sequent V L) := ⟨fun Γ ↦ ⟨⌜Γ⌝, by simp⟩⟩

@[simp] lemma Sequent.typed_quote_val (Γ : Finset (SyntacticFormula L)) : (⌜Γ⌝ : Metamath.Sequent V L).val = ⌜Γ⌝ := rfl

@[simp] lemma Sequent.quote_mem_quote {φ : SyntacticFormula L} {Γ : Finset (SyntacticFormula L)} :
    ⌜φ⌝ ∈ (⌜Γ⌝ : Metamath.Sequent V L) ↔ φ ∈ Γ := by simp [Metamath.Sequent.mem_iff, ←Semiformula.quote_def]

@[simp] lemma Sequent.typed_quote_insert (Γ : Finset (SyntacticFormula L)) (φ) : (⌜insert φ Γ⌝ : Metamath.Sequent V L) = insert ⌜φ⌝ ⌜Γ⌝ := by
  ext; simp [Metamath.Sequent.mem_iff, Semiformula.quote_def]

@[simp] lemma Sequent.typed_quote_empty : (⌜(∅ : Finset (SyntacticFormula L))⌝ : Metamath.Sequent V L) = ∅ := rfl

@[simp] lemma Sequent.typed_quote_singleton (φ : SyntacticFormula L) :
    (⌜({φ} : Finset (SyntacticFormula L))⌝ : Metamath.Sequent V L) = {⌜φ⌝} := by
  rw [show ({φ} : Finset (SyntacticFormula L)) = insert φ ∅ by simp]
  rw [Sequent.typed_quote_insert]
  simp [Sequent.insert_empty_eq_singleton]

@[simp] lemma setShift_typed_quote (Γ : Finset (SyntacticFormula L)) :
    (⌜Finset.image Rewriting.shift Γ⌝ : Metamath.Sequent V L) = (⌜Γ⌝ : Metamath.Sequent V L).shift := by
  apply Sequent.ext'
  simp [←setShift_quote]; rfl

lemma Sequent.typed_quote_inj {Γ Δ : Finset (SyntacticFormula L)} : (⌜Γ⌝ : Metamath.Sequent V L) = ⌜Δ⌝ → Γ = Δ := fun h ↦ by
  have : (⌜Γ⌝ : V) = ⌜Δ⌝ := by simpa using congr_arg Sequent.val h
  exact quote_inj this

lemma Sequent.coe_eq (Γ : Finset (SyntacticFormula L)) : (↑(⌜Γ⌝ : ℕ) : V) = ⌜Γ⌝ := by
  induction Γ using Finset.induction
  · simp
  case insert φ s h ih =>
    simp [insert_absolute, ih, Semiformula.coe_quote_eq_quote]

@[simp] lemma Sequent.typed_quote_subset_typed_quote {Γ Δ : Finset (SyntacticFormula L)} :
    (⌜Γ⌝ : Metamath.Sequent V L) ⊆ ⌜Δ⌝ ↔ Γ ⊆ Δ := Sequent.quote_subset_quote

lemma isFormulaSet_sound {s : ℕ} : IsFormulaSet L s → ∃ S : Finset (SyntacticFormula L), ⌜S⌝ = s := by
  intro h
  have : ∀ x, ∃ φ : SyntacticFormula L, x ∈ s → ⌜φ⌝ = x := by
    intro x
    by_cases hx : x ∈ s
    · simpa [hx] using (h x hx).sound
    · simp [hx]
  choose ps hps using this
  exact ⟨(s.bitIndices.map ps).toFinset, by
    apply mem_ext
    intro x
    constructor
    · intro h
      rcases Derivation2.Sequent.mem_quote h with ⟨p, hp, rfl⟩
      rcases by simpa using hp with ⟨x, hx, rfl⟩
      simpa [hps x (mem_iff_mem_bitIndices.mpr hx)] using mem_iff_mem_bitIndices.mpr hx
    · intro h
      rw [←hps x h]
      simpa [Derivation2.Sequent.mem_quote_iff, ←mem_iff_mem_bitIndices] using ⟨x, h, rfl⟩⟩

variable (V)

noncomputable def typedQuote {Γ : Finset (SyntacticFormula L)} : T ⊢₂ Γ → T.internalize V ⊢ᵈᵉʳ ⌜Γ⌝
  |   closed Δ φ h hn => TDerivation.em ⌜φ⌝ (by simpa) (by simpa using Sequent.quote_mem_quote.mpr hn)
  |       root φ hT _ => TDerivation.byAxm ⌜φ⌝ (by simp [tmem, hT]) (by simpa)
  |           verum h => TDerivation.verum (by simpa using Sequent.quote_mem_quote.mpr h)
  |       and h bp bq =>
    TDerivation.and' (by simpa using Sequent.quote_mem_quote.mpr h) (bp.typedQuote.cast (by simp)) (bq.typedQuote.cast (by simp))
  |            or h b =>
    TDerivation.or' (by simpa using Sequent.quote_mem_quote.mpr h) <| b.typedQuote.cast (by simp)
  |           all h d =>
    TDerivation.all' (by simpa using Sequent.quote_mem_quote.mpr h) <| d.typedQuote.cast (by simp)
  |          ex h t d =>
    TDerivation.ex' (by simpa using Sequent.quote_mem_quote.mpr h) ⌜t⌝ <| d.typedQuote.cast (by simp [Matrix.constant_eq_singleton])
  |           wk d ss => TDerivation.wk d.typedQuote (by simpa)
  |           shift d => (TDerivation.shift d.typedQuote).cast (by simp)
  | cut (φ := φ) d dn =>
    TDerivation.cut (φ := ⌜φ⌝) (d.typedQuote.cast (by simp)) (dn.typedQuote.cast (by simp))

noncomputable instance (Γ : Finset (SyntacticFormula L)) : GoedelQuote (T ⊢₂ Γ) (T.internalize V ⊢ᵈᵉʳ ⌜Γ⌝) := ⟨typedQuote V⟩

noncomputable instance (Γ : Finset (SyntacticFormula L)) : GoedelQuote (T ⊢₂ Γ) V := ⟨fun d ↦ (⌜d⌝ : T.internalize V ⊢ᵈᵉʳ ⌜Γ⌝).val⟩

lemma quote_def (d : T ⊢₂ Γ) : (⌜d⌝ : V) = (⌜d⌝ : T.internalize V ⊢ᵈᵉʳ ⌜Γ⌝).val := rfl

lemma coe_typedQuote_val_eq (d : T ⊢₂ Γ) : ↑(d.typedQuote ℕ).val = (d.typedQuote V).val :=
  match d with
  |   closed Δ φ h hn => by
    simp [typedQuote, axL, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote']
  |       root φ hT _ => by
    simp [typedQuote, Metamath.root, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote']
  |           verum h => by
    simp [typedQuote, Metamath.verumIntro, nat_cast_pair, Sequent.coe_eq]
  |       and h b₁ b₂ => by
    simp [typedQuote, Metamath.andIntro, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote',
      b₁.coe_typedQuote_val_eq, b₂.coe_typedQuote_val_eq]
  |            or h b => by
    simp [typedQuote, Metamath.orIntro, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote',
      b.coe_typedQuote_val_eq]
  |           all h b => by
    simp [typedQuote, Metamath.allIntro, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote',
      b.coe_typedQuote_val_eq]
  |          ex h t b => by
    simp [typedQuote, Metamath.exIntro, nat_cast_pair, Sequent.coe_eq,
      Semiterm.coe_quote_eq_quote', Semiformula.coe_quote_eq_quote',
      b.coe_typedQuote_val_eq]
  |           wk b ss => by
    simp [typedQuote, Metamath.wkRule, nat_cast_pair, Sequent.coe_eq, b.coe_typedQuote_val_eq]
  |           shift b => by
    simp [typedQuote, Metamath.shiftRule, nat_cast_pair, Sequent.coe_eq,
      b.coe_typedQuote_val_eq, ←setShift_typed_quote]
  |       cut b₁ b₂ => by
    simp [typedQuote, Metamath.cutRule, nat_cast_pair, Sequent.coe_eq, Semiformula.coe_quote_eq_quote',
      b₁.coe_typedQuote_val_eq, b₂.coe_typedQuote_val_eq]

lemma coe_quote_eq (d : T ⊢₂ Γ) : (↑(⌜d⌝ : ℕ) : V) = ⌜d⌝ := coe_typedQuote_val_eq V d

end Derivation2

noncomputable instance (Γ : Sequent L) : GoedelQuote (T ⟹ Γ) V := ⟨fun b ↦ ⌜Derivation.toDerivation2 T b⌝⟩

noncomputable instance (φ : SyntacticFormula L) : GoedelQuote (T ⊢ φ) V := ⟨fun b ↦
  let b : T ⟹ [φ] := b
  ⌜b⌝⟩

lemma quote_derivation_def {Γ : Sequent L} (b : T ⟹ Γ) : (⌜b⌝ : V) = ⌜Derivation.toDerivation2 T b⌝ := rfl

lemma quote_proof_def {φ : SyntacticFormula L} (b : T ⊢ φ) : (⌜b⌝ : V) = ⌜Derivation.toDerivation2 T b⌝ := rfl

@[simp] lemma derivation_of_quote_derivation {Γ : Sequent L} (b : T ⟹ Γ) : T.DerivationOf (⌜b⌝ : V) ⌜Γ.toFinset⌝ := by
  let x := Derivation2.typedQuote V (Derivation.toDerivation2 T b)
  suffices T.DerivationOf x.val ⌜List.toFinset Γ⌝ from this
  simpa using x.derivationOf

@[simp] lemma proof_of_quote_proof {φ : SyntacticFormula L} (b : T ⊢ φ) : T.Proof (⌜b⌝ : V) ⌜φ⌝ := by
  let x := Derivation2.typedQuote V (Derivation.toDerivation2 T b)
  suffices T.Proof x.val ⌜φ⌝ from this
  simpa using x.derivationOf

lemma coe_quote_proof_eq (d : T ⊢ φ) : (↑(⌜d⌝ : ℕ) : V) = ⌜d⌝ := by
  simp [quote_proof_def, Derivation2.coe_quote_eq]

namespace Theory

open Derivation2

lemma Derivation.sound {d : ℕ} (h : T.Derivation d) : ∃ Γ, ⌜Γ⌝ = fstIdx d ∧ T ⊢₂! Γ := by
  induction d using Nat.strongRec
  case ind d ih =>
  rcases h.case with ⟨hs, H⟩
  rcases isFormulaSet_sound hs with ⟨Γ, hΓ⟩
  refine ⟨Γ, hΓ, ?_⟩
  rcases H with (⟨s, φ, rfl, hφ, hnp⟩ | ⟨s, rfl, hv⟩ |
    ⟨s, φ, ψ, dp, dq, rfl, hpq, ⟨hφ, hdφ⟩, ⟨hψ, hdq⟩⟩ | ⟨s, φ, ψ, d, rfl, hpq, ⟨h, hd⟩⟩ |
    ⟨s, φ, d, rfl, hps, hd, dd⟩ | ⟨s, φ, t, d, rfl, hps, ht, hd, dd⟩ |
    ⟨s, d, rfl, hs, dd⟩ | ⟨s, d, rfl, rfl, dd⟩ |
    ⟨s, φ, d₁, d₂, rfl, ⟨h₁, dd₁⟩, ⟨h₂, dd₂⟩⟩ | ⟨s, φ, rfl, hs, hT⟩)
  · rcases (hs φ (by simp [hφ])).sound with ⟨φ, rfl⟩
    refine ⟨Derivation2.closed Γ φ
      (by simp [←Sequent.mem_quote_iff (V := ℕ), hΓ, hφ])
      (by simpa [←Sequent.mem_quote_iff (V := ℕ), hΓ, Semiformula.quote_def] using hnp)⟩
  · refine ⟨Derivation2.verum (by simp [←Sequent.mem_quote_iff (V := ℕ), hΓ, hv])⟩
  · have fpq : IsFormula L φ ∧ IsFormula L ψ := by simpa using hs (φ ^⋏ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih dp (by simp) hdφ with ⟨Γφ, hΓφ, ⟨bφ⟩⟩
    rcases ih dq (by simp) hdq with ⟨Γψ, hΓψ, ⟨bψ⟩⟩
    refine ⟨Derivation2.and (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), hpq])
      (bφ.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓφ, hφ]))
      (bψ.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΓψ, hψ]))⟩
  · have fpq : IsFormula L φ ∧ IsFormula L ψ := by simpa using hs (φ ^⋎ ψ) (by simp [hpq])
    rcases by simpa using hΓ
    rcases fpq.1.sound with ⟨φ, rfl⟩
    rcases fpq.2.sound with ⟨ψ, rfl⟩
    rcases ih d (by simp) hd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.or (φ := φ) (ψ := ψ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_or, hpq])
      (b.cast <| Sequent.quote_inj (V := ℕ) (by simp [hΔ, h]))⟩
  · rcases by simpa using hΓ
    have : IsSemiformula L 1 φ := by simpa using hs (^∀ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.all (φ := φ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_all, hps])
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by simp [hΔ, hd, setShift_quote, Semiformula.quote_def])⟩
  · rcases by simpa using hΓ
    have : IsSemiformula L 1 φ := by simpa using hs (^∃ φ) (by simp [hps])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ht.sound with ⟨t, rfl⟩
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.ex (φ := φ)
      (by simp [←Sequent.mem_quote_iff (V := ℕ), Semiformula.quote_ex, hps]) t
      (b.cast <| Sequent.quote_inj (V := ℕ) <| by
        simp [hΔ, hd, substs1, Matrix.constant_eq_singleton, Semiformula.quote_def, Semiterm.quote_def])⟩
  · rcases by simpa using hΓ
    rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    refine ⟨Derivation2.wk (Δ := Δ) b
      ((Sequent.quote_subset_quote (V := ℕ)).mp <| by simp [hΔ, hs])⟩
  · rcases ih d (by simp) dd with ⟨Δ, hΔ, ⟨b⟩⟩
    have : Γ = Finset.image Rewriting.shift Δ :=
      Sequent.quote_inj <| by simpa [←hΔ, setShift_quote] using hΓ
    rcases this
    refine ⟨Derivation2.shift b⟩
  · rcases by simpa using hΓ
    have : IsFormula L φ := dd₁.isFormulaSet φ (by simp [h₁])
    rcases this.sound with ⟨φ, rfl⟩
    rcases ih d₁ (by simp) dd₁ with ⟨Δ₁, hΔ₁, ⟨b₁⟩⟩
    have : Δ₁ = (φ ⫽ Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₁, h₁]
    rcases this
    rcases ih d₂ (by simp) dd₂ with ⟨Δ₂, hΔ₂, ⟨b₂⟩⟩
    have : Δ₂ = (∼φ ⫽ Γ) := Sequent.quote_inj (V := ℕ) <| by simp [hΔ₂, h₂, Semiformula.quote_def]
    rcases this
    refine ⟨Derivation2.cut b₁ b₂⟩
  · rcases by simpa using hΓ
    rcases Sequent.mem_quote hs with ⟨φ, hφ, rfl⟩
    refine ⟨Derivation2.root φ (by simpa using hT) hφ⟩

lemma Provable.sound2 {φ : SyntacticFormula L} (h : T.Provable (⌜φ⌝ : ℕ)) : T ⊢₂.! φ := by
  rcases h with ⟨d, hp, hd⟩
  rcases hd.sound with ⟨Γ, e, b⟩
  have : Γ = {φ} := Sequent.quote_inj (V := ℕ) <| by simp [e, hp]
  rcases this
  exact b

lemma Provable.sound {φ : SyntacticFormula L} (h : T.Provable (⌜φ⌝ : ℕ)) : T ⊢! φ :=
  provable_iff_derivable2.mpr <| Theory.Provable.sound2 (by simpa using h)

lemma Provable.smallSound {σ : Sentence L} (h : T.Provable (⌜σ⌝ : ℕ)) : T ⊢! ↑σ :=
  provable_iff_derivable2.mpr <| Theory.Provable.sound2 (by simpa using h)

end Theory

end LO.FirstOrder
