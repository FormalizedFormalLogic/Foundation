module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory

@[expose] public section
/-!
# Executable recognizers for `Δ₁` axiom sets

`Theory.Δ₁` makes the axioms of `T` *arithmetically* `Δ₁`, which is what the arithmetized
provability predicate needs, but it does not make them `Decidable` in Lean: `T.Δ₁Class` unfolds to
satisfaction of a `𝚫₁` formula in `ℕ`, and the `𝚺₁` side of that has unbounded quantifiers.
Anything that has to *run* over codes — an executable derivation checker, say, whose `axm` rule
carries the side condition `p ∈ T.Δ₁Class` — needs the recognizer supplied.

`Theory.DecidableΔ₁` is that interface. `decide_iff` is stated over raw codes `p : ℕ`, not only
over `⌜σ⌝`: `Derivation.Phi`'s `axm` disjunct quantifies over arbitrary `p ∈ s`, whereas
`Δ₁Class.mem_iff` pins `Δ₁Class` down only at codes of sentences. A recognizer that decided
"`p = ⌜σ⌝` for some `σ ∈ T`" would agree with `Δ₁Class` only if `T.Δ₁ch` were sound on non-codes,
which `Theory.Δ₁` does not promise. `DecidableΔ₁.decide_quote` is the corollary, never the
definition. For the combinators below it *is* sound on non-codes (`evalb_ofList_ch`).

`Δ₁Class T` mentions `T` only through `Δ₁.ch`, so everything here is stated at the `ch` level
(`mem_Δ₁Class_iff_evalb`); that avoids having to pin the `[T.Δ₁]` instance argument branch by
branch through the `Δ₁.ofList` recursion.
-/

namespace LO.FirstOrder.Theory

open Encodable Arithmetic Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] {T U : Theory L}

/-! ### The axiom class at `V := ℕ`, at the level of `Δ₁.ch` -/

lemma mem_Δ₁Class_iff_evalb [T.Δ₁] (p : ℕ) :
    p ∈ T.Δ₁Class (V := ℕ) ↔ Semiformula.Evalb ![p] (Δ₁.ch T).val := Iff.rfl

namespace Δ₁

@[simp] lemma evalb_singleton_ch (φ : Sentence L) (p : ℕ) :
    Semiformula.Evalb ![p] (Δ₁.singleton φ).ch.val ↔ p = encode φ := by simp

lemma evalb_ofList_ch (l : List (Sentence L)) (p : ℕ) :
    Semiformula.Evalb ![p] (Δ₁.ofList l).ch.val ↔ ∃ φ ∈ l, p = encode φ := by
  induction l with
  | nil =>
    show Semiformula.Evalb ![p] (⊥ : 𝚫₁.Semisentence 1).val ↔ _
    simp
  | cons φ l ih =>
    show Semiformula.Evalb ![p] ((Δ₁.singleton φ).ch ⋎ (Δ₁.ofList l).ch).val ↔ _
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    rw [ih, evalb_singleton_ch]
    simp

lemma evalb_ofFinite_ch (T : Theory L) (h : Set.Finite T) (p : ℕ) :
    Semiformula.Evalb ![p] (Δ₁.ofFinite T h).ch.val ↔ ∃ σ ∈ T, p = encode σ := by
  rw [show (Δ₁.ofFinite T h).ch = (Δ₁.ofList h.toFinset.toList).ch from rfl, evalb_ofList_ch]
  simp

end Δ₁

/-! ### The interface -/

/-- An executable recognizer for the `Δ₁` axiom class of `T`, in the standard model.

`decide_iff` is over raw codes `p : ℕ`, not just over `⌜σ⌝`; see the module docstring. -/
class DecidableΔ₁ (T : Theory L) [T.Δ₁] where
  decide : ℕ → Bool
  decide_iff (p : ℕ) : decide p = true ↔ p ∈ T.Δ₁Class (V := ℕ)

namespace DecidableΔ₁

instance [T.Δ₁] [T.DecidableΔ₁] (p : ℕ) : Decidable (p ∈ T.Δ₁Class (V := ℕ)) :=
  decidable_of_iff _ (decide_iff (T := T) p)

/-- The corollary at codes of sentences. It is *derived* from `decide_iff`, and is deliberately not
the definition of the interface. -/
lemma decide_quote [T.Δ₁] [T.DecidableΔ₁] (σ : Sentence L) :
    decide (T := T) (encode σ) = true ↔ σ ∈ T := by
  rw [decide_iff, show (encode σ : ℕ) = (⌜σ⌝ : ℕ) from (Sentence.quote_eq_encode_standard σ).symm]
  exact Bootstrapping.Δ₁Class.mem_iff

/-! ### Instantiations mirroring the `Δ₁` combinators -/

instance empty : (∅ : Theory L).DecidableΔ₁ where
  decide _ := false
  decide_iff p := by
    rw [mem_Δ₁Class_iff_evalb]
    show false = true ↔ Semiformula.Evalb ![p] (⊥ : 𝚫₁.Semisentence 1).val
    simp

instance singleton (φ : Sentence L) : ({φ} : Theory L).DecidableΔ₁ where
  decide p := p == encode φ
  decide_iff p := by rw [mem_Δ₁Class_iff_evalb, Δ₁.evalb_singleton_ch]; simp

instance add [dT : T.Δ₁] [dU : U.Δ₁] [cT : T.DecidableΔ₁] [cU : U.DecidableΔ₁] :
    (T ∪ U).DecidableΔ₁ where
  decide p := cT.decide p || cU.decide p
  decide_iff p := by
    rw [mem_Δ₁Class_iff_evalb, show (Δ₁.ch (T ∪ U)) = dT.ch ⋎ dU.ch from rfl]
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq, Bool.or_eq_true]
    exact or_congr ((cT.decide_iff p).trans (mem_Δ₁Class_iff_evalb p))
      ((cU.decide_iff p).trans (mem_Δ₁Class_iff_evalb p))

/-- A finite theory presented by an explicit list. `Theory.Δ₁.ofFinite` goes through
`Set.Finite.toFinset.toList`, which is `noncomputable`, so the list has to be supplied by hand. -/
@[reducible] def ofFinite (T : Theory L) (h : Set.Finite T) (l : List (Sentence L))
    (hl : ∀ σ, σ ∈ l ↔ σ ∈ T) :
    letI := Δ₁.ofFinite T h
    T.DecidableΔ₁ :=
  letI := Δ₁.ofFinite T h
  { decide := fun p ↦ l.any fun σ ↦ p == encode σ
    decide_iff := fun p ↦ by
      rw [mem_Δ₁Class_iff_evalb, Δ₁.evalb_ofFinite_ch]
      simpa using
        ⟨fun ⟨σ, hσ, e⟩ ↦ ⟨σ, (hl σ).mp hσ, e⟩, fun ⟨σ, hσ, e⟩ ↦ ⟨σ, (hl σ).mpr hσ, e⟩⟩ }

end DecidableΔ₁

end LO.FirstOrder.Theory

namespace LO.FirstOrder.Arithmetic.PeanoMinus

open Encodable LO.FirstOrder LO.FirstOrder.Theory Language

/-! ### `𝗣𝗔⁻`

`Theory.Δ₁.ofFinite` presents a finite theory through `Set.Finite.toFinset.toList`, which is
`noncomputable`, so the recognizer needs the enumeration written out. `𝗣𝗔⁻` is the 17 arithmetic
axioms together with `𝗘𝗤 ℒₒᵣ`, and the latter is finite only because `ℒₒᵣ` is: three general
axioms, one congruence axiom per function symbol (`0`, `1`, `+`, `*`) and one per relation symbol
(`=`, `<`). Twenty-six in all. -/

/-- An explicit enumeration of `𝗣𝗔⁻`. -/
def axioms : List (Sentence ℒₒᵣ) :=
  [ Theory.Eq.refl ℒₒᵣ, Theory.Eq.symm ℒₒᵣ, Theory.Eq.trans ℒₒᵣ,
    Theory.Eq.funcExt (L := ℒₒᵣ) ORing.Func.zero,
    Theory.Eq.funcExt (L := ℒₒᵣ) ORing.Func.one,
    Theory.Eq.funcExt (L := ℒₒᵣ) ORing.Func.add,
    Theory.Eq.funcExt (L := ℒₒᵣ) ORing.Func.mul,
    Theory.Eq.relExt (L := ℒₒᵣ) ORing.Rel.eq,
    Theory.Eq.relExt (L := ℒₒᵣ) ORing.Rel.lt,
    Axiom.addZero, Axiom.addAssoc, Axiom.addComm, Axiom.addEqOfLt, Axiom.zeroLe,
    Axiom.zeroLtOne, Axiom.oneLeOfZeroLt, Axiom.addLtAdd, Axiom.mulZero, Axiom.mulOne,
    Axiom.mulAssoc, Axiom.mulComm, Axiom.mulLtMul, Axiom.distr, Axiom.ltIrrefl,
    Axiom.ltTrans, Axiom.ltTri ]

lemma mem_axioms_iff (σ : Sentence ℒₒᵣ) : σ ∈ axioms ↔ σ ∈ 𝗣𝗔⁻ := by
  constructor
  · intro h
    simp only [axioms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact equal _ eqAxiom.refl
    · exact equal _ eqAxiom.symm
    · exact equal _ eqAxiom.trans
    · exact equal _ (eqAxiom.funcExt _)
    · exact equal _ (eqAxiom.funcExt _)
    · exact equal _ (eqAxiom.funcExt _)
    · exact equal _ (eqAxiom.funcExt _)
    · exact equal _ (eqAxiom.relExt _)
    · exact equal _ (eqAxiom.relExt _)
    · exact addZero
    · exact addAssoc
    · exact addComm
    · exact addEqOfLt
    · exact zeroLe
    · exact zeroLtOne
    · exact oneLeOfZeroLt
    · exact addLtAdd
    · exact mulZero
    · exact mulOne
    · exact mulAssoc
    · exact mulComm
    · exact mulLtMul
    · exact distr
    · exact ltIrrefl
    · exact ltTrans
    · exact ltTri
  · intro h
    cases h with
    | equal φ hφ =>
      cases hφ with
      | refl => simp [axioms]
      | symm => simp [axioms]
      | trans => simp [axioms]
      | funcExt f => cases f <;> simp [axioms]
      | relExt r => cases r <;> simp [axioms]
    | addZero => simp [axioms]
    | addAssoc => simp [axioms]
    | addComm => simp [axioms]
    | addEqOfLt => simp [axioms]
    | zeroLe => simp [axioms]
    | zeroLtOne => simp [axioms]
    | oneLeOfZeroLt => simp [axioms]
    | addLtAdd => simp [axioms]
    | mulZero => simp [axioms]
    | mulOne => simp [axioms]
    | mulAssoc => simp [axioms]
    | mulComm => simp [axioms]
    | mulLtMul => simp [axioms]
    | distr => simp [axioms]
    | ltIrrefl => simp [axioms]
    | ltTrans => simp [axioms]
    | ltTri => simp [axioms]

/-- The axioms of `𝗣𝗔⁻` are executably recognizable. -/
noncomputable instance decidableΔ₁ :
    @Theory.DecidableΔ₁ ℒₒᵣ _ _ 𝗣𝗔⁻ (Theory.Δ₁.ofFinite 𝗣𝗔⁻ finite) :=
  Theory.DecidableΔ₁.ofFinite _ finite axioms mem_axioms_iff

/-! ### Examples

The inputs are numerals: a set literal such as `({p, q} : ℕ)` is itself built from `Exp.exp` and
does not reduce, so `decide` must be fed codes, not sets. -/

example : axioms.length = 26 := by decide

example :
    letI := Theory.Δ₁.ofFinite (𝗣𝗔⁻ : ArithmeticTheory) finite
    Theory.DecidableΔ₁.decide (T := (𝗣𝗔⁻ : ArithmeticTheory))
      (encode Axiom.zeroLtOne) = true := by decide

example :
    letI := Theory.Δ₁.ofFinite (𝗣𝗔⁻ : ArithmeticTheory) finite
    Theory.DecidableΔ₁.decide (T := (𝗣𝗔⁻ : ArithmeticTheory)) 0 = false := by decide

example :
    letI := Theory.Δ₁.ofFinite (𝗣𝗔⁻ : ArithmeticTheory) finite
    (encode Axiom.mulComm : ℕ) ∈ (𝗣𝗔⁻ : ArithmeticTheory).Δ₁Class (V := ℕ) := by decide

end LO.FirstOrder.Arithmetic.PeanoMinus

end
