module

public import Foundation.FirstOrder.Basic.Coding
public import Foundation.Vorspiel.Computability
public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Incompleteness.Halting
public import Mathlib.Computability.Reduce

/-!
# Church's undecidability theorem

`church_theorem_general` shows that for every arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences,
the set of `T`-provable sentences is not computable, by a direct diagonalization on the
self-applied substitution `σ ↦ σ/[⌜σ⌝]` (no fixed-point/Gödel-numbering machinery beyond weak
representability of r.e. predicates, `re_complete`, is needed, unlike Gödel's first incompleteness
theorem). `church_theorem` specializes this to `T = ∅`: since `𝗣𝗔⁻` is finitely axiomatizable,
`𝗣𝗔⁻`-provability computably many-one reduces to `∅`-provability, so undecidability transfers
from `church_theorem_general` without needing the `𝗥₀ ⪯ T` and soundness hypotheses required
there.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

section Diagonalization

/-- A total function on `ℕ` whose graph is r.e. is computable. -/
lemma computable_of_graph_rePred {g : ℕ → ℕ} (h : REPred fun p : ℕ × ℕ ↦ p.2 = g p.1) :
    Computable g := by
  have hF : Partrec₂ fun a b : ℕ ↦ (Part.assert (b = g a) fun _ ↦ Part.some ()).map fun _ ↦ b :=
    Partrec.map h (Primrec.snd.comp Primrec.fst).to_comp
  obtain ⟨k, hk, Hk⟩ := Partrec.projection hF (by
    rintro a b₁ b₂ c₁ c₂ h₁ h₂
    simp only [Part.mem_map_iff, Part.mem_assert_iff] at h₁ h₂
    obtain ⟨-, ⟨rfl, -⟩, rfl⟩ := h₁
    obtain ⟨-, ⟨rfl, -⟩, rfl⟩ := h₂
    rfl)
  refine hk.of_eq_tot fun a ↦ ?_
  exact (Hk (g a) a).mpr ⟨g a, by simp [Part.mem_map_iff, Part.mem_assert_iff]⟩

/-- A `𝚺₁`-definable binary relation on `ℕ` is r.e. -/
lemma rePred_of_sigma1_relation {R : ℕ → ℕ → Prop} (h : 𝚺₁-Relation R) :
    REPred fun p : ℕ × ℕ ↦ R p.1 p.2 := by
  obtain ⟨φ, hφ⟩ := h
  have : REPred fun p : ℕ × ℕ ↦
      φ.val.Eval (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2).get id :=
    (sigma1_re id φ.sigma_prop).comp
      (Primrec.to_comp <| Primrec.vector_cons.comp .fst
        (Primrec.vector_cons.comp .snd (.const List.Vector.nil)))
  exact this.of_eq <| by intro p; simpa [List.Vector.cons_get] using hφ ![p.1, p.2]

/-- If `g : α → ℕ` is a computable numeric code for `F : α → β` (i.e. `g a` decodes back to
`F a` for every `a`), then `F` is computable. -/
lemma computable_of_computable_encode {α β : Type*} [Primcodable α] [Primcodable β]
    {g : α → ℕ} (hg : Computable g) {F : α → β} (h : ∀ a, g a = Encodable.encode (F a))
    (default : β) : Computable F := by
  have : Computable (fun a ↦ (Encodable.decode (g a) : Option β).getD default) :=
    Computable.option_getD (Computable.decode.comp hg) (Computable.const default)
  exact this.of_eq fun a ↦ by rw [h, Encodable.encodek, Option.getD_some]

/-- The code-level diagonal self-substitution: if `n` is the code of a `Semisentence ℒₒᵣ 1`,
`diagCode n` is the code of its self-substitution `n/[⌜n⌝]`. This is `Bootstrapping.Arithmetic.substNumeral`
applied to `n` twice, i.e. the same expression as the `D` used in `Incompleteness/First.lean`. -/
noncomputable def diagCode (n : ℕ) : ℕ := substNumeral (V := ℕ) n n

/-- The graph of `diagCode` is `𝚺₁`-definable. -/
lemma diagCode_graph_sigma1 : 𝚺₁-Relation fun n m : ℕ ↦ m = diagCode n := by
  have hSN : 𝚺-[1].Definable (fun w : Fin 3 → ℕ ↦ w 0 = substNumeral (w 1) (w 2)) :=
    HierarchySymbol.Defined.to_definable ssnum substNumeral.defined
  exact (hSN.retraction ![1, 0, 0]).of_iff fun v ↦ by simp [diagCode]

/-- `diagCode` is computable. -/
lemma diagCode_computable : Computable diagCode :=
  computable_of_graph_rePred (rePred_of_sigma1_relation diagCode_graph_sigma1)

/-- `diagCode` applied to the code of `σ` is the code of `σ`'s diagonal self-substitution. -/
lemma diagCode_quote_eq (σ : ArithmeticSemisentence 1) :
    diagCode ⌜σ⌝ = ⌜(σ/[⌜σ⌝] : ArithmeticSentence)⌝ :=
  substNumeral_app_quote σ σ

/-- The diagonal substitution `σ ↦ σ/[⌜σ⌝]`. -/
noncomputable def diagSubst (σ : ArithmeticSemisentence 1) : ArithmeticSentence := σ/[⌜σ⌝]

/-- `diagSubst` is computable. -/
lemma diagSubst_computable : Computable diagSubst :=
  computable_of_computable_encode (diagCode_computable.comp Computable.encode)
    (fun σ ↦ by simpa [diagSubst, Sentence.quote_eq_encode] using diagCode_quote_eq σ) ⊤

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- This direction needs neither `𝗥₀ ⪯ T` nor `𝚺₁`-soundness, only closure of `ComputablePred`
-- under complement and many-one reduction along the computable `diagSubst`.
omit [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] in
/-- If `T`-provability is computable, so is `σ ↦ T ⊬ diagSubst σ`. -/
lemma unprovable_diagSubst_computable (hC : ComputablePred T.theory) :
    ComputablePred (fun σ ↦ T ⊬ diagSubst σ) :=
  ComputablePred.computable_of_manyOneReducible
    (ManyOneReducible.mk (fun σ ↦ T ⊬ σ) diagSubst_computable) hC.not

/-- The diagonal fixed point for `σ ↦ T ⊬ diagSubst σ`: a sentence whose `T`-provability and
`T`-unprovability (after diagonal substitution) coincide, obtained from `codeOfREPred` and
`re_complete` applied to the decode-lifted predicate `σ ↦ T ⊬ diagSubst σ`. -/
lemma diagSubst_fixedPoint (hD : ComputablePred (fun σ ↦ T ⊬ diagSubst σ)) :
    ∃ δ : ArithmeticSemisentence 1, (T ⊬ diagSubst δ) ↔ T ⊢ diagSubst δ := by
  have hRe : REPred fun n : ℕ ↦ (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      (fun σ ↦ T ⊬ diagSubst σ) := REPred.iff_decoded_pred.mp hD.to_re
  refine ⟨codeOfREPred fun n : ℕ ↦
    (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False (fun σ ↦ T ⊬ diagSubst σ), ?_⟩
  simpa [Encodable.encodek, diagSubst, Arithmetic.gödelNumber'_eq_coe_encode]
    using re_complete (T := T) hRe (x := Encodable.encode (codeOfREPred fun n : ℕ ↦
      (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False (fun σ ↦ T ⊬ diagSubst σ)))

/-- Church's theorem, for an arbitrary arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences: the set
of `T`-provable sentences is not computable. -/
theorem church_theorem_general : ¬ComputablePred T.theory := by
  by_contra hC
  obtain ⟨δ, hδ⟩ := diagSubst_fixedPoint (unprovable_diagSubst_computable hC)
  tauto

end Diagonalization

section PeanoMinusReduction

/-- A finite theory proves the conjunction of its own (finite) axiom set. -/
lemma finite_theory_provable_conj {T : Theory ℒₒᵣ} (hT : Set.Finite T) : T ⊢ hT.toFinset.conj :=
  Entailment.FConj!_iff_forall_provable.mpr fun {σ} hσ ↦ Entailment.by_axm (by simp_all)

/-- A finite theory is provability-equivalent to the (singleton) theory consisting of the
conjunction of its own axioms. -/
lemma finite_theory_equiv_singletonConj {T : Theory ℒₒᵣ} (hT : Set.Finite T) :
    T ≊ ({hT.toFinset.conj} : ArithmeticTheory) :=
  Entailment.Equiv.antisymm_iff.mpr
    ⟨Entailment.WeakerThan.ofAxm! fun {σ} hσ ↦
        Entailment.mdp! (Entailment.left_Fconj!_intro (by simp_all)) (Entailment.by_axm rfl),
      Entailment.WeakerThan.ofAxm! fun {σ} hσ ↦ by
        rcases hσ with rfl; exact finite_theory_provable_conj hT⟩

/-- A deduction theorem for finite theories: a finite theory `T` proves `σ` iff `∅` proves the
implication from the conjunction of `T`'s axioms to `σ`. -/
lemma finite_theory_provable_iff_conj_imp {T : Theory ℒₒᵣ} (hT : Set.Finite T) :
    T ⊢ σ ↔ (∅ : ArithmeticTheory) ⊢ hT.toFinset.conj 🡒 σ := by
  rw [Entailment.Equiv.iff.mp (finite_theory_equiv_singletonConj hT) σ, ←insert_empty_eq]
  exact Entailment.deduction_iff

/-- Church's theorem: the set of (purely logically, i.e. `∅`-)provable sentences is not
computable. -/
theorem church_theorem : ¬ComputablePred ((∅ : ArithmeticTheory).theory) := by
  by_contra hC
  apply church_theorem_general (T := 𝗣𝗔⁻) (ComputablePred.computable_of_manyOneReducible ?_ hC)
  refine ⟨fun σ ↦ PeanoMinus.finite.toFinset.conj 🡒 σ, ?_, ?_⟩
  . set π := PeanoMinus.finite.toFinset.conj
    set c := Encodable.encode (∼π : ArithmeticSentence)
    have hPrim : Primrec fun e : ℕ ↦ (Nat.pair 5 <| Nat.pair c e) + 1 :=
      Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
        (Primrec₂.natPair.comp (Primrec.const c) Primrec.id))
    exact computable_of_computable_encode (hPrim.to_comp.comp Computable.encode)
      (fun σ ↦ by rw [Semiformula.imp_eq, Semiformula.encode_or,
        ← Semiformula.encode_eq_toNat, ← Semiformula.encode_eq_toNat]) ⊤
  . -- specialize `finite_theory_provable_iff_conj_imp` to `T = 𝗣𝗔⁻`
    exact fun σ ↦ finite_theory_provable_iff_conj_imp PeanoMinus.finite

end PeanoMinusReduction

end LO.FirstOrder.Arithmetic

end
