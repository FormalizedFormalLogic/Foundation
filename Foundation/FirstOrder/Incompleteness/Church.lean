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

`church_theoremAux` shows that for every arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences, the
set of `T`-provable sentences is not computable, by a direct diagonalization on the self-applied
substitution `σ ↦ σ/[⌜σ⌝]` (no fixed-point/Gödel-numbering machinery beyond weak representability
of r.e. predicates, `re_complete`, is needed, unlike Gödel's first incompleteness theorem).
`church_theorem` specializes this to `T = ∅`: since `𝗣𝗔⁻` is finitely axiomatizable, `∅`-provability
computably many-one reduces `𝗣𝗔⁻`-provability to itself, removing the `𝗥₀ ⪯ T` and soundness
hypotheses needed by `church_theoremAux`.

This file is currently a skeleton: every helper lemma (`A2`-`A9`, `C1`-`C4` in the accompanying
proof plan) is stated with `sorry`; only `church_theoremAux` and `church_theorem` themselves have
complete proofs, assembled from those (sorry'd) facts.

- folklore; the standard proof of Church's theorem via undecidability of `𝚺₁`-completeness, see
  e.g. Rogers, *Theory of Recursive Functions and Effective Computability*, or Smoryński's chapter
  in the *Handbook of Mathematical Logic*.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic


namespace ArithmeticTheory

variable {T : ArithmeticTheory}

abbrev codes (T : ArithmeticTheory) : ℕ → Prop := λ n => (Encodable.decode n).elim False (T ⊢ ·)

def RE (T : ArithmeticTheory) : Prop := REPred T.theory

lemma iff_RE_theoryCodes_RE : RE T ↔ REPred (codes T) :=
  _root_.REPred.iff_decoded_pred


def Computable (T : ArithmeticTheory) : Prop := ComputablePred T.theory

lemma iff_Computable_theoryCodes_Computable : Computable T ↔ ComputablePred (codes T) :=
  _root_.ComputablePred.iff_decoded_pred

end ArithmeticTheory


open Bootstrapping Bootstrapping.Arithmetic

section Diagonalization

/-! ### Part I: Church's theorem for an arbitrary theory `T ⊇ 𝗥₀` -/

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

/-- The code-level diagonal self-substitution: if `n` is the code of a `Semisentence ℒₒᵣ 1`,
`d n` is the code of its self-substitution `n/[⌜n⌝]`. This is `Bootstrapping.Arithmetic.substNumeral`
applied to `n` twice, i.e. the same expression as the `D` used in `Incompleteness/First.lean`. -/
noncomputable def d (n : ℕ) : ℕ := substNumeral (V := ℕ) n n

/-- The graph of `d` is `𝚺₁`-definable. -/
lemma d_graph_sigma1 : 𝚺₁-Relation fun n m : ℕ ↦ m = d n := by
  have hSN : 𝚺-[1].Definable (fun w : Fin 3 → ℕ ↦ w 0 = substNumeral (w 1) (w 2)) :=
    HierarchySymbol.Defined.to_definable ssnum substNumeral.defined
  exact (hSN.retraction ![1, 0, 0]).of_iff fun v ↦ by simp [d]

/-- `d` is computable. -/
lemma d_computable : Computable d :=
  computable_of_graph_rePred (rePred_of_sigma1_relation d_graph_sigma1)

/-- `d` applied to the code of `σ` is the code of `σ`'s diagonal self-substitution. -/
lemma d_quote_eq (σ : ArithmeticSemisentence 1) : d (⌜σ⌝ : ℕ) = (⌜(σ/[⌜σ⌝] : ArithmeticSentence)⌝ : ℕ) :=
  substNumeral_app_quote σ σ

/-- The diagonal substitution `σ ↦ σ/[⌜σ⌝]`. -/
noncomputable def f (σ : ArithmeticSemisentence 1) : ArithmeticSentence := σ/[⌜σ⌝]

/-- `f` is computable. -/
lemma f_computable : Computable f := by
  have : Computable (fun σ : ArithmeticSemisentence 1 ↦
      (Encodable.decode (d (Encodable.encode σ)) : Option ArithmeticSentence).getD ⊤) :=
    Computable.option_getD (Computable.decode.comp (d_computable.comp Computable.encode))
      (Computable.const ⊤)
  refine this.of_eq fun σ ↦ ?_
  have h : d (Encodable.encode σ) = Encodable.encode (f σ) := by
    simpa [f, Sentence.quote_eq_encode] using d_quote_eq σ
  rw [h, Encodable.encodek, Option.getD_some]

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- This direction needs neither `𝗥₀ ⪯ T` nor `𝚺₁`-soundness, only closure of `ComputablePred`
-- under complement and many-one reduction along the computable `f`.
omit [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] in
/-- If `T`-provability is computable, so is `σ ↦ T ⊬ f σ`. -/
lemma D_computable (hC : ComputablePred T.theory) : ComputablePred (fun σ ↦ T ⊬ f σ) :=
  ComputablePred.computable_of_manyOneReducible
    (ManyOneReducible.mk (fun σ ↦ T ⊬ σ) f_computable) hC.not

/-- The diagonal fixed point for `σ ↦ T ⊬ f σ`: a sentence whose `T`-provability and
`T`-unprovability (after diagonal substitution) coincide, obtained from `codeOfREPred` and
`re_complete` applied to the decode-lifted predicate `σ ↦ T ⊬ f σ`. -/
lemma D_diagonal (hD : ComputablePred (fun σ ↦ T ⊬ f σ)) : ∃ δ : ArithmeticSemisentence 1, (T ⊬ f δ) ↔ T ⊢ f δ := by
  have hRe : REPred fun n : ℕ ↦ (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      (fun σ ↦ T ⊬ f σ) := REPred.iff_decoded_pred.mp hD.to_re
  refine ⟨codeOfREPred fun n : ℕ ↦
    (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False (fun σ ↦ T ⊬ f σ), ?_⟩
  simpa [Encodable.encodek, f, Arithmetic.gödelNumber'_eq_coe_encode]
    using re_complete (T := T) hRe (x := Encodable.encode (codeOfREPred fun n : ℕ ↦
      (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False (fun σ ↦ T ⊬ f σ)))

/-- Church's theorem, for an arbitrary arithmetic theory `T ⊇ 𝗥₀` sound on `𝚺₁` sentences: the set
of `T`-provable sentences is not computable. -/
theorem church_theoremAux : ¬ComputablePred {σ : ArithmeticSentence | T ⊢ σ} := by
  by_contra hC;
  obtain ⟨δ, hδ⟩ := D_diagonal $ D_computable hC;
  tauto;

end Diagonalization

section PeanoMinusReduction

/-! ### Part II: Church's theorem for `T = ∅`, via a reduction through `𝗣𝗔⁻` -/

lemma ttt {σ : ArithmeticSentence} :
  letI π := PeanoMinus.finite.toFinset.conj
  (𝗣𝗔⁻ : ArithmeticTheory) ⊢ σ ↔ ({π} : ArithmeticTheory) ⊢ σ
  := by
  set π := PeanoMinus.finite.toFinset.conj
  have hπ : (𝗣𝗔⁻ : ArithmeticTheory) ⊢ π :=
    Entailment.FConj!_iff_forall_provable.mpr fun ψ hψ ↦
      Entailment.by_axm (by simpa using hψ)
  have h₁ : (𝗣𝗔⁻ : ArithmeticTheory) ⪯ ({π} : ArithmeticTheory) :=
    Entailment.WeakerThan.ofAxm! fun {ψ} hψ ↦
      Entailment.mdp! (Entailment.left_Fconj!_intro (by simpa using hψ)) (Entailment.by_axm rfl)
  have h₂ : ({π} : ArithmeticTheory) ⪯ (𝗣𝗔⁻ : ArithmeticTheory) :=
    Entailment.WeakerThan.ofAxm! fun {ψ} hψ ↦ by
      rcases hψ with rfl; exact hπ
  exact ⟨h₁.wk, h₂.wk⟩


/-
/-- `𝗣𝗔⁻` is finitely axiomatized. -/
lemma exists_peanoMinus_list : ∃ Γ : List ArithmeticSentence, ∀ σ, σ ∈ (𝗣𝗔⁻ : ArithmeticTheory) ↔ σ ∈ Γ := by
  refine ⟨PeanoMinus.finite.toFinset.toList, fun σ ↦ ?_⟩
  rw [Finset.mem_toList, Set.Finite.mem_toFinset]
-/

/-- The deduction theorem for the finite theory `𝗣𝗔⁻`: `𝗣𝗔⁻` proves `σ` iff `∅` proves the
conjunction of `𝗣𝗔⁻`'s axioms implies `σ`. -/
lemma peanoMinus_provable_iff {σ : ArithmeticSentence} :
  letI π := PeanoMinus.finite.toFinset.conj
  (𝗣𝗔⁻ : ArithmeticTheory) ⊢ σ ↔ (∅ : ArithmeticTheory) ⊢ π 🡒 σ := by
  apply Iff.trans ttt;
  rw [← insert_empty_eq PeanoMinus.finite.toFinset.conj]
  exact Entailment.deduction_iff

/-- Church's theorem: the set of (purely logically, i.e. `∅`-)provable sentences is not
computable. -/
theorem church_theorem : ¬ComputablePred ((∅ : ArithmeticTheory).theory) := by
  by_contra hC;
  apply church_theoremAux (T := 𝗣𝗔⁻) (ComputablePred.computable_of_manyOneReducible ?_ hC);
  refine ⟨λ σ => PeanoMinus.finite.toFinset.conj 🡒 σ, ?_, ?_⟩
  . sorry;
  . intro σ;
    exact peanoMinus_provable_iff;

end PeanoMinusReduction

end LO.FirstOrder.Arithmetic

end
