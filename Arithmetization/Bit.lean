import Arithmetization.Exponential.Exp

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

variable [𝐈𝚺₁.Mod M]


def Bit (i a : M) : Prop := LenBit (exp i) a

instance : Membership M M := ⟨Bit⟩

def bitdef : Σᴬ[0] 2 := ⟨“∃[#0 < #2 + 1] (!expdef [#0, #1] ∧ !lenbitdef [#0, #2])”, by simp⟩

lemma bit_defined : Σᴬ[0]-Relation ((· ∈ ·) : M → M → Prop) bitdef := by
  intro v; simp [bitdef, lenbit_defined.pval, exp_defined.pval, ←le_iff_lt_succ]
  constructor
  · intro h; exact ⟨exp (v 0), by simp [h.le], rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

instance {b s} : DefinableRel b s ((· ∈ ·) : M → M → Prop) := defined_to_with_param₀ _ bit_defined

open Classical in
noncomputable def bitInsert (i a : M) : M := if i ∈ a then a else a + exp i

instance : Insert M M := ⟨bitInsert⟩

lemma insert_eq {i a : M} : insert i a = bitInsert i a := rfl

lemma mem_iff_bit {i a : M} : i ∈ a ↔ Bit i a := iff_of_eq rfl

lemma exp_le_of_mem {i a : M} (h : i ∈ a) : exp i ≤ a := LenBit.le h

lemma lt_of_mem {i a : M} (h : i ∈ a) : i < a := lt_of_lt_of_le (lt_exp i) (exp_le_of_mem h)

@[definability] lemma Definable.ball_mem {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial b s f) (h : Definable b s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable b s (fun v ↦ ∀ x ∈ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∀[#0 < #1] (!bitdef .[#0, #1] → !((Rew.substs (#0 :> (#·.succ.succ))).hom p)))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, bit_defined.pval, ←le_iff_lt_succ]
        constructor
        · rintro h; exact ⟨f v, hbf v, rfl, fun x _ hx ↦ h x hx⟩
        · rintro ⟨_, _, rfl, h⟩ x hx; exact h x (lt_of_mem hx) hx⟩

@[definability] lemma Definable.bex_mem {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : Semipolynomial b s f) (h : Definable b s (fun w ↦ P (w ·.succ) (w 0))) :
    Definable b s (fun v ↦ ∃ x ∈ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  exact ⟨⟨“∃[#0 < !!(Rew.bShift bf) + 1] (!f_graph ∧ ∃[#0 < #1] (!bitdef .[#0, #1] ∧ !((Rew.substs (#0 :> (#·.succ.succ))).hom p)))”, by simp⟩,
    by  intro v; simp [hf_graph.eval, hp.eval, bit_defined.pval, ←le_iff_lt_succ]
        constructor
        · rintro ⟨x, hx, h⟩; exact ⟨f v, hbf v, rfl, x, lt_of_mem hx, hx, h⟩
        · rintro ⟨_, _, rfl, x, _, hx, h⟩; exact ⟨x, hx, h⟩⟩

lemma mem_iff_mul_exp_add_exp_add {i a : M} : i ∈ a ↔ ∃ k, ∃ r < exp i, a = k * exp (i + 1) + exp i + r := by
  simp [mem_iff_bit, exp_succ]
  exact lenbit_iff_add_mul (exp_pow2 i) (a := a)

lemma not_mem_iff_mul_exp_add {i a : M} : i ∉ a ↔ ∃ k, ∃ r < exp i, a = k * exp (i + 1) + r := by
  simp [mem_iff_bit, exp_succ]
  exact not_lenbit_iff_add_mul (exp_pow2 i) (a := a)

@[simp] lemma not_mem_zero (i : M) : i ∉ (0 : M) := by simp [mem_iff_bit, Bit]

@[simp] lemma mem_bitInsert_iff {i j a : M} :
    i ∈ insert j a ↔ i = j ∨ i ∈ a := by
  by_cases h : j ∈ a <;> simp [h, insert_eq, bitInsert]
  · by_cases e : i = j <;> simp [h, e]
  · simpa [exponential_inj.eq_iff] using
      lenbit_add_pow2_iff_of_not_lenbit (exp_pow2 i) (exp_pow2 j) h

lemma lt_exp_iff {a i : M} : a < exp i ↔ ∀ j ∈ a, j < i :=
  ⟨fun h j hj ↦ exponential_monotone.mp <| lt_of_le_of_lt (exp_le_of_mem hj) h,
  by {
    contrapose; simp
    intro (h : exp i ≤ a)


   }⟩

instance : HasSubset M := ⟨fun a b ↦ ∀ {i}, i ∈ a → i ∈ b⟩

def bitSubsetdef : Σᴬ[0] 2 := ⟨“∀[#0 < #1] (!bitdef [#0, #1] → !bitdef [#0, #2])”, by simp⟩

lemma bitSubset_defined : Σᴬ[0]-Relation ((· ⊆ ·) : M → M → Prop) bitSubsetdef := by
  intro v; simp [bitSubsetdef, bit_defined.pval]
  exact ⟨by intro h x _ hx; exact h hx, by intro h x hx; exact h x (lt_of_mem hx) hx⟩

instance {b s} : DefinableRel b s ((· ⊆ ·) : M → M → Prop) := defined_to_with_param₀ _ bitSubset_defined

lemma le_of_subset {a b : M} (h : a ⊆ b) : a ≤ b := by
  by_contra A


lemma mem_ext {a b : M} (h : ∀ i, i ∈ a ↔ i ∈ b) : a = b := by sorry



end Model

end

end Arith

end LO.FirstOrder
