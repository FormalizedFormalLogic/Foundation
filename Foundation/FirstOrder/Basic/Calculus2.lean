module
public import Foundation.FirstOrder.Basic.Calculus
@[expose] public section

/-! # Alternative definition of proof -/

namespace LO.FirstOrder

variable {L : Language} [L.DecidableEq]

section derivation2

inductive Derivation2 (T : Theory L) : Finset (Proposition L) → Type _
| closed (Γ) (φ : Proposition L) : φ ∈ Γ → ∼φ ∈ Γ → Derivation2 T Γ
| axm {Γ} (φ : Sentence L) : φ ∈ T → (φ : Proposition L) ∈ Γ → Derivation2 T Γ
| verum {Γ} : ⊤ ∈ Γ → Derivation2 T Γ
| and {Γ} {φ ψ : Proposition L} : φ ⋏ ψ ∈ Γ → Derivation2 T (insert φ Γ) → Derivation2 T (insert ψ Γ) → Derivation2 T Γ
| or {Γ} {φ ψ : Proposition L} : φ ⋎ ψ ∈ Γ → Derivation2 T (insert φ (insert ψ Γ)) → Derivation2 T Γ
| all {Γ} {φ : Semiproposition L 1} : ∀¹ φ ∈ Γ → Derivation2 T (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → Derivation2 T Γ
| exs {Γ} {φ : Semiproposition L 1} : ∃¹ φ ∈ Γ → (t : SyntacticTerm L) → Derivation2 T (insert (φ/[t]) Γ) → Derivation2 T Γ
| wk {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
| shift {Γ}   : Derivation2 T Γ → Derivation2 T (Γ.image Rewriting.shift)
| cut {Γ φ} : Derivation2 T (insert φ Γ) → Derivation2 T (insert (∼φ) Γ) → Derivation2 T Γ

scoped infix:45 " ⟹₂" => Derivation2

abbrev Derivable2 (T : Theory L) (Γ : Finset (Proposition L)) := Nonempty (T ⟹₂ Γ)

scoped infix:45 " ⟹₂! " => Derivable2

abbrev _root_.LO.FirstOrder.Theory.Proof2 (T : Theory L) (φ : Proposition L) := T ⟹₂ {φ}

scoped infix: 45 " ⊢!₂! " => Theory.Proof2

variable {T : Theory L}

lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    Γ⁺ᵐ.toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shiftsM]

def Derivation.toDerivation2 (T) {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → T ⟹₂ Γ.toFinset
  | Derivation.identity R v => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | Derivation.verum => Derivation2.verum (by simp)
  | Derivation.and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by intro x hx; simp_all; tauto))
  | Derivation.or (Γ := Γ) (φ := φ) (ψ := ψ) dpq =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq)
      (by intro x hx; simp_all; tauto))
  | Derivation.all (Γ := Γ) (φ := φ) dp =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp)
        (by
          intro x hx
          simp [shifts_toFinset_eq_image_shift] at hx ⊢
          aesop))
  | Derivation.exs (Γ := Γ) (φ := φ) (t := t) dp =>
    Derivation2.exs (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
  | Derivation.contraction d h =>
    Derivation2.wk (Derivation.toDerivation2 T d) (Multiset.toFinset_subset.mpr h)
  | Derivation.cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (by intro x hx; simp_all; tauto))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by intro x hx; simp_all; tauto))

/-- Contracts a principal formula already present in the side context.
This is a routine structural derivation. -/
def Derivation.absorb (d : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (h : φ ∈ Γ) : ⊢ᴸᴷ¹ Γ :=
  d.contra <| by
    intro ψ hψ
    rcases Multiset.mem_add.mp hψ with hψ | hψ <;> simp_all

namespace Derivation2

structure ProofData (T : Theory L) (Γ : Finset (Proposition L)) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : ⊢ᴸᴷ¹ Γ.1 + ∼Sequent.embed axioms

noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Γ)
    (h : Γ = Δ := by simp) : T ⟹₂ Δ := h ▸ d

omit [L.DecidableEq] in
@[simp] lemma shifts_tilde_embed (A : Multiset (Sentence L)) :
    (∼Sequent.embed A)⁺ᵐ = ∼Sequent.embed A := by
  simp [Rewriting.shiftsM, Sequent.embed, Multiset.tilde_def]

@[reducible] noncomputable def cutManyProof (A : Multiset (Sentence L))
    (hA : ∀ ψ ∈ A, ψ ∈ T)
    (d : T ⟹₂ (insert (φ : Proposition L) (∼Sequent.embed A).toFinset)) : T ⟹₂ {φ} :=
  -- Multiset induction cannot eliminate into the Type-valued derivation family.
  let rec go : (l : List (Sentence L)) → (∀ ψ ∈ l, ψ ∈ T) →
      T ⟹₂ (insert (φ : Proposition L) (∼Sequent.embed (l : Multiset _)).toFinset) →
      T ⟹₂ {φ}
    | [], _, d => Derivation2.cast d (by simp)
    | ψ :: l, hl, d =>
        have ax : T ⟹₂ insert (ψ : Proposition L)
            (insert φ (∼Sequent.embed (l : Multiset _)).toFinset) :=
          Derivation2.axm ψ (hl ψ (by simp)) (by simp)
        have dn : T ⟹₂ insert (∼(ψ : Proposition L))
            (insert φ (∼Sequent.embed (l : Multiset _)).toFinset) := by
          refine Derivation2.cast d ?_
          ext x
          have hneg : ∼x = Rewriting.emb ψ ↔ x = ∼Rewriting.emb ψ := by grind
          simp [Sequent.embed, hneg, or_left_comm]
        have c : T ⟹₂ insert φ (∼Sequent.embed (l : Multiset _)).toFinset := by
          exact Derivation2.cast (Derivation2.cut ax dn) (by ext x; simp)
        go l (by simp_all) c
  go A.toList (by simpa using hA) <| Derivation2.cast d (by ext x; simp)

noncomputable def toProofData : {Γ : Finset (Proposition L)} → T ⟹₂ Γ →
    ProofData T Γ
  | Γ, closed _ φ hp hn =>
      ⟨0, by simp, (Derivation.eta φ).contra (by
        intro x hx
        rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | Γ, axm φ hT hΓ =>
      ⟨⦃φ⦄, by simp [hT],
        (Derivation.eta (φ : Proposition L)).contra (by
          intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | Γ, verum h =>
      ⟨0, by simp, Derivation.verum.contra (by intro x hx; simp_all)⟩
  | Γ, and (φ := φ) (ψ := ψ) h dφ dψ => by
      rcases toProofData dφ with ⟨A, hA, bφ⟩
      rcases toProofData dψ with ⟨B, hB, bψ⟩
      refine ⟨A + B, by simp; grind, ?_⟩
      have bφ' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed (A + B)) + ⦃φ⦄ :=
        bφ.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
      have bψ' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed (A + B)) + ⦃ψ⦄ :=
        bψ.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
      exact (Derivation.and bφ' bψ').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, or (φ := φ) (ψ := ψ) h d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed A) + ⦃φ, ψ⦄ :=
        b.contra (by intro x hx; simp_all; aesop)
      exact (Derivation.or b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, all (φ := φ) h d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed A)⁺ᵐ + ⦃Rewriting.free φ⦄ :=
        b.contra (by
          rw [Rewriting.shiftsM_add, shifts_tilde_embed]
          intro x hx
          simp [Rewriting.shiftsM] at hx ⊢
          aesop)
      exact (Derivation.all b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, exs (φ := φ) h t d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed A) + ⦃φ/[t]⦄ :=
        b.contra (by intro x hx; simp_all; aesop)
      exact (Derivation.exs (t := t) b').absorb (Multiset.mem_add.mpr <| Or.inl h)
  | Γ, wk d h => by
      rcases toProofData d with ⟨A, hA, b⟩
      exact ⟨A, hA, b.contra (by intro x hx; simp_all; aesop)⟩
  | _, shift (Γ := Γ) d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, b.shift.contra ?_⟩
      rw [Rewriting.shiftsM_add, shifts_tilde_embed]
      intro x hx
      simpa [Rewriting.shiftsM] using hx
  | Γ, cut (φ := φ) d dn => by
      rcases toProofData d with ⟨A, hA, b⟩
      rcases toProofData dn with ⟨B, hB, bn⟩
      refine ⟨A + B, by simp; grind, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed (A + B)) + ⦃φ⦄ :=
        b.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
      have bn' : ⊢ᴸᴷ¹ (Γ.1 + ∼Sequent.embed (A + B)) + ⦃∼φ⦄ :=
        bn.contra (by intro x hx; simp_all [Sequent.embed]; aesop)
      exact (Derivation.cut (Γ := Γ.1 + ∼Sequent.embed (A + B))
        (Δ := Γ.1 + ∼Sequent.embed (A + B)) (φ := φ) b' bn').contra
        (by intro x hx; simp_all)

end Derivation2

namespace Theory

noncomputable def Proof.toProof2 {φ : Sentence L} (b : T ⊢! φ) : T ⊢!₂! (φ : Proposition L) :=
  Derivation2.cutManyProof b.axioms b.axioms_mem <|
    Derivation2.cast (Derivation.toDerivation2 T b.derivation) (by ext x; simp [Sequent.embed])

noncomputable def Proof2.toProof {φ : Sentence L} (d : T ⊢!₂! (φ : Proposition L)) : T ⊢! φ := by
  rcases Derivation2.toProofData d with ⟨A, hA, b⟩
  exact ⟨A, hA, Derivation.cast b (by simp [Sequent.embed, Multiset.atom_eq_singleton])⟩

end Theory

lemma provable_iff_derivable2 {φ : Sentence L} : T ⊢ φ ↔ Nonempty (T ⊢!₂! (φ : Proposition L)) := by
  exact ⟨fun h ↦ ⟨h.get.toProof2⟩, fun ⟨h⟩ ↦ ⟨h.toProof⟩⟩

end derivation2

end LO.FirstOrder
