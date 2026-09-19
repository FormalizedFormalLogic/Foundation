module
public import Foundation.FirstOrder.LK.Basic
@[expose] public section

/-! # Alternative definition of proof -/

namespace FFL.FirstOrder

variable {L : Language} [L.DecidableEq]

section derivation2

inductive LK2.Derivation (T : Theory L) : Finset (Proposition L) → Type _
| closed (Γ) (φ : Proposition L) : φ ∈ Γ → ∼φ ∈ Γ → LK2.Derivation T Γ
| axm {Γ} (φ : Sentence L) : φ ∈ T → (φ : Proposition L) ∈ Γ → LK2.Derivation T Γ
| verum {Γ} : ⊤ ∈ Γ → LK2.Derivation T Γ
| and {Γ} {φ ψ : Proposition L} : φ ⋏ ψ ∈ Γ → LK2.Derivation T (insert φ Γ) →
    LK2.Derivation T (insert ψ Γ) → LK2.Derivation T Γ
| or {Γ} {φ ψ : Proposition L} : φ ⋎ ψ ∈ Γ → LK2.Derivation T (insert φ (insert ψ Γ)) →
    LK2.Derivation T Γ
| all {Γ} {φ : Semiproposition L 1} : ∀¹ φ ∈ Γ →
    LK2.Derivation T (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → LK2.Derivation T Γ
| exs {Γ} {φ : Semiproposition L 1} : ∃¹ φ ∈ Γ → (t : SyntacticTerm L) →
    LK2.Derivation T (insert (φ/[t]) Γ) → LK2.Derivation T Γ
| wk {Δ Γ} : LK2.Derivation T Δ → Δ ⊆ Γ → LK2.Derivation T Γ
| shift {Γ} : LK2.Derivation T Γ → LK2.Derivation T (Γ.image Rewriting.shift)
| cut {Γ φ} : LK2.Derivation T (insert φ Γ) → LK2.Derivation T (insert (∼φ) Γ) → LK2.Derivation T Γ

scoped infix:45 " ⟹₂" => LK2.Derivation

abbrev LK2.Derivable (T : Theory L) (Γ : Finset (Proposition L)) := Nonempty (T ⟹₂ Γ)

scoped infix:45 " ⟹₂! " => LK2.Derivable

abbrev _root_.FFL.FirstOrder.Theory.Proof2 (T : Theory L) (φ : Proposition L) := T ⟹₂ {φ}

scoped infix: 45 " ⊢₂! " => Theory.Proof2

variable {T : Theory L} {Γ : LK.Sequent L} {φ : Proposition L}

lemma shifts_toFinset_eq_image_shift (Γ : LK.Sequent L) :
    Γ⁺.toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

def LK.Derivation.toDerivation2 (T) {Γ : LK.Sequent L} : ⊢ᴸᴷ¹ Γ → T ⟹₂ Γ.toFinset
  | LK.Derivation.identity R v => LK2.Derivation.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | LK.Derivation.verum => LK2.Derivation.verum (by simp)
  | LK.Derivation.and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    LK2.Derivation.and (φ := φ) (ψ := ψ) (by simp)
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T dq) (by intro x hx; simp_all; tauto))
  | LK.Derivation.or (Γ := Γ) (φ := φ) (ψ := ψ) dpq =>
    LK2.Derivation.or (φ := φ) (ψ := ψ) (by simp)
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T dpq)
      (by intro x hx; simp_all; tauto))
  | LK.Derivation.all (Γ := Γ) (φ := φ) dp =>
    LK2.Derivation.all (φ := φ) (by simp)
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T dp)
        (by
          intro x hx
          simp [shifts_toFinset_eq_image_shift] at hx ⊢
          aesop))
  | LK.Derivation.exs (Γ := Γ) (φ := φ) (t := t) dp =>
    LK2.Derivation.exs (φ := φ) (by simp) t
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T dp) (by intro x hx; simp_all; tauto))
  | LK.Derivation.contraction d =>
    LK2.Derivation.wk (LK.Derivation.toDerivation2 T d) (by intro x hx; simpa using hx)
  | LK.Derivation.weakening d =>
    LK2.Derivation.wk (LK.Derivation.toDerivation2 T d) (by intro x hx; simp_all)
  | LK.Derivation.cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    LK2.Derivation.cut (φ := φ)
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T d₁) (by intro x hx; simp_all; tauto))
      (LK2.Derivation.wk (LK.Derivation.toDerivation2 T d₂) (by intro x hx; simp_all; tauto))

namespace LK2.Derivation

structure ProofData (T : Theory L) (Γ : Finset (Proposition L)) where
  axioms : Multiset (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : ⊢ᴸᴷ¹ Γ.1 + ∼LK.Sequent.embed axioms

noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂Γ)
    (h : Γ = Δ := by simp) : T ⟹₂ Δ := h ▸ d

omit [L.DecidableEq] in
@[simp] lemma shifts_tilde_embed (A : Multiset (Sentence L)) :
    (∼LK.Sequent.embed A)⁺ = ∼LK.Sequent.embed A := by
  simp [Rewriting.shifts, LK.Sequent.embed, Multiset.tilde_def]

@[reducible] noncomputable def cutManyProof (A : Multiset (Sentence L))
    (hA : ∀ ψ ∈ A, ψ ∈ T)
    (d : T ⟹₂(insert (φ : Proposition L) (∼LK.Sequent.embed A).toFinset)) : T ⟹₂ {φ} :=
  -- Multiset induction cannot eliminate into the Type-valued derivation family.
  let rec go : (l : List (Sentence L)) → (∀ ψ ∈ l, ψ ∈ T) →
      T ⟹₂ (insert (φ : Proposition L) (∼LK.Sequent.embed (l : Multiset _)).toFinset) →
      T ⟹₂ {φ}
    | [], _, d => LK2.Derivation.cast d (by simp)
    | ψ :: l, hl, d =>
        have ax : T ⟹₂ insert (ψ : Proposition L)
            (insert φ (∼LK.Sequent.embed (l : Multiset _)).toFinset) :=
          LK2.Derivation.axm ψ (hl ψ (by simp)) (by simp)
        have dn : T ⟹₂ insert (∼(ψ : Proposition L))
            (insert φ (∼LK.Sequent.embed (l : Multiset _)).toFinset) := by
          refine LK2.Derivation.cast d ?_
          ext x
          have hneg : ∼x = Rewriting.emb ψ ↔ x = ∼Rewriting.emb ψ := by grind
          simp [LK.Sequent.embed, hneg, or_left_comm]
        have c : T ⟹₂ insert φ (∼LK.Sequent.embed (l : Multiset _)).toFinset := by
          exact LK2.Derivation.cast (LK2.Derivation.cut ax dn) (by ext x; simp)
        go l (by simp_all) c
  go A.toList (by simpa using hA) <| LK2.Derivation.cast d (by ext x; simp)

noncomputable def toProofData {Γ : Finset (Proposition L)} : T ⟹₂ Γ →
    ProofData T Γ
  | closed _ φ hp hn =>
      ⟨0, by simp, (LK.Derivation.eta φ).contra default (by
        intro x hx
        rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | axm φ hT hΓ =>
      ⟨⦃φ⦄, by simp [hT],
        (LK.Derivation.eta (φ : Proposition L)).contra default (by
          intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx <;> simp_all)⟩
  | verum h =>
      ⟨0, by simp, LK.Derivation.verum.contra default (by intro x hx; simp_all)⟩
  | and (φ := φ) (ψ := ψ) h dφ dψ => by
      rcases toProofData dφ with ⟨A, hA, bφ⟩
      rcases toProofData dψ with ⟨B, hB, bψ⟩
      refine ⟨A + B, by simp; grind, ?_⟩
      have bφ' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed (A + B)) + ⦃φ⦄ :=
        bφ.contra default (by intro x hx; simp_all [LK.Sequent.embed]; aesop)
      have bψ' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed (A + B)) + ⦃ψ⦄ :=
        bψ.contra default (by intro x hx; simp_all [LK.Sequent.embed]; aesop)
      exact Structural.absorb (LK.Derivation.and bφ' bψ') (Multiset.mem_add.mpr <| Or.inl h)
  | or (φ := φ) (ψ := ψ) h d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed A) + ⦃φ, ψ⦄ :=
        b.contra default (by intro x hx; simp_all; aesop)
      exact Structural.absorb (LK.Derivation.or b') (Multiset.mem_add.mpr <| Or.inl h)
  | all (φ := φ) h d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed A)⁺ + ⦃Rewriting.free φ⦄ :=
        b.contra default (by
          rw [Rewriting.shifts_add, shifts_tilde_embed]
          intro x hx
          simp [Rewriting.shifts] at hx ⊢
          aesop)
      exact Structural.absorb (LK.Derivation.all b') (Multiset.mem_add.mpr <| Or.inl h)
  | exs (φ := φ) h t d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed A) + ⦃φ/[t]⦄ :=
        b.contra default (by intro x hx; simp_all; aesop)
      exact Structural.absorb (LK.Derivation.exs (t := t) b') (Multiset.mem_add.mpr <| Or.inl h)
  | wk d h => by
      rcases toProofData d with ⟨A, hA, b⟩
      exact ⟨A, hA, b.contra default (by intro x hx; simp_all; aesop)⟩
  | shift (Γ := Γ) d => by
      rcases toProofData d with ⟨A, hA, b⟩
      refine ⟨A, hA, b.shift.contra default ?_⟩
      rw [Rewriting.shifts_add, shifts_tilde_embed]
      intro x hx
      simpa [Rewriting.shifts] using hx
  | cut (φ := φ) d dn => by
      rcases toProofData d with ⟨A, hA, b⟩
      rcases toProofData dn with ⟨B, hB, bn⟩
      refine ⟨A + B, by simp; grind, ?_⟩
      have b' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed (A + B)) + ⦃φ⦄ :=
        b.contra default (by intro x hx; simp_all [LK.Sequent.embed]; aesop)
      have bn' : ⊢ᴸᴷ¹ (Γ.1 + ∼LK.Sequent.embed (A + B)) + ⦃∼φ⦄ :=
        bn.contra default (by intro x hx; simp_all [LK.Sequent.embed]; aesop)
      exact (LK.Derivation.cut (Γ := Γ.1 + ∼LK.Sequent.embed (A + B))
        (Δ := Γ.1 + ∼LK.Sequent.embed (A + B)) (φ := φ) b' bn').contra default
        (by intro x hx; simp_all)

end LK2.Derivation

namespace Theory

noncomputable def Proof.toProof2 {φ : Sentence L} (b : T ⊢! φ) : T ⊢₂! (φ : Proposition L) :=
  LK2.Derivation.cutManyProof b.axioms b.axioms_mem <|
    LK2.Derivation.cast (LK.Derivation.toDerivation2 T b.derivation) (by
      ext x
      simp [LK.Sequent.embed, Multiset.map_tilde_comm])

noncomputable def Proof2.toProof {φ : Sentence L} (d : T ⊢₂! (φ : Proposition L)) : T ⊢! φ := by
  rcases LK2.Derivation.toProofData d with ⟨A, hA, b⟩
  exact ⟨A, hA, LK.Derivation.cast b (by
    simp [LK.Sequent.embed, Multiset.atom_eq_singleton, Multiset.map_tilde_comm])⟩

end Theory

lemma provable_iff_derivable2 {φ : Sentence L} : T ⊢ φ ↔ Nonempty (T ⊢₂! (φ : Proposition L)) := by
  exact ⟨fun h ↦ ⟨h.get.toProof2⟩, fun ⟨h⟩ ↦ ⟨h.toProof⟩⟩

end derivation2

end FFL.FirstOrder
