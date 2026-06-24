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
| all {Γ} {φ : Semiproposition L 1} : ∀⁰ φ ∈ Γ → Derivation2 T (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → Derivation2 T Γ
| exs {Γ} {φ : Semiproposition L 1} : ∃⁰ φ ∈ Γ → (t : SyntacticTerm L) → Derivation2 T (insert (φ/[t]) Γ) → Derivation2 T Γ
| wk {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
| shift {Γ}   : Derivation2 T Γ → Derivation2 T (Γ.image Rewriting.shift)
| cut {Γ φ} : Derivation2 T (insert φ Γ) → Derivation2 T (insert (∼φ) Γ) → Derivation2 T Γ

scoped infix:45 " ⟹₂" => Derivation2

abbrev Derivable2 (T : Theory L) (Γ : Finset (Proposition L)) := Nonempty (T ⟹₂ Γ)

scoped infix:45 " ⟹₂! " => Derivable2

abbrev Derivable2SingleConseq (T : Theory L) (φ : Proposition L) : Prop := T ⟹₂! {φ}

scoped infix: 45 " ⊢!₂! " => Derivable2SingleConseq

variable {T : Theory L}

lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    (Rewriting.shifts Γ).toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

def Derivation.toDerivation2 (T) {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → T ⟹₂ Γ.toFinset
  | Derivation.identity R v => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | Derivation.verum => Derivation2.verum (by simp)
  | Derivation.and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by simp))
  | Derivation.or (Γ := Γ) (φ := φ) (ψ := ψ) dpq =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq)
      (by simp))
  | Derivation.all (Γ := Γ) (φ := φ) dp =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp)
        (by simp [shifts_toFinset_eq_image_shift]))
  | Derivation.exs (Γ := Γ) (φ := φ) (t := t) dp =>
    Derivation2.exs (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp))
  | Derivation.contraction d h =>
    Derivation2.wk (Derivation.toDerivation2 T d) (List.toFinset_mono h)
  | Derivation.cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (List.subset_def.mpr <| by simp_all))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (List.subset_def.mpr <| by simp_all))

namespace Derivation2

noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Γ) (h : Γ = Δ := by simp) : T ⟹₂ Δ := by
  rcases h; exact d

omit [L.DecidableEq] in
private lemma exists_shift_mem_embed_of_mem {A : List (Sentence L)} {φ : Proposition L}
    (h : φ ∈ Sequent.embed A) : ∃ ψ ∈ Sequent.embed A, Rewriting.shift ψ = φ := by
  simp [Sequent.embed] at h ⊢
  grind

omit [L.DecidableEq] in
private lemma mem_embed_of_exists_shift_mem {A : List (Sentence L)} {φ : Proposition L}
    (h : ∃ ψ ∈ Sequent.embed A, Rewriting.shift ψ = φ) : φ ∈ Sequent.embed A := by
  simp [Sequent.embed] at h ⊢
  grind

@[reducible] noncomputable def cutMany : (A : List (Sentence L)) → (∀ ψ ∈ A, ψ ∈ T) →
    T ⟹₂! (insert (φ : Proposition L) (∼Sequent.embed A).toFinset) → T ⟹₂! {φ}
  | [], _, d => d
  | ψ :: A, hA, ⟨d⟩ =>
      have ax : T ⟹₂ insert (ψ : Proposition L) (insert φ (∼Sequent.embed A).toFinset) :=
        Derivation2.axm ψ (hA ψ (by simp)) (by simp)
      have dn : T ⟹₂ insert (∼(ψ : Proposition L)) (insert φ (∼Sequent.embed A).toFinset) := by
        refine Derivation2.cast d ?_
        ext x; simp [List.toFinset_cons]; grind
      have c : T ⟹₂ insert φ (∼Sequent.embed A).toFinset := by
        refine Derivation2.cast (Derivation2.cut ax dn) ?_
        ext x; simp
      cutMany A (by simp_all) ⟨c⟩

noncomputable def toProof : {Γ : Finset (Proposition L)} → T ⟹₂ Γ →
    ∃ A : List (Sentence L), (∀ ψ ∈ A, ψ ∈ T) ∧ Nonempty (⊢ᴸᴷ¹ Γ.toList ++ ∼Sequent.embed A)
  | Γ, closed _ φ hp hn =>
      ⟨[], by simp, ⟨(Derivation.eta φ).contra <| List.subset_def.mpr (by simp_all)⟩⟩
  | Γ, axm φ hT hΓ =>
      ⟨[φ], by simp [hT], ⟨(Derivation.eta (φ : Proposition L)).contra <| List.subset_def.mpr (by simp_all)⟩⟩
  | Γ, verum h =>
      ⟨[], by simp, ⟨Derivation.verum.contra <| List.subset_def.mpr (by simp_all)⟩⟩
  | Γ, and (φ := φ) (ψ := ψ) h dφ dψ => by
      rcases toProof dφ with ⟨A, hA, ⟨bφ⟩⟩
      rcases toProof dψ with ⟨B, hB, ⟨bψ⟩⟩
      refine ⟨A ++ B, by simp; grind, ⟨?_⟩⟩
      have bφ' : ⊢ᴸᴷ¹ φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bφ.contra <| List.subset_def.mpr (by simp_all [Sequent.embed_append]; grind)
      have bψ' : ⊢ᴸᴷ¹ ψ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bψ.contra <| List.subset_def.mpr (by simp_all [Sequent.embed_append]; grind)
      exact (Derivation.and bφ' bψ').contra <| List.subset_def.mpr (by simp_all)
  | Γ, or (φ := φ) (ψ := ψ) h d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ :: ψ :: Γ.toList ++ ∼Sequent.embed A :=
        b.contra <| List.subset_def.mpr (by simp_all; grind)
      exact (Derivation.or b').contra <| List.subset_def.mpr (by simp_all)
  | Γ, all (φ := φ) h d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ Rewriting.free φ :: (Γ.toList ++ ∼Sequent.embed A)⁺ :=
        b.contra <| List.subset_def.mpr (by simp_all [Rewriting.shifts]; grind [exists_shift_mem_embed_of_mem])
      exact (Derivation.all b').contra <| List.subset_def.mpr (by simp_all)
  | Γ, exs (φ := φ) h t d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ/[t] :: Γ.toList ++ ∼Sequent.embed A :=
        b.contra <| List.subset_def.mpr (by simp_all; grind)
      exact (Derivation.exs (t := t) b').contra <| List.subset_def.mpr (by simp_all)
  | Γ, wk d h => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨b.contra <| List.subset_def.mpr (by simp_all; grind)⟩⟩
  | _, shift (Γ := Γ) d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      exact b.shift.contra <| List.subset_def.mpr (by simp_all [Rewriting.shifts]; grind [mem_embed_of_exists_shift_mem])
  | Γ, cut (φ := φ) d dn => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      rcases toProof dn with ⟨B, hB, ⟨bn⟩⟩
      refine ⟨A ++ B, by simp; grind, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        b.contra <| List.subset_def.mpr (by simp_all [Sequent.embed_append]; grind)
      have bn' : ⊢ᴸᴷ¹ ∼φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bn.contra <| List.subset_def.mpr (by simp_all [Sequent.embed_append]; grind)
      exact (Derivation.cut
        b' bn').contra <| List.subset_def.mpr (by simp_all; grind)

end Derivation2

lemma provable_iff_derivable2 {φ : Sentence L} : T ⊢ φ ↔ T ⊢!₂! (φ : Proposition L) := by
  constructor
  · rintro ⟨A, hA, d⟩
    exact Derivation2.cutMany A hA ⟨Derivation2.cast (Derivation.toDerivation2 T d) (by simp [Sequent.embed])⟩
  · rintro ⟨d⟩
    rcases d.toProof with ⟨A, hA, ⟨b⟩⟩
    exact ⟨A, hA, b.contra <| List.subset_def.mpr (by simp [Sequent.embed])⟩

end derivation2

end LO.FirstOrder
