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

omit [L.DecidableEq] in
@[simp] lemma Sequent.embed_append (A B : List (Sentence L)) :
    Sequent.embed (A ++ B) = Sequent.embed A ++ Sequent.embed B := by
  simp [Sequent.embed]

lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    (Rewriting.shifts Γ).toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

set_option linter.flexible false in
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
        (by
          intro x hx
          simp [shifts_toFinset_eq_image_shift] at hx ⊢
          grind))
  | Derivation.exs (Γ := Γ) (φ := φ) (t := t) dp =>
    Derivation2.exs (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simp))
  | Derivation.contraction d h =>
    Derivation2.wk (Derivation.toDerivation2 T d) (List.toFinset_mono h)
  | Derivation.cut (Γ := Γ) (Δ := Δ) (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (by intro x hx; simp at hx ⊢; grind))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by intro x hx; simp at hx ⊢; grind))

namespace Derivation2

noncomputable def cast {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Γ) (h : Γ = Δ := by simp) : T ⟹₂ Δ := by
  rcases h; exact d

noncomputable def contra {Γ Δ : Finset (Proposition L)} (d : T ⟹₂ Δ) (h : Δ ⊆ Γ := by simp) : T ⟹₂ Γ :=
  d.wk h

omit [L.DecidableEq] in
lemma mem_theory_append {A B : List (Sentence L)} (hA : ∀ ψ ∈ A, ψ ∈ T) (hB : ∀ ψ ∈ B, ψ ∈ T) :
    ∀ ψ ∈ A ++ B, ψ ∈ T := by
  intro ψ hψ
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact hA ψ hψ
  · exact hB ψ hψ

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
      cutMany A (by intro θ hθ; exact hA θ (by simp [hθ])) ⟨c⟩

set_option linter.flexible false in
noncomputable def toProof : {Γ : Finset (Proposition L)} → T ⟹₂ Γ →
    ∃ A : List (Sentence L), (∀ ψ ∈ A, ψ ∈ T) ∧ Nonempty (⊢ᴸᴷ¹ Γ.toList ++ ∼Sequent.embed A)
  | Γ, closed _ φ hp hn =>
      ⟨[], by simp, ⟨(Derivation.eta φ).contra (by intro x hx; simp at hx ⊢; grind)⟩⟩
  | Γ, axm φ hT hΓ =>
      ⟨[φ], by simp [hT], ⟨(Derivation.eta (φ : Proposition L)).contra (by intro x hx; simp at hx ⊢; grind)⟩⟩
  | Γ, verum h =>
      ⟨[], by simp, ⟨Derivation.verum.contra (by intro x hx; simp at hx ⊢; grind)⟩⟩
  | Γ, and (φ := φ) (ψ := ψ) h dφ dψ => by
      rcases toProof dφ with ⟨A, hA, ⟨bφ⟩⟩
      rcases toProof dψ with ⟨B, hB, ⟨bψ⟩⟩
      refine ⟨A ++ B, mem_theory_append hA hB, ⟨?_⟩⟩
      have bφ' : ⊢ᴸᴷ¹ φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bφ.contra (by intro x hx; simp at hx ⊢; grind)
      have bψ' : ⊢ᴸᴷ¹ ψ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bψ.contra (by intro x hx; simp at hx ⊢; grind)
      exact (Derivation.and bφ' bψ').contra (by intro x hx; simp at hx ⊢; grind)
  | Γ, or (φ := φ) (ψ := ψ) h d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ :: ψ :: Γ.toList ++ ∼Sequent.embed A :=
        b.contra (by intro x hx; simp at hx ⊢; grind)
      exact (Derivation.or b').contra (by intro x hx; simp at hx ⊢; grind)
  | Γ, all (φ := φ) h d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ Rewriting.free φ :: (Γ.toList ++ ∼Sequent.embed A)⁺ :=
        b.contra (by
          intro x hx
          suffices x = Rewriting.free φ ∨ (∃ a ∈ Γ, Rewriting.shift a = x) ∨
              ∃ a ∈ Sequent.embed A, Rewriting.shift a = ∼x by
            simpa [Rewriting.shifts] using this
          have hx' : (x = Rewriting.free φ ∨ ∃ a ∈ Γ, Rewriting.shift a = x) ∨
              ∼x ∈ Sequent.embed A := by
            simpa [Rewriting.shifts] using hx
          rcases hx' with (rfl | hx) | hx
          · exact Or.inl rfl
          · exact Or.inr <| Or.inl hx
          · rw [Sequent.embed] at hx
            rcases List.mem_map.mp hx with ⟨θ, hθ, hθx⟩
            exact Or.inr <| Or.inr ⟨Rewriting.emb θ,
              by rw [Sequent.embed]; exact List.mem_map.mpr ⟨θ, hθ, rfl⟩,
              by rw [←hθx]; simp⟩)
      exact (Derivation.all b').contra (by intro x hx; simp at hx ⊢; grind)
  | Γ, exs (φ := φ) h t d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ/[t] :: Γ.toList ++ ∼Sequent.embed A :=
        b.contra (by intro x hx; simp at hx ⊢; grind)
      exact (Derivation.exs (t := t) b').contra (by intro x hx; simp at hx ⊢; grind)
  | Γ, wk d h => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨b.contra ?_⟩⟩
      intro x hx
      simp at hx ⊢
      grind
  | _, shift (Γ := Γ) d => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      refine ⟨A, hA, ⟨?_⟩⟩
      exact b.shift.contra (by
        intro x hx
        suffices (∃ a ∈ Γ, Rewriting.shift a = x) ∨ ∼x ∈ Sequent.embed A by
          simpa [Rewriting.shifts] using this
        have hx' : (∃ a ∈ Γ, Rewriting.shift a = x) ∨
            ∃ a ∈ Sequent.embed A, Rewriting.shift a = ∼x := by
          simpa [Rewriting.shifts] using hx
        rcases hx' with hx | ⟨a, ha, hax⟩
        · exact Or.inl hx
        · right
          rw [Sequent.embed] at ha
          rcases List.mem_map.mp ha with ⟨θ, hθ, rfl⟩
          rw [←hax]
          rw [Sequent.embed]
          exact List.mem_map.mpr ⟨θ, hθ, by simp⟩)
  | Γ, cut (φ := φ) d dn => by
      rcases toProof d with ⟨A, hA, ⟨b⟩⟩
      rcases toProof dn with ⟨B, hB, ⟨bn⟩⟩
      refine ⟨A ++ B, mem_theory_append hA hB, ⟨?_⟩⟩
      have b' : ⊢ᴸᴷ¹ φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        b.contra (by intro x hx; simp at hx ⊢; grind)
      have bn' : ⊢ᴸᴷ¹ ∼φ :: Γ.toList ++ ∼Sequent.embed (A ++ B) :=
        bn.contra (by intro x hx; simp at hx ⊢; grind)
      exact (Derivation.cut
        b' bn').contra (by intro x hx; simp at hx ⊢; grind)

end Derivation2

set_option linter.flexible false in
lemma provable_iff_derivable2 {φ : Sentence L} : T ⊢ φ ↔ T ⊢!₂! (φ : Proposition L) := by
  constructor
  · rintro ⟨A, hA, d⟩
    exact Derivation2.cutMany A hA ⟨Derivation2.cast (Derivation.toDerivation2 T d) (by ext x; simp [Sequent.embed])⟩
  · rintro ⟨d⟩
    rcases d.toProof with ⟨A, hA, ⟨b⟩⟩
    exact ⟨A, hA, b.contra (by
      intro x hx
      simp at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · right
        rw [Sequent.embed] at hx
        exact List.mem_map.mp hx)⟩

end derivation2

end LO.FirstOrder
