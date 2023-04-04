import Logic.Predicate.FirstOrder.Semantics
import Logic.Predicate.FirstOrder.Coding
import Logic.Vorspiel.Order

universe u v

namespace FirstOrder

variable {L : Language.{u}}
  [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]

def SubFormula.index (p : SyntacticFormula L) : ℕ  := Encodable.encode p

lemma SubFormula.index_inj {p q : SyntacticFormula L} : p.index = q.index ↔ p = q :=
  Encodable.encode_inj

open SubFormula

def sequentUpper (Γ : Sequent L) : ℕ := Γ.sup SubFormula.upper

lemma not_fvar?_sequentUpper {p : SyntacticFormula L} {Γ : Sequent L} (h : p ∈ Γ) : ¬fvar? p (sequentUpper Γ) :=
  not_fvar?_of_lt_upper p (by simpa[sequentUpper] using Finset.le_sup h)

inductive SearchTreeAux (s : ℕ) (Γ : Sequent L) : SyntacticFormula L → Sequent L → Prop
  | rel {k} (r : L.rel k) (v) :
      nrel r v ∉ Γ → SearchTreeAux s Γ (rel r v) ∅ 
  | nrel {k} (r : L.rel k) (v) :
      rel r v ∉ Γ → SearchTreeAux s Γ (nrel r v) ∅
  | falsum : SearchTreeAux s Γ ⊥ ∅
  | andLeft (p q : SyntacticFormula L) : SearchTreeAux s Γ (p ⋏ q) {p}
  | andRight (p q : SyntacticFormula L) : SearchTreeAux s Γ (p ⋏ q) {q}
  | or (p q : SyntacticFormula L) : SearchTreeAux s Γ (p ⋎ q) {p, q}
  | all (p : SyntacticSubFormula L 1) : SearchTreeAux s Γ (∀' p) {subst &(sequentUpper Γ) p}
  | ex (p : SyntacticSubFormula L 1) : SearchTreeAux s Γ (∃' p) ((SubTerm.enumLt s).image (subst · p))

inductive SearchTreeAt (s : ℕ) : Sequent L → Sequent L → Prop
  | decomp (p : SyntacticFormula L) (Γ Δ : Sequent L) :
      p.index = s.unpair.1 → p ∈ Γ → SearchTreeAux s.unpair.2 Γ p Δ → SearchTreeAt s (Δ ∪ Γ) Γ
  | refl (Γ : Sequent L) : (∀ p ∈ Γ, p.index ≠ s.unpair.1) → SearchTreeAt s Γ Γ

local notation:25 Γ₁" ≺[" s:25 "] " Γ₂:80 => SearchTreeAt s Γ₁ Γ₂

lemma searchtreeAt_iff_decomp_of_index {Γ' Γ : Sequent L} {p} (hp : p ∈ Γ) (hs : index p = s.unpair.1) :
  Γ' ≺[s] Γ ↔ ∃ Δ, SearchTreeAux s.unpair.2 Γ p Δ ∧ Γ' = Δ ∪ Γ :=
  ⟨by rintro (_ | _)
      case decomp q E hs' hq h =>
        have : p = q := SubFormula.index_inj.mp (by simp[hs, hs'])
        exact ⟨E, by simpa[this] using h, rfl⟩
      case refl H =>
        have := H p hp; contradiction,
   by rintro ⟨Δ, h, rfl⟩; exact SearchTreeAt.decomp p Γ Δ hs hp h⟩

inductive SearchTree.IsUnder (Γ : Sequent L) : ℕ × Sequent L → Prop
  | top : SearchTree.IsUnder Γ (0, Γ)
  | lt {s} {Γ₁ Γ₂ : Sequent L} : Γ₂ ≺[s] Γ₁ → SearchTree.IsUnder Γ (s, Γ₁) → SearchTree.IsUnder Γ (s + 1, Γ₂)

def SearchTreeUnder (Γ : Sequent L) := {p // SearchTree.IsUnder Γ p}

inductive SearchTree (Γ : Sequent L) : SearchTreeUnder Γ → SearchTreeUnder Γ → Prop
  | intro {s : ℕ} {Δ₁ Δ₂ : Sequent L} {h₁ : SearchTree.IsUnder Γ (s, Δ₁)} {h₂ : SearchTree.IsUnder Γ (s + 1, Δ₂)} :
      Δ₂ ≺[s] Δ₁ → SearchTree Γ ⟨(s + 1, Δ₂), h₂⟩ ⟨(s, Δ₁), h₁⟩

namespace SearchTree

section WellFounded

variable {Γ : Sequent L} (wf : WellFounded (SearchTree Γ))

noncomputable def SearchTree.recursion {C : SearchTreeUnder Γ → Sort _} 
  (τ) (h : ∀ τ₁, (∀ τ₂, SearchTree Γ τ₂ τ₁ → C τ₂) → C τ₁) : C τ :=
  WellFounded.recursion wf τ h

noncomputable def syntacticMainLemmaAux (τ : SearchTreeUnder Γ) : ⊩ τ.val.2 := by
  apply SearchTree.recursion wf τ
  intro ⟨⟨s, Δ⟩, hΔ⟩ ih; simp
  have ih : ∀ Δ₂ : Sequent L, Δ₂ ≺[s] Δ → ⊩ Δ₂ :=
    fun Δ₂ h => ih ⟨(s + 1, Δ₂), SearchTree.IsUnder.lt h hΔ⟩ (SearchTree.intro h)
  by_cases hs : ∀ p ∈ Δ, p.index ≠ s.unpair.fst
  case pos =>
    exact ih Δ (SearchTreeAt.refl Δ hs)
  case neg =>
    have : ∃ p ∈ Δ, index p = s.unpair.1 := by simpa using hs
    choose p hp using this
    cases p using cases'
    case hverum =>
      exact Derivation.verum Δ hp.1
    case hfalsum =>
      have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨∅, SearchTreeAux.falsum, by simp⟩
      exact ih Δ this
    case hrel k r v =>
      by_cases hrv : nrel r v ∈ Δ
      · exact Derivation.axL Δ r v hp.1 hrv
      · have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨∅, SearchTreeAux.rel r v hrv, by simp⟩
        exact ih Δ this
    case hnrel k r v =>
      by_cases hrv : rel r v ∈ Δ
      · exact Derivation.axL Δ r v hrv hp.1
      · have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨∅, SearchTreeAux.nrel r v hrv, by simp⟩
        exact ih Δ this
    case hand p q =>
      have dp : insert p Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨_, SearchTreeAux.andLeft p q, rfl⟩
      have dq : insert q Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨_, SearchTreeAux.andRight p q, rfl⟩
      have : ⊩ insert (p ⋏ q) Δ := Derivation.and Δ p q (ih _ dp) (ih _ dq)
      exact this.cast (by simp[hp.1])
    case hor p q =>
      have : {p, q} ∪ Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨_, SearchTreeAux.or p q, rfl⟩
      have : ⊩ insert (p ⋎ q) Δ := Derivation.or ((ih _ this).cast (by simp[Finset.insert_eq]))
      exact this.cast (by simp[hp.1])
    case hall p =>
      have : {subst &(sequentUpper Δ) p} ∪ Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨_, SearchTreeAux.all p, rfl⟩
      have : ⊩ insert (subst &(sequentUpper Δ) p) Δ := ih _ this
      have : ⊩ insert (∀' p) Δ := Derivation.genelalizeByNewver (not_fvar?_sequentUpper hp.1) (fun _ hq => not_fvar?_sequentUpper hq) this
      exact this.cast (by simp[hp.1])
    case hex p =>
      have : ((SubTerm.enumLt s.unpair.2).image (subst · p)) ∪ Δ ≺[s] Δ :=
        (searchtreeAt_iff_decomp_of_index hp.1 hp.2).mpr ⟨_, SearchTreeAux.ex p, rfl⟩
      have : ⊩ ((SubTerm.enumLt s.unpair.2).image (subst · p)) ∪ Δ := ih _ this
      have : ⊩ insert (∃' p) Δ := Derivation.exOfInstances (SubTerm.enumLtList s.unpair.2) p (by simpa[List.toFinset_map] using this)
      exact this.cast (by simp[hp.1])  
    
noncomputable def syntacticMainLemma : ⊩ Γ := syntacticMainLemmaAux wf ⟨(0, Γ), SearchTree.IsUnder.top (Γ := Γ)⟩

end WellFounded

end SearchTree

end FirstOrder