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

open SubFormula Encodable

def sequentUpper (Γ : Sequent L) : ℕ := Γ.sup SubFormula.upper

lemma not_fvar?_sequentUpper {p : SyntacticFormula L} {Γ : Sequent L} (h : p ∈ Γ) : ¬fvar? p (sequentUpper Γ) :=
  not_fvar?_of_lt_upper p (by simpa[sequentUpper] using Finset.le_sup h)

inductive Decomp (t : SyntacticTerm L) (Γ : Sequent L) : SyntacticFormula L → Sequent L → Prop
  | rel {k} (r : L.rel k) (v) : nrel r v ∉ Γ → Decomp t Γ (rel r v) ∅ 
  | nrel {k} (r : L.rel k) (v) : rel r v ∉ Γ → Decomp t Γ (nrel r v) ∅
  | falsum : Decomp t Γ ⊥ ∅
  | andLeft (p q : SyntacticFormula L) : Decomp t Γ (p ⋏ q) {p}
  | andRight (p q : SyntacticFormula L) : Decomp t Γ (p ⋏ q) {q}
  | or (p q : SyntacticFormula L) : Decomp t Γ (p ⋎ q) {p, q}
  | all (p : SyntacticSubFormula L 1) : Decomp t Γ (∀' p) {⟦↦ &(sequentUpper Γ)⟧ p}
  | ex (p : SyntacticSubFormula L 1) : Decomp t Γ (∃' p) {⟦↦ t⟧ p}

abbrev codeFormula (s : ℕ) : ℕ := s.unpair.1.unpair.1

abbrev codeTerm (s : ℕ) : ℕ := s.unpair.1.unpair.2

abbrev codeIndex (p : SyntacticFormula L) (t : SyntacticTerm L) (i : ℕ) : ℕ := ((encode p).mkpair (encode t)).mkpair i

lemma codeIndex_inj {p q : SyntacticFormula L} {t u} {i j} (h : codeIndex p t i = codeIndex q u j) : p = q ∧ t = u ∧ i = j := by
  simp[codeIndex] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; simp

inductive SearchTreeAt (s : ℕ) : Sequent L → Sequent L → Prop
  | decomp (p : SyntacticFormula L) (Γ Δ : Sequent L) (i : ℕ) :
      p ∈ Γ → s = codeIndex p t i →
      Decomp t Γ p Δ → SearchTreeAt s (Δ ∪ Γ) Γ
  | refl (Γ : Sequent L) : (∀ p ∈ Γ, ∀ t, ∀ i, s ≠ codeIndex p t i) → SearchTreeAt s Γ Γ

local notation:25 Γ₁" ≺[" s:25 "] " Γ₂:80 => SearchTreeAt s Γ₁ Γ₂

lemma searchtreeAt_iff_decomp_of_index {Γ' Γ : Sequent L} {p} {t} {i} (hΓ : p ∈ Γ) (hs : s = codeIndex p t i) :
  Γ' ≺[s] Γ ↔ ∃ Δ, Decomp t Γ p Δ ∧ Γ' = Δ ∪ Γ :=
  ⟨by rintro (_ | _)
      case decomp u q Δ j hj _ h =>
        rcases codeIndex_inj (hs.symm.trans hj) with ⟨rfl, rfl, rfl⟩
        exact ⟨Δ, h, rfl⟩
      case refl H =>
        have := H p hΓ t i; contradiction,
   by rintro ⟨Δ, h, rfl⟩; exact SearchTreeAt.decomp p Γ Δ i hΓ hs h⟩

lemma searchtreeAt_iff_decomp_of_index' {Γ' Γ : Sequent L} {p} {t} {i} (hΓ : p ∈ Γ) :
  Γ' ≺[codeIndex p t i] Γ ↔ ∃ Δ, Decomp t Γ p Δ ∧ Γ' = Δ ∪ Γ := searchtreeAt_iff_decomp_of_index hΓ rfl

lemma subset_of_searchtreeAt {Γ' Γ : Sequent L} (h : Γ' ≺[s] Γ) : Γ ⊆ Γ' := by
  rcases h with (_ | _) <;> simp[Finset.subset_union_right]

inductive SearchTree.IsUnder (Γ : Sequent L) : ℕ × Sequent L → Prop
  | top : SearchTree.IsUnder Γ (0, Γ)
  | lt {s} {Γ₁ Γ₂ : Sequent L} : Γ₂ ≺[s] Γ₁ → SearchTree.IsUnder Γ (s, Γ₁) → SearchTree.IsUnder Γ (s + 1, Γ₂)

def SearchTreeUnder (Γ : Sequent L) := {p // SearchTree.IsUnder Γ p}

inductive SearchTree (Γ : Sequent L) : SearchTreeUnder Γ → SearchTreeUnder Γ → Prop
  | intro {s : ℕ} {Δ₁ Δ₂ : Sequent L}
      (h₁ : SearchTree.IsUnder Γ (s, Δ₁)) (h₂ : SearchTree.IsUnder Γ (s + 1, Δ₂)) :
      Δ₂ ≺[s] Δ₁ → SearchTree Γ ⟨(s + 1, Δ₂), h₂⟩ ⟨(s, Δ₁), h₁⟩

lemma searchTree_iff {Γ : Sequent L} {τ₁ τ₂ : SearchTreeUnder Γ} : 
    SearchTree Γ τ₂ τ₁ ↔ ∃ s, τ₁.val.1 = s ∧ τ₂.val.1 = s + 1 ∧ (τ₂.val.2 ≺[s] τ₁.val.2) := by
  constructor
  · rintro ⟨⟩; simp[*]
  · intro ⟨s, h₁, h₂, h⟩;
    have := SearchTree.intro (Γ := Γ) (s := s)
      (by simpa[←h₁] using τ₁.property) (by simpa[←h₂] using τ₂.property) h
    rcases h₁ with rfl; simpa[←h₂] using this

namespace SearchTree

section WellFounded

variable {Γ : Sequent L} (wf : WellFounded (SearchTree Γ))

noncomputable def SearchTree.recursion {C : SearchTreeUnder Γ → Sort _} 
  (τ) (h : ∀ τ₁, (∀ τ₂, SearchTree Γ τ₂ τ₁ → C τ₂) → C τ₁) : C τ :=
  WellFounded.fix wf h τ

noncomputable def syntacticMainLemma (τ : SearchTreeUnder Γ) : ⊢ᵀ τ.val.2 := by
  apply SearchTree.recursion wf τ
  intro ⟨⟨s, Δ⟩, hΔ⟩ ih; simp
  have ih : ∀ Δ₂ : Sequent L, Δ₂ ≺[s] Δ → ⊢ᵀ Δ₂ :=
    fun Δ₂ h => ih ⟨(s + 1, Δ₂), SearchTree.IsUnder.lt h hΔ⟩ (SearchTree.intro _ _ h)
  by_cases hs : ∀ p ∈ Δ, ∀ t, ∀ i, s ≠ codeIndex p t i
  case pos =>
    exact ih Δ (SearchTreeAt.refl Δ hs)
  case neg =>
    have : ∃ p ∈ Δ, ∃ t, ∃ i, s = codeIndex p t i := by simpa using hs
    choose p hp t i hi using this
    cases p using cases'
    case hverum =>
      exact DerivationCutRestricted.verum Δ hp
    case hfalsum =>
      have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨∅, Decomp.falsum, by simp⟩
      exact ih Δ this
    case hrel k r v =>
      by_cases hrv : nrel r v ∈ Δ
      · exact DerivationCutRestricted.axL Δ r v hp hrv
      · have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨∅, Decomp.rel r v hrv, by simp⟩
        exact ih Δ this
    case hnrel k r v =>
      by_cases hrv : rel r v ∈ Δ
      · exact DerivationCutRestricted.axL Δ r v hrv hp
      · have : Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨∅, Decomp.nrel r v hrv, by simp⟩
        exact ih Δ this
    case hand p q =>
      have dp : insert p Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨_, Decomp.andLeft p q, rfl⟩
      have dq : insert q Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨_, Decomp.andRight p q, rfl⟩
      have : ⊢ᵀ insert (p ⋏ q) Δ := DerivationCutRestricted.and Δ p q (ih _ dp) (ih _ dq)
      exact this.cast (by simp[hp])
    case hor p q =>
      have : {p, q} ∪ Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨_, Decomp.or p q, rfl⟩
      have : ⊢ᵀ insert (p ⋎ q) Δ := DerivationCutRestricted.or _ _ _ ((ih _ this).cast (by simp[Finset.insert_eq]))
      exact this.cast (by simp[hp])
    case hall p =>
      have : {⟦↦ &(sequentUpper Δ)⟧ p} ∪ Δ ≺[s] Δ := (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨_, Decomp.all p, rfl⟩
      have : ⊢ᵀ insert (⟦↦ &(sequentUpper Δ)⟧ p) Δ := ih _ this
      have : ⊢ᵀ insert (∀' p) Δ := DerivationCutRestricted.genelalizeByNewver₀ (not_fvar?_sequentUpper hp) (fun _ hq => not_fvar?_sequentUpper hq) this
      exact this.cast (by simp[hp])
    case hex p =>
      have : {⟦↦ t⟧ p} ∪ Δ ≺[s] Δ :=
        (searchtreeAt_iff_decomp_of_index hp hi).mpr ⟨_, Decomp.ex p, rfl⟩
      have : ⊢ᵀ insert (⟦↦ t⟧ p) Δ := ih _ this
      have : ⊢ᵀ insert (∃' p) Δ := DerivationCutRestricted.ex Δ t p this
      exact this.cast (by simp[hp])  

noncomputable def syntacticMainLemma_top : ⊢ᵀ Γ := syntacticMainLemma wf ⟨(0, Γ), SearchTree.IsUnder.top (Γ := Γ)⟩

end WellFounded

section NotWellFounded

variable {Γ : Sequent L} (nwf : ¬WellFounded (SearchTree Γ))

def SearchTreeUnder.top : SearchTreeUnder Γ := ⟨(0, Γ), IsUnder.top⟩

variable (Γ)

noncomputable def chainU : ℕ → SearchTreeUnder Γ := descendingChain (SearchTree Γ) SearchTreeUnder.top

noncomputable def chain (s : ℕ) : Sequent L := (chainU (Γ := Γ) s).val.2

variable {Γ}

lemma top_inaccessible : ¬Acc (SearchTree Γ) SearchTreeUnder.top := by
  intro A
  have : WellFounded (SearchTree Γ) := ⟨by
    intro ⟨τ, hτ⟩
    induction hτ
    case top => exact A
    case lt Γ₁ Γ₂ lt u₁ ih =>
      exact ih.inv (SearchTree.intro u₁ (IsUnder.lt lt u₁) lt)⟩
  contradiction

lemma chainU_spec : IsInfiniteDescendingChain (SearchTree Γ) (chainU Γ) :=
  isInfiniteDescendingChain_of_non_acc _ _ (top_inaccessible nwf)

lemma chainU_val_fst_eq (s : ℕ) : (chainU Γ s).val.1 = s := by
  induction' s with s ih <;> simp
  · exact rfl
  · rcases searchTree_iff.mp (chainU_spec nwf s) with ⟨_, hs, hss, _⟩
    rw[hss, ←hs, ih]

lemma chain_spec (s) : chain Γ (s + 1) ≺[s] chain Γ s := by
  rcases searchTree_iff.mp (chainU_spec nwf s) with ⟨s', hs', _, lt⟩
  have : s' = s := hs'.symm.trans (chainU_val_fst_eq nwf s)
  simpa[this] using lt

lemma chain_subset_chain_of_le {s u : ℕ} (h : s ≤ u) : chain Γ s ⊆ chain Γ u := by
  suffices : ∀ d, chain Γ s ⊆ chain Γ (s + d)
  simpa[Nat.add_sub_of_le h] using this (u - s)
  intro d; induction' d with d ih
  · rfl
  · simp[Nat.add_succ]; exact subset_trans ih $ subset_of_searchtreeAt (chain_spec nwf (s + d))

variable (Γ)

def chainSet : Set (SyntacticFormula L) := ⋃ s, chain Γ s

local notation "⛓️" => chainSet Γ

set_option linter.unusedVariables false in
def model (Γ : Sequent L) := SyntacticTerm L

instance : Inhabited (model Γ) := ⟨(default : SyntacticTerm L)⟩

instance model.structure : Structure L (model Γ) where
  func := SubTerm.func
  rel  := fun r v => nrel r v ∈ ⛓️

variable {Γ}

lemma mem_chain_iff {p} : p ∈ ⛓️ ↔ ∃ s, p ∈ chain Γ s := by simp[chainSet]

lemma mem_chain_of_mem_chainSet {p} (hp : p ∈ ⛓️) (t) (s : ℕ) :
    ∃ i, s ≤ codeIndex p t i ∧ p ∈ chain Γ (codeIndex p t i) := by
  rcases mem_chain_iff.mp hp with ⟨s', hp⟩
  have : (max s s') ≤ codeIndex p t (max s s') := Nat.right_le_mkpair _ _
  exact ⟨max s s', le_trans (by simp) this, by
    have : s' ≤ codeIndex p t (max s s') := le_trans (by simp) this
    exact chain_subset_chain_of_le nwf this hp⟩

lemma chain_succ_of_mem {p : SyntacticFormula L} (h : p ∈ ⛓️) (t) (s) : ∃ i Δ,
    s ≤ codeIndex p t i ∧
    Decomp t (chain Γ (codeIndex p t i)) p Δ ∧
      chain Γ (codeIndex p t i + 1) = Δ ∪ chain Γ (codeIndex p t i) := by
  rcases mem_chain_of_mem_chainSet nwf h t s with ⟨i, hi, hp⟩
  have : chain Γ (codeIndex p t i + 1) ≺[codeIndex p t i] chain Γ (codeIndex p t i) := chain_spec nwf (codeIndex p t i)
  rcases (searchtreeAt_iff_decomp_of_index' hp).mp this with ⟨Δ, hΔ, e⟩
  exact ⟨i, Δ, hi, hΔ, e⟩

lemma verum_nonmem_chain : ⊤ ∉ ⛓️ := by
  intro h; rcases chain_succ_of_mem nwf h default 0 with ⟨_, _, _, ⟨⟩, _⟩

lemma rel_nonmem_chain {k} {r : L.rel k} {v} : rel r v ∈ ⛓️ → nrel r v ∉ ⛓️ := by
  intro hpos hneg
  have : ∃ sₚ, rel r v ∈ chain Γ sₚ := mem_chain_iff.mp hpos
  rcases this with ⟨sₚ, hsₚ⟩
  have : ∃ i Δ, sₚ ≤ codeIndex (nrel r v) default i ∧
      Decomp default (chain Γ (codeIndex (nrel r v) default i)) (nrel r v) Δ ∧
      chain Γ (codeIndex (nrel r v) default i + 1) = Δ ∪ chain Γ (codeIndex (nrel r v) default i) :=
    chain_succ_of_mem nwf hneg default sₚ
  rcases this with ⟨i, Δ, hi, ⟨⟩, hΔ⟩
  have : rel r v ∈ chain Γ (codeIndex (nrel r v) default i) := chain_subset_chain_of_le nwf hi hsₚ
  contradiction

lemma and_mem_chain {p q : SyntacticFormula L} (h : p ⋏ q ∈ ⛓️) : p ∈ ⛓️ ∨ q ∈ ⛓️ := by
  have : ∃ i Δ, Decomp default (chain Γ (codeIndex (p ⋏ q) default i)) (p ⋏ q) Δ ∧
      chain Γ (codeIndex (p ⋏ q) default i + 1) = Δ ∪ chain Γ (codeIndex (p ⋏ q) default i) := by
    simpa using chain_succ_of_mem nwf h default 0
  rcases this with ⟨i, Δ, ⟨⟩, h⟩
  case andLeft => exact Or.inl $ mem_chain_iff.mpr ⟨codeIndex (p ⋏ q) default i + 1, by simp[h]⟩
  case andRight => exact Or.inr $ mem_chain_iff.mpr ⟨codeIndex (p ⋏ q) default i + 1, by simp[h]⟩

lemma or_mem_chain {p q : SyntacticFormula L} (h : p ⋎ q ∈ ⛓️) : p ∈ ⛓️ ∧ q ∈ ⛓️ := by
  have : ∃ i Δ, Decomp default (chain Γ (codeIndex (p ⋎ q) default i)) (p ⋎ q) Δ ∧
      chain Γ (codeIndex (p ⋎ q) default i + 1) = Δ ∪ chain Γ (codeIndex (p ⋎ q) default i) := by
    simpa using chain_succ_of_mem nwf h default 0
  rcases this with ⟨i, Δ, ⟨⟩, h⟩
  exact ⟨mem_chain_iff.mpr ⟨codeIndex (p ⋎ q) default i + 1, by simp[h]⟩,
         mem_chain_iff.mpr ⟨codeIndex (p ⋎ q) default i + 1, by simp[h]⟩⟩

lemma forall_mem_chain {p : SyntacticSubFormula L 1} (h : ∀' p ∈ ⛓️) : ∃ u, ⟦↦ u⟧ p ∈ ⛓️ := by
  have : ∃ i Δ, Decomp default (chain Γ (codeIndex (∀' p) default i)) (∀' p) Δ ∧
      chain Γ (codeIndex (∀' p) default i + 1) = Δ ∪ chain Γ (codeIndex (∀' p) default i) := by
    simpa using chain_succ_of_mem nwf h default 0
  rcases this with ⟨i, Δ, ⟨⟩, h⟩
  exact ⟨&(sequentUpper (chain Γ (codeIndex (∀' p) default i))),
    mem_chain_iff.mpr ⟨codeIndex (∀' p) default i + 1, by simp[h]⟩⟩

lemma ex_mem_chain {p : SyntacticSubFormula L 1} (h : ∃' p ∈ ⛓️) : ∀ u, ⟦↦ u⟧ p ∈ ⛓️ := by
  intro u
  have : ∃ i Δ, Decomp u (chain Γ (codeIndex (∃' p) u i)) (∃' p) Δ ∧
      chain Γ (codeIndex (∃' p) u i + 1) = Δ ∪ chain Γ (codeIndex (∃' p) u i) := by
    simpa using chain_succ_of_mem nwf h u 0
  rcases this with ⟨i, Δ, ⟨⟩, h⟩
  exact mem_chain_iff.mpr ⟨codeIndex (∃' p) u i + 1, by simp[h]⟩

@[simp] lemma val_model {e : Fin n → SyntacticTerm L} {ε} (t : SyntacticSubTerm L n) :
    SubTerm.val (model.structure Γ) e ε t = SubTerm.bind e ε t := by
  induction t <;> simp[*, SubTerm.val_func, SubTerm.bind_func]; rfl

@[simp] lemma model_rel {k} (r : L.rel k) (v : Fin k → SyntacticTerm L) :
    (model.structure Γ).rel r v ↔ nrel r v ∈ ⛓️ := of_eq rfl

lemma semanticMainLemma : (p : SyntacticFormula L) → p ∈ ⛓️ → ¬Val (model.structure Γ) SubTerm.fvar p
  | ⊤,        h => by by_contra; exact verum_nonmem_chain nwf h
  | ⊥,        _ => by simp
  | rel r v,  h => by simpa[eval_rel] using rel_nonmem_chain nwf h
  | nrel r v, h => by simpa[eval_nrel] using h
  | p ⋏ q,    h => by
      simp; intro _ _
      have : p ∈ ⛓️ ∨ q ∈ ⛓️ := and_mem_chain nwf h
      rcases this with (h | h)
      · have : ¬Val (model.structure Γ) SubTerm.fvar p := semanticMainLemma p h
        contradiction
      · have : ¬Val (model.structure Γ) SubTerm.fvar q := semanticMainLemma q h
        contradiction
  | p ⋎ q,    h => by
      have hpq : p ∈ ⛓️ ∧ q ∈ ⛓️ := or_mem_chain nwf h
      simp; rintro (h | h)
      · exact semanticMainLemma p hpq.1 h
      · exact semanticMainLemma q hpq.2 h
  | ∀' p,     h => by
      have : ∃ u, ⟦↦ u⟧ p ∈ ⛓️ := forall_mem_chain nwf h
      rcases this with ⟨u, hu⟩
      have : ¬Eval (model.structure Γ) ![u] SubTerm.fvar p := by
        simpa[Matrix.constant_eq_singleton] using semanticMainLemma (⟦↦ u⟧ p) hu
      simp; exact ⟨u, this⟩
  | ∃' p,     h => by
      simp; intro u
      have : ⟦↦ u⟧ p ∈ ⛓️ := ex_mem_chain nwf h u
      have : ¬Eval (model.structure Γ) ![u] SubTerm.fvar p := by
        simpa[Matrix.constant_eq_singleton] using semanticMainLemma (⟦↦ u⟧ p) this
      assumption
  termination_by semanticMainLemma p _ => p.complexity

lemma semanticMainLemma_top {p : SyntacticFormula L} (h : p ∈ Γ) : ¬Val (model.structure Γ) SubTerm.fvar p :=
  semanticMainLemma nwf p (mem_chain_iff.mpr ⟨0, by simpa[chain, chainU] using h⟩)

end NotWellFounded
  
end SearchTree

end FirstOrder