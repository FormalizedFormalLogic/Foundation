import Logic.Predicate.FirstOrder.Basic
import Logic.Predicate.FirstOrder.Completeness.Coding
import Logic.Vorspiel.Order

namespace LO

namespace FirstOrder

namespace Completeness

open SubFormula DerivationWA Encodable
variable {L : Language.{u}}
  [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]
variable {T : Theory L} {Γ : Sequent L}

inductive Redux (T : Theory L) : Code L → Sequent L → Sequent L → Prop
  | axLRefl   {Γ : Sequent L} {k} (r : L.rel k) (v) :
    SubFormula.rel r v ∉ Γ ∨ SubFormula.nrel r v ∉ Γ → Redux T (Code.axL r v) Γ Γ
  | verumRefl {Γ : Sequent L} : ⊤ ∉ Γ → Redux T Code.verum Γ Γ
  | and₁      {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∈ Γ → Redux T (Code.and p q) (insert p Γ) Γ
  | and₂      {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∈ Γ → Redux T (Code.and p q) (insert q Γ) Γ
  | andRefl   {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋏ q ∉ Γ → Redux T (Code.and p q) Γ Γ
  | or        {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋎ q ∈ Γ → Redux T (Code.or p q) (insert p $ insert q Γ) Γ
  | orRefl    {Γ : Sequent L} {p q : SyntacticFormula L} : p ⋎ q ∉ Γ → Redux T (Code.or p q) Γ Γ
  | all       {Γ : Sequent L} {p : SyntacticSubFormula L 1} : ∀' p ∈ Γ → Redux T (Code.all p) (insert ([→ &(newVar Γ)].hom p) Γ) Γ
  | allRefl   {Γ : Sequent L} {p : SyntacticSubFormula L 1} : ∀' p ∉ Γ → Redux T (Code.all p) Γ Γ
  | ex        {Γ : Sequent L} {p : SyntacticSubFormula L 1} {t : SyntacticTerm L} :
    ∃' p ∈ Γ → Redux T (Code.ex p t) (insert ([→ t].hom p) Γ) Γ
  | exRefl    {Γ : Sequent L} {p : SyntacticSubFormula L 1} {t : SyntacticTerm L} :
    ∃' p ∉ Γ → Redux T (Code.ex p t) Γ Γ
  | id        {Γ : Sequent L} {σ : Sentence L} (hσ : σ ∈ T) : Redux T (Code.id σ) (insert (~Rew.embl σ) Γ) Γ
  | idRefl    {Γ : Sequent L} {σ : Sentence L} (hσ : σ ∉ T) : Redux T (Code.id σ) Γ Γ

local notation:25 Δ₁" ≺[" c:25 "] " Δ₂:80 => Redux T c Δ₁ Δ₂

inductive ReduxNat (T : Theory L) (s : ℕ) : Sequent L → Sequent L → Prop
  | redux {c : Code L} : decode s.unpair.1 = some c → ∀ {Δ₂ Δ₁}, Redux T c Δ₂ Δ₁ → ReduxNat T s Δ₂ Δ₁
  | refl : decode (α := Code L) s.unpair.1 = none → ∀ Δ, ReduxNat T s Δ Δ

local notation:25 Δ₁" ≺⟨" s:25 "⟩ " Δ₂:80 => ReduxNat T s Δ₁ Δ₂

lemma Redux.antimonotone {c : Code L} {Δ₂ Δ₁ : Sequent L} (h : Δ₂ ≺[c] Δ₁) : Δ₁ ⊆ Δ₂ := by
  cases h <;> simp[Finset.subset_insert]; { intro x hx; simp; exact Or.inr $ Or.inr hx }

lemma ReduxNat.antimonotone {s : ℕ} {Δ₂ Δ₁ : Sequent L} (h : Δ₂ ≺⟨s⟩ Δ₁) : Δ₁ ⊆ Δ₂ := by
  cases h; { exact Redux.antimonotone (by assumption) }; { rfl }

lemma ReduxNat.toRedux {c : Code L} {i} {Δ₂ Δ₁ : Sequent L} (h : Δ₂ ≺⟨(encode c).pair i⟩ Δ₁) : Δ₂ ≺[c] Δ₁ := by
  rcases h with (⟨h, r⟩ | ⟨h⟩); { simp at h; simpa[h] using r }; { simp at h }

inductive SearchTreeAux (T : Theory L) (Γ : Sequent L) : ℕ → Sequent L → Type u
  | zero : SearchTreeAux T Γ 0 Γ
  | succ : SearchTreeAux T Γ s Δ₁ → ReduxNat T s Δ₂ Δ₁ → SearchTreeAux T Γ (s + 1) Δ₂

def SearchTree (T : Theory L) (Γ : Sequent L) := (s : ℕ) × (Δ : Sequent L) × SearchTreeAux T Γ s Δ

namespace SearchTree

abbrev rank (τ : SearchTree T Γ) := τ.1

abbrev seq (τ : SearchTree T Γ) := τ.2.1

inductive Lt (T : Theory L) (Γ : Sequent L) : SearchTree T Γ → SearchTree T Γ → Prop
  | intro {s} {Δ₂ Δ₁} (a : SearchTreeAux T Γ s Δ₁) (r : ReduxNat T s Δ₂ Δ₁) : Lt T Γ ⟨s + 1, Δ₂, a.succ r⟩ ⟨s, Δ₁, a⟩

lemma rank_of_lt {τ₁ τ₂ : SearchTree T Γ} (h : Lt T Γ τ₂ τ₁) : τ₂.rank = τ₁.rank + 1 := by
  cases h; simp

lemma seq_of_lt {τ₁ τ₂ : SearchTree T Γ} (h : Lt T Γ τ₂ τ₁) : τ₂.seq ≺⟨τ₁.rank⟩ τ₁.seq := by
  cases h; simp[rank, seq]; assumption

instance : Top (SearchTree T Γ) := ⟨⟨0, Γ, SearchTreeAux.zero⟩⟩ 

@[simp] lemma rank_top : (⊤ : SearchTree T Γ).rank = 0 := rfl

@[simp] lemma seq_top : (⊤ : SearchTree T Γ).seq = Γ := rfl

end SearchTree

section WellFounded

open DerivationCRWA
variable (wf : WellFounded (SearchTree.Lt T Γ))

noncomputable def SearchTree.recursion {C : SearchTree T Γ → Sort v}
  (τ) (h : ∀ τ₁, (∀ τ₂, SearchTree.Lt T Γ τ₂ τ₁ → C τ₂) → C τ₁) : C τ :=
  WellFounded.fix wf h τ

noncomputable def syntacticMainLemma (σ : SearchTree T Γ) : T ⊢ᵀ σ.seq := by
  apply SearchTree.recursion wf σ
  intro ⟨s, Δ₁, a₁⟩ ih; simp
  have ih' : ∀ {Δ₂}, ReduxNat T s Δ₂ Δ₁ → T ⊢ᵀ Δ₂ := fun {Δ₂} r => ih ⟨s + 1, Δ₂, a₁.succ r⟩ (SearchTree.Lt.intro a₁ r)
  rcases hs : (decode s.unpair.1 : Option (Code L)) with (_ | c)
  { have : ReduxNat T s Δ₁ Δ₁ := ReduxNat.refl hs Δ₁
    exact ih' this }
  { cases c
    case axL r v =>
    { by_cases hr : rel r v ∈ Δ₁ ∧ nrel r v ∈ Δ₁
      { exact axL r v hr.1 hr.2 }
      { exact ih' (ReduxNat.redux hs $ Redux.axLRefl r v (not_and_or.mp hr)) } }
    case verum =>
    { by_cases h : ⊤ ∈ Δ₁
      { exact verum h }
      { exact ih' (ReduxNat.redux hs $ Redux.verumRefl h) } }
    case and p q =>
    { by_cases h : p ⋏ q ∈ Δ₁
      { have rp : insert p Δ₁ ≺[Code.and p q] Δ₁ := Redux.and₁ h
        have rq : insert q Δ₁ ≺[Code.and p q] Δ₁ := Redux.and₂ h
        have dp : T ⊢ᵀ insert p Δ₁ := ih' (ReduxNat.redux hs rp)
        have dq : T ⊢ᵀ insert q Δ₁ := ih' (ReduxNat.redux hs rq)
        exact DerivationCRWA.and h dp dq }
      { exact ih' (ReduxNat.redux hs $ Redux.andRefl h) } }
    case or p q =>
    { by_cases h : p ⋎ q ∈ Δ₁
      { have : insert p (insert q Δ₁) ≺[Code.or p q] Δ₁ := Redux.or h
        have : T ⊢ᵀ (insert p $ insert q Δ₁) := ih' (ReduxNat.redux hs this)
        exact DerivationCRWA.or h this }
      { exact ih' (ReduxNat.redux hs $ Redux.orRefl h) } }
    case all p =>
    { by_cases h : ∀' p ∈ Δ₁
      { have : insert ([→ &(newVar Δ₁)].hom p) Δ₁ ≺[Code.all p] Δ₁ := Redux.all h
        have : T ⊢ᵀ insert ([→ &(newVar Δ₁)].hom p) Δ₁ := ih' (ReduxNat.redux hs this)
        exact DerivationWA.all_nvar h this }
      { exact ih' (ReduxNat.redux hs $ Redux.allRefl h) } }
    case ex p t =>
    { by_cases h : ∃' p ∈ Δ₁
      { have : insert ([→ t].hom p) Δ₁ ≺[Code.ex p t] Δ₁ := Redux.ex h
        have : T ⊢ᵀ insert ([→ t].hom p) Δ₁ := ih' (ReduxNat.redux hs this)
        exact DerivationCRWA.ex h this }
      { exact ih' (ReduxNat.redux hs $ Redux.exRefl h) } }
    case id σ =>
    { by_cases h : σ ∈ T
      { have : insert (~Rew.embl σ) Δ₁ ≺[Code.id σ] Δ₁ := Redux.id h
        have : T ⊢ᵀ insert (~Rew.embl σ) Δ₁ := ih' (ReduxNat.redux hs this)
        exact DerivationCRWA.id h this }
      { exact ih' (ReduxNat.redux hs $ Redux.idRefl h) } } }

noncomputable def syntacticMainLemmaTop : T ⊢ᵀ Γ := syntacticMainLemma wf ⊤

end WellFounded

section NotWellFounded

variable (nwf : ¬WellFounded (SearchTree.Lt T Γ))

noncomputable def chainU (T : Theory L) (Γ : Sequent L) : ℕ → SearchTree T Γ := descendingChain (SearchTree.Lt T Γ) ⊤

noncomputable def chain (T : Theory L) (Γ : Sequent L) (s : ℕ) : Sequent L := (chainU T Γ s).seq

def chainSet (T : Theory L) (Γ : Sequent L) : Set (SyntacticFormula L) := ⋃ s : ℕ, chain T Γ s

local notation "⛓️[" s "]" => chain T Γ s

local notation "⛓️" => chainSet T Γ

lemma top_inaccessible : ¬Acc (SearchTree.Lt T Γ) ⊤ := by
  intro A
  have : WellFounded (SearchTree.Lt T Γ) := ⟨by
    rintro ⟨s, Δ, a⟩
    induction a
    case zero => exact A
    case succ s Δ₁ Δ₂ a r ih => exact ih.inv (SearchTree.Lt.intro a r)⟩
  contradiction

lemma chainU_spec : IsInfiniteDescendingChain (SearchTree.Lt T Γ) (chainU T Γ) :=
  isInfiniteDescendingChain_of_non_acc _ _ (top_inaccessible nwf)

lemma chainU_val_fst_eq (s : ℕ) : (chainU T Γ s).rank = s := by
  induction' s with s ih <;> simp[SearchTree.rank]
  · exact rfl
  · simpa[ih] using SearchTree.rank_of_lt (chainU_spec nwf s)
    
lemma chain_spec (s) : ⛓️[s + 1] ≺⟨s⟩ ⛓️[s] :=
  by simpa[chainU_val_fst_eq nwf s] using SearchTree.seq_of_lt (chainU_spec nwf s)

lemma chain_monotone {s u : ℕ} (h : s ≤ u) : ⛓️[s] ⊆ ⛓️[u] := by
  suffices : ∀ d, ⛓️[s] ⊆ ⛓️[s + d]
  simpa[Nat.add_sub_of_le h] using this (u - s)
  intro d; induction' d with d ih
  · rfl
  · simp[Nat.add_succ]; exact subset_trans ih $ ReduxNat.antimonotone (chain_spec nwf (s + d))  

lemma chain_spec' (c : Code L) (i : ℕ) : ⛓️[(encode c).pair i + 1] ≺[c] ⛓️[(encode c).pair i] := (chain_spec nwf _).toRedux

lemma chainSet_verum : ⊤ ∉ ⛓️ := by
  simp[chainSet]; intro s h
  have : ⊤ ∈ ⛓️[(encode (Code.verum : Code L)).pair s] := chain_monotone nwf (Nat.right_le_pair _ _) h
  have : ¬⊤ ∈ ⛓️[(encode (Code.verum : Code L)).pair s] := by
    have : ⛓️[(encode Code.verum).pair s + 1] ≺[Code.verum] ⛓️[(encode Code.verum).pair s] := chain_spec' nwf _ _
    generalize ⛓️[(encode (Code.verum : Code L)).pair s + 1] = Δ' at this
    rcases this; assumption
  contradiction
  
lemma chainSet_axL {k} (r : L.rel k) (v : Fin k → SyntacticTerm L) : rel r v ∉ ⛓️ ∨ nrel r v ∉ ⛓️ := by
  by_contra h
  have : (∃ s₁, rel r v ∈ ⛓️[s₁]) ∧ (∃ s₂, nrel r v ∈ ⛓️[s₂])
  { have h : rel r v ∈ ⛓️ ∧ nrel r v ∈ ⛓️ := by simpa[not_or] using h
    simpa[chainSet] using h }
  rcases this with ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩
  have : rel r v ∈ ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂)] ∧ nrel r v ∈ ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂)]
  { exact ⟨chain_monotone nwf (le_trans (by simp) (Nat.right_le_pair _ _)) hs₁,
    chain_monotone nwf (le_trans (by simp) (Nat.right_le_pair _ _)) hs₂⟩ }
  have : ¬(rel r v ∈ ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂)] ∧ nrel r v ∈ ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂)])
  { rw[not_and_or]
    have : ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂) + 1] ≺[Code.axL r v] ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂)] := chain_spec' nwf _ _
    generalize ⛓️[(encode $ Code.axL r v).pair (max s₁ s₂) + 1] = Δ' at this
    rcases this; assumption }
  contradiction

lemma chainSet_and {p q : SyntacticFormula L} (h : p ⋏ q ∈ ⛓️) : p ∈ ⛓️ ∨ q ∈ ⛓️ := by
  have : ∃ s, p ⋏ q ∈ ⛓️[s] := by simpa[chainSet] using h
  rcases this with ⟨s, hs⟩
  have : ⛓️[(encode $ Code.and p q).pair s + 1] ≺[Code.and p q] ⛓️[(encode $ Code.and p q).pair s] := chain_spec' nwf _ _
  generalize hΔ : ⛓️[(encode $ Code.and p q).pair s + 1] = Δ at this
  rcases this
  case and₁ =>
  { exact Or.inl (Set.mem_iUnion.mpr ⟨(encode $ Code.and p q).pair s + 1, by simp[hΔ]⟩) }
  case and₂ =>
  { exact Or.inr (Set.mem_iUnion.mpr ⟨(encode $ Code.and p q).pair s + 1, by simp[hΔ]⟩) }
  case andRefl =>
  { have : p ⋏ q ∈ ⛓️[(encode $ Code.and p q).pair s] := chain_monotone nwf (Nat.right_le_pair _ _) hs
    contradiction }

lemma chainSet_or {p q : SyntacticFormula L} (h : p ⋎ q ∈ ⛓️) : p ∈ ⛓️ ∧ q ∈ ⛓️ := by
  have : ∃ s, p ⋎ q ∈ ⛓️[s] := by simpa[chainSet] using h
  rcases this with ⟨s, hs⟩
  have : ⛓️[(encode $ Code.or p q).pair s + 1] ≺[Code.or p q] ⛓️[(encode $ Code.or p q).pair s] := chain_spec' nwf _ _
  generalize hΔ : ⛓️[(encode $ Code.or p q).pair s + 1] = Δ at this
  rcases this
  { exact ⟨Set.mem_iUnion.mpr ⟨(encode $ Code.or p q).pair s + 1, by simp[hΔ]⟩,
    Set.mem_iUnion.mpr ⟨(encode $ Code.or p q).pair s + 1, by simp[hΔ]⟩⟩ }
  { have : p ⋎ q ∈ ⛓️[(encode $ Code.or p q).pair s] := chain_monotone nwf (Nat.right_le_pair _ _) hs
    contradiction }

lemma chainSet_all {p : SyntacticSubFormula L 1} (h : ∀' p ∈ ⛓️) : ∃ t, [→ t].hom p ∈ ⛓️ := by
  have : ∃ s, ∀' p ∈ ⛓️[s] := by simpa[chainSet] using h
  rcases this with ⟨s, hs⟩
  have : ⛓️[(encode $ Code.all p).pair s + 1] ≺[Code.all p] ⛓️[(encode $ Code.all p).pair s] := chain_spec' nwf _ _
  generalize hΔ : ⛓️[(encode $ Code.all p).pair s + 1] = Δ at this
  rcases this
  { exact ⟨&(newVar ⛓️[(encode $ Code.all p).pair s]), Set.mem_iUnion.mpr ⟨(encode $ Code.all p).pair s + 1, by simp[hΔ]⟩⟩ }
  { have : ∀' p ∈ ⛓️[(encode $ Code.all p).pair s] := chain_monotone nwf (Nat.right_le_pair _ _) hs
    contradiction }

lemma chainSet_ex {p : SyntacticSubFormula L 1} (h : ∃' p ∈ ⛓️) : ∀ t, [→ t].hom p ∈ ⛓️ := fun t => by
  have : ∃ s, ∃' p ∈ ⛓️[s] := by simpa[chainSet] using h
  rcases this with ⟨s, hs⟩
  have : ⛓️[(encode $ Code.ex p t).pair s + 1] ≺[Code.ex p t] ⛓️[(encode $ Code.ex p t).pair s] := chain_spec' nwf _ _
  generalize hΔ : ⛓️[(encode $ Code.ex p t).pair s + 1] = Δ at this
  rcases this
  { exact Set.mem_iUnion.mpr ⟨(encode $ Code.ex p t).pair s + 1, by simp[hΔ]⟩ }
  { have : ∃' p ∈ ⛓️[(encode $ Code.ex p t).pair s] := chain_monotone nwf (Nat.right_le_pair _ _) hs
    contradiction }

lemma chainSet_id {σ : Sentence L} (h : σ ∈ T) : ~Rew.embl σ ∈ ⛓️ := by
  have : ⛓️[(encode $ Code.id σ).pair 0 + 1] ≺[Code.id σ] ⛓️[(encode $ Code.id σ).pair 0] := chain_spec' nwf _ _
  generalize hΔ : ⛓️[(encode $ Code.id σ).pair 0 + 1] = Δ
  rw[hΔ] at this; rcases this
  { exact Set.mem_iUnion.mpr ⟨(encode $ Code.id σ).pair 0 + 1, by simp[hΔ]⟩ }
  { contradiction }

set_option linter.unusedVariables false in
def Model (T : Theory L) (Γ : Sequent L) := SyntacticTerm L

instance : Inhabited (Model T Γ) := ⟨(default : SyntacticTerm L)⟩

instance Model.structure (T : Theory L) (Γ : Sequent L) : Structure L (Model T Γ) where
  func := fun _ f v => SubTerm.func f v
  rel  := fun _ r v => nrel r v ∈ chainSet T Γ

@[simp] lemma Model.val {e : Fin n → SyntacticTerm L} {ε} (t : SyntacticSubTerm L n) :
    SubTerm.val (Model.structure T Γ) e ε t = Rew.bind e ε t := by
  induction t <;> simp[*, SubTerm.val_func, Rew.func]; rfl

@[simp] lemma Model.rel {k} (r : L.rel k) (v : Fin k → SyntacticTerm L) :
    (Model.structure T Γ).rel r v ↔ nrel r v ∈ ⛓️ := of_eq rfl

lemma semanticMainLemma_val : (p : SyntacticFormula L) → p ∈ ⛓️ → ¬Val (Model.structure T Γ) SubTerm.fvar p
  | ⊤,        h => by by_contra; exact chainSet_verum nwf h
  | ⊥,        _ => by simp
  | rel r v,  h => by { rcases chainSet_axL nwf r v with (hr | hr); { contradiction }; { simpa[eval_rel] using hr } } 
  | nrel r v, h => by simpa[eval_nrel] using h
  | p ⋏ q,    h => by
      simp; intro _ _
      have : p ∈ ⛓️ ∨ q ∈ ⛓️ := chainSet_and nwf h
      rcases this with (h | h)
      · have : ¬Val (Model.structure T Γ) SubTerm.fvar p := semanticMainLemma_val p h
        contradiction
      · have : ¬Val (Model.structure T Γ) SubTerm.fvar q := semanticMainLemma_val q h
        contradiction
  | p ⋎ q,    h => by
      have hpq : p ∈ ⛓️ ∧ q ∈ ⛓️ := chainSet_or nwf h
      simp; rintro (h | h)
      · exact semanticMainLemma_val p hpq.1 h
      · exact semanticMainLemma_val q hpq.2 h
  | ∀' p,     h => by
      have : ∃ u, [→ u].hom p ∈ ⛓️ := chainSet_all nwf h
      rcases this with ⟨u, hu⟩
      have : ¬Eval (Model.structure T Γ) ![u] SubTerm.fvar p := by
        simpa[eval_substs, Matrix.constant_eq_singleton] using semanticMainLemma_val ([→ u].hom p) hu
      simp; exact ⟨u, this⟩
  | ∃' p,     h => by
      simp; intro u
      have : [→ u].hom p ∈ ⛓️ := chainSet_ex nwf h u
      have : ¬Eval (Model.structure T Γ) ![u] SubTerm.fvar p := by
        simpa[eval_substs, Matrix.constant_eq_singleton] using semanticMainLemma_val ([→ u].hom p) this
      assumption
  termination_by semanticMainLemma_val p _ => p.complexity

lemma Model.models : Model T Γ ⊧* T := by
  intro σ hσ; simpa using semanticMainLemma_val nwf _ (chainSet_id nwf hσ)

lemma semanticMainLemmaTop {p : SyntacticFormula L} (h : p ∈ Γ) : ¬Val (Model.structure T Γ) SubTerm.fvar p :=
  semanticMainLemma_val nwf p (Set.mem_iUnion.mpr ⟨0, by simp[chain, chainU, h]⟩)

end NotWellFounded

end Completeness

end FirstOrder

end LO