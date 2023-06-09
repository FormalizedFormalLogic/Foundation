import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Semantics
import Logic.Vorspiel.Logic

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable {L : Language.{u}} {μ : Type v} {μ₁ : Type v₁} {μ₂ : Type v₂}

namespace FirstOrder

namespace SubFormula
variable {M : Type w} (s : Structure L M)

def Eval' (ε : μ → M) : ∀ {n}, (Fin n → M) → SubFormula L μ n → Prop
  | _, _, ⊤        => True
  | _, _, ⊥        => False
  | _, e, rel p v  => s.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, nrel p v => ¬s.rel p (fun i => SubTerm.val s e ε (v i))
  | _, e, p ⋏ q    => p.Eval' ε e ∧ q.Eval' ε e
  | _, e, p ⋎ q    => p.Eval' ε e ∨ q.Eval' ε e
  | _, e, ∀' p     => ∀ x : M, (p.Eval' ε (x :> e))
  | _, e, ∃' p     => ∃ x : M, (p.Eval' ε (x :> e))

@[simp] lemma Eval'_neg (p : SubFormula L μ n) :
    Eval' s ε e (~p) = ¬Eval' s ε e p :=
  by induction p using rec' <;> simp[*, Eval', ←neg_eq, or_iff_not_imp_left]

section

variable {n : ℕ} (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

def Eval : SubFormula L μ n →L Prop where
  toFun := Eval' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[Eval']
  map_or' := by simp[Eval']
  map_neg' := by simp[Eval'_neg]
  map_imp' := by simp[imp_eq, Eval'_neg, ←neg_eq, Eval', imp_iff_not_or]

abbrev Eval! (M : Type w) [s : Structure L M] {n} (e : Fin n → M) (ε : μ → M) :
    SubFormula L μ n →L Prop := Eval s e ε

abbrev Val (ε : μ → M) : Formula L μ →L Prop := Eval s ![] ε

abbrev BVal (e : Fin n → M) : SubFormula L Empty n →L Prop := Eval s e Empty.elim

abbrev Val! (M : Type w) [s : Structure L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

abbrev BVal! (M : Type w) [s : Structure L M] (e : Fin n → M) :
    SubFormula L Empty n →L Prop := BVal s e

end

lemma eval_rel {k} {r : L.rel k} {v} :
    Eval s e ε (rel r v) ↔ s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_rel₀ {r : L.rel 0} :
    Eval s e ε (rel r ![]) ↔ s.rel r ![] := by simp[eval_rel, Matrix.empty_eq]

@[simp] lemma eval_rel₁ {r : L.rel 1} (t : SubTerm L μ n) :
    Eval s e ε (rel r ![t]) ↔ s.rel r ![t.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_rel₂ {r : L.rel 2} (t₁ t₂ : SubTerm L μ n) :
    Eval s e ε (rel r ![t₁, t₂]) ↔ s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

lemma eval_nrel {k} {r : L.rel k} {v} :
    Eval s e ε (nrel r v) ↔ ¬s.rel r (fun i => SubTerm.val s e ε (v i)) := of_eq rfl

@[simp] lemma eval_nrel₀ {r : L.rel 0} :
    Eval s e ε (nrel r ![]) ↔ ¬s.rel r ![] := by simp[eval_nrel, Matrix.empty_eq]

@[simp] lemma eval_nrel₁ {r : L.rel 1} (t : SubTerm L μ n) :
    Eval s e ε (nrel r ![t]) ↔ ¬s.rel r ![t.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_nrel₂ {r : L.rel 2} (t₁ t₂ : SubTerm L μ n) :
    Eval s e ε (nrel r ![t₁, t₂]) ↔ ¬s.rel r ![t₁.val s e ε, t₂.val s e ε] := by
  simp[eval_rel]; apply of_eq; congr
  funext i; cases' i using Fin.cases with i <;> simp

@[simp] lemma eval_all {p : SubFormula L μ (n + 1)} :
    Eval s e ε (∀' p) ↔ ∀ x : M, Eval s (x :> e) ε p := of_eq rfl

@[simp] lemma eval_univClosure {e'} {p : SubFormula L μ n} :
    Eval s e' ε (univClosure p) ↔ ∀ e, Eval s e ε p := by
  induction' n with n ih generalizing e' <;> simp[*, eq_finZeroElim]
  constructor
  · intro h e; simpa using h (Matrix.vecTail e) (Matrix.vecHead e)
  · intro h e x; exact h (x :> e)

@[simp] lemma eval_ex {p : SubFormula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

lemma eval_bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    Eval s e₂ ε₂ (bind bound free p) ↔
    Eval s (SubTerm.val s e₂ ε₂ ∘ bound) (SubTerm.val s e₂ ε₂ ∘ free) p := by
  induction p using rec' generalizing n₂ <;> simp[*, SubTerm.val_bind, Function.comp, bind_rel, bind_nrel, eval_rel, eval_nrel]
  · apply forall_congr'; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)
  · apply exists_congr; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)

lemma eval_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : SubFormula L μ₁ n₁) :
    Eval s e ε (map bound free p) ↔ Eval s (e ∘ bound) (ε ∘ free) p :=
  by simp[map, eval_bind, Function.comp]

@[simp] lemma eval_substs {k} (w : Fin k → SubTerm L μ n) (p : SubFormula L μ k) :
    Eval s e ε (substs w p) ↔ Eval s (fun i => (w i).val s e ε) ε p :=
  by simp[substs, eval_bind]; apply of_eq; congr

@[simp] lemma eval_emb (p : SubFormula L Empty n) :
    Eval s e ε (emb p) ↔ Eval s e Empty.elim p := by simp[emb, eval_map, Empty.eq_elim]

section Syntactic

variable (ε : ℕ → M)

@[simp] lemma eval_free (p : SyntacticSubFormula L (n + 1)) :
    Eval s e (a :>ₙ ε) (free p) ↔ Eval s (e <: a) ε p :=
  by simp[free, eval_bind]; apply of_eq; congr; funext x; cases x using Fin.lastCases <;> simp

@[simp] lemma eval_shift (p : SyntacticSubFormula L n) :
    Eval s e (a :>ₙ ε) (shift p) ↔ Eval s e ε p :=
  by simp[shift, eval_map]; apply of_eq; congr 

end Syntactic

section Hom
variable {M₁ : Type w₁} {M₂ : Type w₂} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma eval_hom_iff_of_qfree : ∀ {n} {e₁ : Fin n → M₁} {ε₁ : μ → M₁} {p : SubFormula L μ n}, p.qfree →
    (Eval s₁ e₁ ε₁ p ↔ Eval s₂ (φ ∘ e₁) (φ ∘ ε₁) p)
  | _, e₁, ε₁, ⊤,        _ => by simp
  | _, e₁, ε₁, ⊥,        _ => by simp
  | _, e₁, ε₁, rel r v,  _ => by simp[Function.comp, eval_rel, φ.hom_rel r, φ.hom_val]
  | _, e₁, ε₁, nrel r v, _ => by simp[Function.comp, eval_nrel, φ.hom_rel r, φ.hom_val]
  | _, e₁, ε₁, p ⋏ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]
  | _, e₁, ε₁, p ⋎ q,    h => by simp at h ⊢; simp[eval_hom_iff_of_qfree h.1, eval_hom_iff_of_qfree h.2]

lemma eval_hom_univClosure {n} {ε₁ : μ → M₁} {p : SubFormula L μ n} (hp : p.qfree) :
    Val s₂ (φ ∘ ε₁) (univClosure p) → Val s₁ ε₁ (univClosure p) := by
  simp; intro h e₁; exact (eval_hom_iff_of_qfree φ hp).mpr (h (φ ∘ e₁))

end Hom

end SubFormula

open Logic

instance semantics : Semantics (Sentence L) where
  struc := Structure.{u, u} L
  realize := (SubFormula.Val · Empty.elim)

abbrev Models (M : Type u) [s : Structure L M] : Sentence L →L Prop := Semantics.realize (self := semantics) s

postfix:max " ⊧₁ " => Models

abbrev ModelsTheory (M : Type u) [s : Structure L M] (T : Theory L) : Prop :=
  Semantics.realizeTheory (𝓢 := semantics) s T

infix:55 " ⊧₁* " => ModelsTheory

structure Theory.semanticGe (T₁ : Theory L₁) (T₂ : Theory L₂) :=
  carrier : Type u → Type u
  struc : (M₁ : Type u) → [Structure L₁ M₁] → Structure L₂ (carrier M₁)
  modelsTheory : ∀ {M₁ : Type u} [Structure L₁ M₁], M₁ ⊧₁* T₁ → ModelsTheory (s := struc M₁) T₂

structure Theory.semanticEquiv (T₁ : Theory L₁) (T₂ : Theory L₂) :=
  toLeft : T₁.semanticGe T₂
  toRight : T₂.semanticGe T₁

variable (L)

def ElementaryEquiv (M₁ M₂ : Type u) [Structure L M₁] [Structure L M₂] : Prop :=
  ∀ σ : Sentence L, M₁ ⊧₁ σ ↔ M₂ ⊧₁ σ

notation:50 M₁ " ≃ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂

variable {L}

section
variable {M : Type u} [s : Structure L M]

lemma models_def : M ⊧₁ = SubFormula.Val s Empty.elim := rfl

lemma models_iff {σ : Sentence L} : M ⊧₁ σ ↔ SubFormula.Val s Empty.elim σ := by simp[models_def]

lemma realize_def : Semantics.realize (self := semantics) s = SubFormula.Val s Empty.elim := rfl

lemma modelsTheory_iff {T : Theory L} : M ⊧₁* T ↔ (∀ ⦃p⦄, p ∈ T → M ⊧₁ p) := of_eq rfl

lemma models_iff_realize {σ : Sentence L} :
    M ⊧₁ σ ↔ Semantics.realize (self := semantics) s σ := of_eq rfl

lemma consequence_iff {T : Theory L} {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure L M], M ⊧₁* T → M ⊧₁ σ) :=
  of_eq rfl

lemma satisfiableₛ_iff {T : Theory L} :
    Semantics.Satisfiableₛ T ↔ ∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M), M ⊧₁* T :=
  of_eq rfl

lemma satisfiableₛ_intro {T : Theory L} (M : Type u) [i : Inhabited M] [s : Structure L M] (h : M ⊧₁* T) : Semantics.Satisfiableₛ T :=
⟨M, i, s, h⟩

lemma valid_iff {σ : Sentence L} :
    Semantics.Valid σ ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧₁ σ :=
  of_eq rfl

lemma validₛ_iff {T : Theory L} :
    Semantics.Validₛ T ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure L M], M ⊧₁* T :=
  of_eq rfl

@[refl]
lemma ElementaryEquiv.refl (M) [Structure L M] : M ≃ₑ[L] M := fun σ => by rfl

@[symm]
lemma ElementaryEquiv.symm {M₁ M₂} [Structure L M₁] [Structure L M₂] : (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₁) :=
  fun h σ => (h σ).symm

@[trans]
lemma ElementaryEquiv.trans {M₁ M₂ M₃ : Type u} [Structure L M₁] [Structure L M₂] [Structure L M₃] :
    (M₁ ≃ₑ[L] M₂) → (M₂ ≃ₑ[L] M₃) → (M₁ ≃ₑ[L] M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)

lemma ElementaryEquiv.models {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) :
    ∀ {σ : Sentence L}, M₁ ⊧₁ σ ↔ M₂ ⊧₁ σ := @h

lemma ElementaryEquiv.modelsTheory {M₁ M₂} [Structure L M₁] [Structure L M₂] (h : M₁ ≃ₑ[L] M₂) :
    ∀ {T : Theory L}, M₁ ⊧₁* T ↔ M₂ ⊧₁* T := by simp[modelsTheory_iff, h.models]

section Hom
variable {M₁ : Type u} {M₂ : Type u} [s₁ : Structure L M₁] [s₂ : Structure L M₂] (φ : M₁ →ₛ[L] M₂)
variable {e₁ : Fin n → M₁} {ε₁ : μ → M₁}

lemma models_hom_iff_of_qfree {σ : Sentence L} (hσ : σ.qfree) : M₁ ⊧₁ σ ↔ M₂ ⊧₁ σ := by
  simpa[Matrix.empty_eq, Empty.eq_elim] using
    SubFormula.eval_hom_iff_of_qfree (e₁ := finZeroElim) (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure {n} {σ : SubSentence L n} (hσ : σ.qfree) :
    M₂ ⊧₁ (univClosure σ) → M₁ ⊧₁ (univClosure σ) := by
  simpa[Matrix.empty_eq, Empty.eq_elim, models_iff] using
    SubFormula.eval_hom_univClosure (ε₁ := Empty.elim) φ hσ

lemma models_hom_univClosure_of_submodels [H : M₁ ⊆ₛ[L] M₂] {n} {σ : SubSentence L n} (hσ : σ.qfree) :
    M₂ ⊧₁ (univClosure σ) → M₁ ⊧₁ (univClosure σ) := models_hom_univClosure H.inclusion hσ

end Hom

end

namespace SubFormula

section onSubFormula₁

variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂} 

section 
variable {M : Type u} {s₂ : Structure L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma eval_onSubFormula₁ {p : SubFormula L₁ μ n} :
    Eval s₂ e ε (Φ.onSubFormula₁ p) ↔ Eval (Φ.onStructure s₂) e ε p :=
  by induction p using rec' <;>
    simp[*, SubTerm.val_onSubTerm, Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel,
      eval_rel, eval_nrel]

lemma models_onSubFormula₁ {σ : Sentence L₁} :
    Semantics.realize (self := semantics) s₂ (Φ.onSubFormula₁ σ) ↔ Semantics.realize (self := semantics) (Φ.onStructure s₂) σ :=
  by simp[Semantics.realize, Val, eval_onSubFormula₁]

lemma onTheory₁_models_onSubFormula₁ {T : Theory L₁} {σ : Sentence L₁} (h : T ⊨ σ) :
    Φ.onTheory₁ T ⊨ Φ.onSubFormula₁ σ := by
  intro M _ s hM
  have : Semantics.realize (self := semantics) (Φ.onStructure s) σ :=
    h M (Φ.onStructure s) (fun q hq => models_onSubFormula₁.mp $ hM (Set.mem_image_of_mem _ hq))
  exact models_onSubFormula₁.mpr this

end

section

variable
  (injf : ∀ k, Function.Injective (Φ.onFunc : L₁.func k → L₂.func k))
  (injr : ∀ k, Function.Injective (Φ.onRel : L₁.rel k → L₂.rel k))
  {M : Type u} [Inhabited M] (s₁ : Structure L₁ M)
  {n} (e : Fin n → M) (ε : μ → M)

lemma eval_extendStructure_onSubFormula₁ {p : SubFormula L₁ μ n} :
    Eval (Φ.extendStructure s₁) e ε (Φ.onSubFormula₁ p) ↔ Eval s₁ e ε p := by
  induction p using rec' <;> simp[*, SubTerm.val_extendStructure_onSubTerm Φ e ε injf s₁,
    Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel, eval_rel, eval_nrel]
  · case hrel k r v =>
    exact Structure.extendStructure_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))
  · case hnrel k r v =>
    simpa[not_iff_not] using
      Structure.extendStructure_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))

lemma models_extendStructure_onSubFormula₁ (σ : Sentence L₁) :
    Semantics.realize (self := semantics) (Φ.extendStructure s₁) (Φ.onSubFormula₁ σ) ↔ Semantics.realize (self := semantics) s₁ σ := by
  simp[Semantics.realize, Val, eval_extendStructure_onSubFormula₁ injf injr]

lemma valid_extendStructure_onSubFormula₁ {σ : Sentence L₁} :
    Semantics.Valid (Φ.onSubFormula₁ σ) → Semantics.Valid σ :=
  fun h _ _ s => (models_extendStructure_onSubFormula₁ injf injr s σ).mp (h _)

lemma onTheory₁_models_onSubFormula₁_iff {T : Theory L₁} {σ : Sentence L₁} :
    Φ.onTheory₁ T ⊨ Φ.onSubFormula₁ σ ↔ T ⊨ σ := by
  constructor
  · simp; intro h M _ s₁ hs₁
    exact (models_extendStructure_onSubFormula₁ injf injr s₁ σ).mp $
      h M (Φ.extendStructure s₁)
      (by simp[Semantics.realizeTheory, Language.Hom.onTheory₁];
          intro σ hσ; exact (models_extendStructure_onSubFormula₁ (Φ := Φ) injf injr s₁ σ).mpr (hs₁ hσ))
  · exact onTheory₁_models_onSubFormula₁

end

end onSubFormula₁

end SubFormula

@[simp] lemma ModelsTheory.empty [Structure L M] : M ⊧₁* (∅ : Theory L)  := by intro _; simp

lemma ModelsTheory.of_ss [Structure L M] {T U : Theory L} (h : M ⊧₁* U) (ss : T ⊆ U) : M ⊧₁* T :=
  fun _ hσ => h (ss hσ)

namespace Theory

variable {L₁ L₂ : Language.{u}}
variable {M : Type u} [s₂ : Structure L₂ M]
variable {Φ : L₁ →ᵥ L₂}

lemma modelsTheory_onTheory₁ {T₁ : Theory L₁} :
    ModelsTheory (s := s₂) (Φ.onTheory₁ T₁) ↔ ModelsTheory (s := Φ.onStructure s₂) T₁ :=
  by simp[SubFormula.models_onSubFormula₁, Language.Hom.onTheory₁, modelsTheory_iff, modelsTheory_iff (T := T₁)]

namespace semanticGe

def of_ss {T₁ : Theory L₁} {T₂ : Theory L₂} (ss : Φ.onTheory₁ T₁ ⊆ T₂) : T₂.semanticGe T₁ where
  carrier := id
  struc := fun _ s => Φ.onStructure s
  modelsTheory := fun {M _} h => (modelsTheory_onTheory₁ (M := M)).mp (h.of_ss ss)

protected def refl {T : Theory L} : T.semanticGe T where
  carrier := id
  struc := fun _ s => s
  modelsTheory := fun h => h

protected def trans {T₁ : Theory L₁} {T₂ : Theory L₂} {T₃ : Theory L₃}
  (g₃ : T₃.semanticGe T₂) (g₂ : T₂.semanticGe T₁) : T₃.semanticGe T₁ where
  carrier := g₂.carrier ∘ g₃.carrier
  struc := fun M₃ _ => let _ := g₃.struc M₃; g₂.struc (g₃.carrier M₃)
  modelsTheory := fun {M₃ _} h =>
    let _ := g₃.struc M₃
    g₂.modelsTheory (g₃.modelsTheory h)

end semanticGe

end Theory

namespace SubFormula

variable {L : Language.{u}} [L.Eq] {μ : Type v} (M : Type w) (s : Structure L M) [s.Eq]
  {n} (e : Fin n → M) (ε : μ → M)

@[simp] lemma eval_eq (t u : SubTerm L μ n) :
    Eval s e ε (rel Language.Eq.eq ![t, u]) ↔ t.val s e ε = u.val s e ε :=
  by simp

end SubFormula

section soundness

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable {P : SyntacticFormula L → Prop}

namespace DerivationCutRestricted

lemma sound : ∀ {Γ : Sequent L}, ⊢ᶜ[P] Γ → ∀ (M : Type u) [s : Structure L M] (ε : ℕ → M), ∃ p ∈ Γ, SubFormula.Val! M ε p
  | _, axL Δ r v hrel hnrel, M, s, ε => by
    by_cases h : s.rel r (SubTerm.val! M ![] ε ∘ v)
    · exact ⟨SubFormula.rel r v, hrel, h⟩
    · exact ⟨SubFormula.nrel r v, hnrel, h⟩
  | _, verum Δ h,            M, s, ε => ⟨⊤, h, by simp⟩
  | _, or Δ p q d,       M, s, ε => by
    have : SubFormula.Val! M ε p ∨ SubFormula.Val! M ε q ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by simpa using sound d M ε
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp[hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp[hq]⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, and Δ p q dp dq,       M, s, ε => by
    have : SubFormula.Val! M ε p ∨ ∃ r ∈ Δ, SubFormula.Val! M ε r := by simpa using sound dp M ε
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : SubFormula.Val! M ε q ∨ ∃ r ∈ Δ, SubFormula.Val! M ε r := by simpa using sound dq M ε
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp[hp, hq]⟩
      · exact ⟨r, by simp[hr], hhr⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, all Δ p d,             M, s, ε => by
    have : (∀ a : M, SubFormula.Eval! M ![a] ε p) ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by
      simpa[shifts, SubFormula.shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound d M (a :>ₙ ε)
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, ex Δ t p d,            M, s, ε => by
    have : SubFormula.Eval! M ![t.val! M ![] ε] ε p ∨ ∃ p ∈ Δ, SubFormula.Val! M ε p := by
      simpa[Matrix.constant_eq_singleton] using sound d M ε
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.val! M ![] ε, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, cut Δ Γ p _ dΔ dΓ,    M, s, ε => by
    have hΔ : SubFormula.Val! M ε p ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by simpa using dΔ.sound M ε
    have hΓ : ¬SubFormula.Val! M ε p ∨ ∃ q ∈ Γ, SubFormula.Val! M ε q := by simpa using dΓ.sound M ε
    rcases hΔ with (hΔ | ⟨q, hΔ, hq⟩)
    · rcases hΓ with (hΓ | ⟨q, hΓ, hq⟩)
      · contradiction
      · exact ⟨q, by simp[hΓ], hq⟩
    · exact ⟨q, by simp[hΔ], hq⟩

end DerivationCutRestricted

theorem soundness {T} {σ : Sentence L} : T ⊢ σ → T ⊨ σ := by
  simp[consequence_iff]; rintro ⟨Γ, hΓ, d⟩ M _ _ hT
  have : M ⊧₁ σ ∨ ∃ τ ∈ Γ, M ⊧₁ τ := by simpa using d.sound M default
  rcases this with (hσ | ⟨τ, hτ, hhτ⟩)
  · assumption
  · have : ~τ ∈ T := by rcases hΓ hτ with ⟨τ', hτ', rfl⟩; simpa[←SubFormula.neg_eq] using hτ'
    have : ¬ M ⊧₁ τ := by simpa using hT this
    contradiction

instance : Logic.Sound (Sentence L) := ⟨soundness⟩

end soundness

end FirstOrder

