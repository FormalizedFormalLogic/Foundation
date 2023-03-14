import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Semantics
import Logic.Vorspiel.Logic

universe u u₁ u₂ v v₁ v₂ w w₁ w₂

variable {L : Language.{u}} {μ : Type v}

namespace FirstOrder

namespace SubFormula
variable {n : ℕ} {M : Type w} (s : Structure₁ L M)
  (e : Fin n → M) (e₂ : Fin n₂ → M) (ε : μ → M) (ε₂ : μ₂ → M)

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

def Eval : SubFormula L μ n →L Prop where
  toFun := Eval' s ε e
  map_top' := rfl
  map_bot' := rfl
  map_and' := by simp[Eval']
  map_or' := by simp[Eval']
  map_neg' := by simp[Eval'_neg]
  map_imp' := by simp[imp_eq, Eval'_neg, ←neg_eq, Eval', imp_iff_not_or]

abbrev Eval! (M : Type w) [s : Structure₁ L M] {n} (e : Fin n → M) (ε : μ → M) :
    SubFormula L μ n →L Prop := Eval s e ε

abbrev Val (ε : μ → M) : Formula L μ →L Prop := Eval s ![] ε

abbrev Val! (M : Type w) [s : Structure₁ L M] (ε : μ → M) :
    Formula L μ →L Prop := Val s ε

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

@[simp] lemma eval_ex {p : SubFormula L μ (n + 1)} :
    Eval s e ε (∃' p) ↔ ∃ x : M, Eval s (x :> e) ε p := of_eq rfl

lemma eval_bind (bound : Fin n₁ → SubTerm L μ₂ n₂) (free : μ₁ → SubTerm L μ₂ n₂) (p : SubFormula L μ₁ n₁) :
    Eval s e₂ ε₂ (bind bound free p) =
    Eval s (SubTerm.val s e₂ ε₂ ∘ bound) (SubTerm.val s e₂ ε₂ ∘ free) p := by
  induction p using rec' generalizing n₂ <;> simp[*, SubTerm.val_bind, Function.comp,
    bind_rel, bind_nrel, eval_rel, eval_nrel]
  · apply forall_congr'; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)
  · apply exists_congr; intros a; apply of_eq; congr; exact funext $ Fin.cases (by simp) (by simp)

lemma eval_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (e : Fin n₂ → M) (ε : μ₂ → M) (p : SubFormula L μ₁ n₁) :
    Eval s e ε (map bound free p) = Eval s (e ∘ bound) (ε ∘ free) p :=
  by simp[map, eval_bind, Function.comp]

lemma eval_subst (u : SubTerm L μ n) (p : SubFormula L μ (n + 1)) :
    Eval s e ε (subst u p) = Eval s (e <: u.val s e ε) ε p :=
  by simp[subst, eval_bind]; apply of_eq; congr ; exact funext $ Fin.lastCases (by simp) (by simp)

section Syntactic
variable (Ψ : ℕ → M)

end Syntactic

end SubFormula

instance semantics : Semantics (Sentence L) where
  struc := Structure₁.{u, u} L
  realize := (SubFormula.Val · Empty.elim)

abbrev Models (M : Type u) [s : Structure₁ L M] : Sentence L →L Prop := Semantics.realize (self := semantics) s

postfix:max " ⊧₁ " => Models

abbrev ModelsTheory (M : Type u) [s : Structure₁ L M] (T : CTheory L) : Prop := Semantics.realizeTheory (s := semantics) s T

infix:55 " ⊧₁* " => ModelsTheory

section
variable {M : Type u} [s : Structure₁ L M]

lemma models_def : M ⊧₁ = SubFormula.Val s Empty.elim := rfl

lemma models_iff {σ : Sentence L} : M ⊧₁ σ ↔ SubFormula.Val s Empty.elim σ := by simp[models_def]

lemma realize_def : Semantics.realize (self := semantics) s = SubFormula.Val s Empty.elim := rfl

lemma modelsₛ_iff {T : CTheory L} : M ⊧₁* T ↔ (∀ ⦃p⦄, p ∈ T → M ⊧₁ p) := of_eq rfl

lemma models_iff_realize {σ : Sentence L} :
    M ⊧₁ σ ↔ Semantics.realize (self := semantics) s σ := of_eq rfl

lemma consequence_iff {T : CTheory L} {σ : Sentence L} :
    T ⊨ σ ↔ (∀ (M : Type u) [Inhabited M] [Structure₁ L M], M ⊧₁* T → M ⊧₁ σ) :=
  of_eq rfl

lemma satisfiableₛ_iff {T : CTheory L} :
    Semantics.Satisfiableₛ T ↔ ∃ (M : Type u) (_ : Inhabited M) (_ : Structure₁ L M), M ⊧₁* T :=
  of_eq rfl

lemma satisfiableₛ_intro {T : CTheory L} (M : Type u) [i : Inhabited M] [s : Structure₁ L M] (h : M ⊧₁* T) : Semantics.Satisfiableₛ T :=
⟨M, i, s, h⟩

lemma validₛ_iff {T : CTheory L} :
    Semantics.Validₛ T ↔ ∀ ⦃M : Type u⦄ [Inhabited M] [Structure₁ L M], M ⊧₁* T :=
  of_eq rfl

end

namespace SubFormula
variable {L₁ L₂ : Language.{u}} {Φ : L₁ →ᵥ L₂} 

section 
variable {M : Type u} {s₂ : Structure₁ L₂ M} {n} {e : Fin n → M} {ε : μ → M}

lemma eval_onSubFormula₁ {p : SubFormula L₁ μ n} :
    Eval s₂ e ε (Φ.onSubFormula₁ p) ↔ Eval (Φ.onStructure₁ s₂) e ε p :=
  by induction p using rec' <;>
    simp[*, SubTerm.val_onSubTerm, Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel,
      eval_rel, eval_nrel]

lemma models_onSubFormula₁ {σ : Sentence L₁} :
    Semantics.realize (self := semantics) s₂ (Φ.onSubFormula₁ σ) ↔ Semantics.realize (self := semantics) (Φ.onStructure₁ s₂) σ :=
  by simp[Semantics.realize, Val, eval_onSubFormula₁]

lemma onSubFormula₁_models_onSubFormula₁ {T : CTheory L₁} {σ : Sentence L₁} (h : T ⊨ σ) :
    Φ.onSubFormula₁ '' T ⊨ Φ.onSubFormula₁ σ := by
  intro M _ s hM
  have : Semantics.realize (self := semantics) (Φ.onStructure₁ s) σ :=
    h M (Φ.onStructure₁ s) (fun q hq => models_onSubFormula₁.mp $ hM (Set.mem_image_of_mem _ hq))
  exact models_onSubFormula₁.mpr this

end

section
variable
  (injf : ∀ k, Function.Injective (Φ.onFunc : L₁.func k → L₂.func k))
  (injr : ∀ k, Function.Injective (Φ.onRel : L₁.rel k → L₂.rel k))
  {M : Type u} [Inhabited M] (s₁ : Structure₁ L₁ M)
  {n} (e : Fin n → M) (ε : μ → M)

lemma eval_extendStructure₁_onSubFormula₁ {p : SubFormula L₁ μ n} :
    Eval (Φ.extendStructure₁ s₁) e ε (Φ.onSubFormula₁ p) ↔ Eval s₁ e ε p := by
  induction p using rec' <;> simp[*, SubTerm.val_extendStructure₁_onSubTerm Φ e ε injf s₁,
    Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel, eval_rel, eval_nrel]
  · case hrel k r v =>
    exact Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))
  · case hnrel k r v =>
    simpa[not_iff_not] using
      Structure₁.extendStructure₁_rel Φ s₁ (injr k) r (fun i => SubTerm.val s₁ e ε (v i))

lemma models_extendStructure₁_onSubFormula₁ (σ : Sentence L₁) :
    Semantics.realize (self := semantics) (Φ.extendStructure₁ s₁) (Φ.onSubFormula₁ σ) ↔ Semantics.realize (self := semantics) s₁ σ := by
  simp[Semantics.realize, Val, eval_extendStructure₁_onSubFormula₁ injf injr]

lemma onSubFormula₁_models_onSubFormula₁_iff {T : CTheory L₁} {σ : Sentence L₁} :
    Φ.onSubFormula₁ '' T ⊨ Φ.onSubFormula₁ σ ↔ T ⊨ σ := by
  constructor
  · simp; intro h M _ s₁ hs₁
    exact (models_extendStructure₁_onSubFormula₁ injf injr s₁ σ).mp $
      h M (Φ.extendStructure₁ s₁)
      (by simp[Semantics.realizeTheory]; intro σ hσ; exact (models_extendStructure₁_onSubFormula₁ injf injr s₁ σ).mpr (hs₁ hσ))
  · exact onSubFormula₁_models_onSubFormula₁

end

end SubFormula

end FirstOrder

namespace Structure₁

class Eq {L : Language.{u}} [L.HasEq] (M : Type w) [s : Structure₁ L M] where
  eq : ∀ a b, s.rel Language.HasEq.eq ![a, b] ↔ a = b

attribute [simp] Eq.eq

end Structure₁

namespace FirstOrder

namespace SubFormula

variable {L : Language.{u}} [L.HasEq] {μ : Type v} (M : Type w) (s : Structure₁ L M) [s.Eq]
  {n} (e : Fin n → M) (ε : μ → M)

@[simp] lemma eval_eq (t u : SubTerm L μ n) :
    Eval s e ε (rel Language.HasEq.eq ![t, u]) ↔ t.val s e ε = u.val s e ε :=
  by simp

end SubFormula

namespace Theory

end Theory

end FirstOrder

