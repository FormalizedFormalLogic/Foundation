import Logic.Predicate.FirstOrder.Basic

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {L₁ : Language.{u}} {L₂ : Language.{u}}

namespace Language

def subLanguage (L : Language) (pfunc : ∀ k, Language.func L k → Prop) (prel : ∀ k, L.rel k → Prop) :
    Language where
  func := fun k => Subtype (pfunc k)
  rel  := fun k => Subtype (prel k)

section subLanguage

variable (L) {pf : ∀ k, Language.func L k → Prop} {pr : ∀ k, L.rel k → Prop}

def ofSubLanguage : subLanguage L pf pr →ᵥ L where
  func := Subtype.val
  rel  := Subtype.val

@[simp] lemma ofSubLanguage_onFunc {k : ℕ} :
    L.ofSubLanguage.func p = p.val := rfl

@[simp] lemma ofSubLanguage_onRel {k : ℕ} :
    L.ofSubLanguage.rel p = p.val := rfl

end subLanguage

end Language

namespace Subterm

open Language
variable [∀ k, DecidableEq (L.func k)]

def lang : Subterm L μ n → Finset (Σ k, L.func k)
  | #_       => ∅
  | &_       => ∅
  | func f v => insert ⟨_, f⟩ $ Finset.biUnion Finset.univ (fun i => lang (v i))

@[simp] lemma lang_func {k} (f : L.func k) (v : Fin k → Subterm L μ n) :
    ⟨k, f⟩ ∈ (func f v).lang := by simp[lang]

lemma lang_func_ss {k} (f : L.func k) (v : Fin k → Subterm L μ n) (i) :
    (v i).lang ⊆ (func f v).lang :=
  by intros x; simp[lang]; intros h; exact Or.inr ⟨i, h⟩

def toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) : ∀ t : Subterm L μ n,
    (∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) → Subterm (subLanguage L pf pr) μ n
  | #x,                    _ => #x
  | &x,                    _ => &x
  | func (arity := k) f v, h => func ⟨f, h k f (by simp)⟩
      (fun i => toSubLanguage' pf pr (v i) (fun k' f' h' => h k' f' (lang_func_ss f v i h')))

@[simp] lemma lMap_toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop)
  (t : Subterm L μ n) (h : ∀ k f, ⟨k, f⟩ ∈ t.lang → pf k f) :
    (t.toSubLanguage' pf pr h).lMap L.ofSubLanguage = t :=
  by induction t <;> simp[*, toSubLanguage', lMap_func]

end Subterm

namespace Subformula

variable [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

noncomputable def langFunc : ∀ {n}, Subformula L μ n → Finset (Σ k, L.func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | _, nrel _ v => Finset.biUnion Finset.univ (fun i => (v i).lang)
  | _, p ⋏ q    => langFunc p ∪ langFunc q
  | _, p ⋎ q    => langFunc p ∪ langFunc q
  | _, ∀' p     => langFunc p
  | _, ∃' p     => langFunc p

noncomputable def langRel : ∀ {n}, Subformula L μ n → Finset (Σ k, L.rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, p ⋏ q    => langRel p ∪ langRel q
  | _, p ⋎ q    => langRel p ∪ langRel q
  | _, ∀' p     => langRel p
  | _, ∃' p     => langRel p

lemma langFunc_rel_ss {k} (r : L.rel k) (v : Fin k → Subterm L μ n) (i) :
    (v i).lang ⊆ (rel r v).langFunc :=
  by intros x; simp[langFunc]; intros h; exact ⟨i, h⟩

def toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) : ∀ {n} (p : Subformula L μ n),
    (∀ k f, ⟨k, f⟩ ∈ p.langFunc → pf k f) →
    (∀ k r, ⟨k, r⟩ ∈ p.langRel → pr k r) →
    Subformula (L.subLanguage pf pr) μ n
  | _, ⊤,        _,  _  => ⊤
  | _, ⊥,        _,  _  => ⊥
  | _, rel r v,  hf, hr =>
      rel ⟨r, hr _ r (by simp[langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | _, nrel r v, hf, hr =>
      nrel ⟨r, hr _ r (by simp[langRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (langFunc_rel_ss r v i h)))
  | _, p ⋏ q,    hf, hr =>
      toSubLanguage' pf pr p (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋏
      toSubLanguage' pf pr q (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, p ⋎ q,    hf, hr =>
      toSubLanguage' pf pr p (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋎
      toSubLanguage' pf pr q (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, ∀' p,     hf, hr => ∀' toSubLanguage' pf pr p hf hr
  | _, ∃' p,     hf, hr => ∃' toSubLanguage' pf pr p hf hr

@[simp] lemma lMap_toSubLanguage'
  (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) {n} (p : Subformula L μ n)
  (hf : ∀ k f, ⟨k, f⟩ ∈ p.langFunc → pf k f) (hr : ∀ k r, ⟨k, r⟩ ∈ p.langRel → pr k r) :
    lMap L.ofSubLanguage (p.toSubLanguage' pf pr hf hr) = p := by
  induction p using rec' <;> simp[*, toSubLanguage', lMap_rel, lMap_nrel]

noncomputable def languageFuncIndexed (p : Subformula L μ n) (k) : Finset (L.func k) :=
  Finset.preimage (langFunc p) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective _)

noncomputable def languageRelIndexed (p : Subformula L μ n) (k) : Finset (L.rel k) :=
  Finset.preimage (langRel p) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective _)

abbrev languageFinset (Γ : Finset (Subformula L μ n)) : Language :=
  Language.subLanguage L (fun k f => ∃ p ∈ Γ, ⟨k, f⟩ ∈ langFunc p) (fun k r => ∃ p ∈ Γ, ⟨k, r⟩ ∈ langRel p)

noncomputable instance (Γ : Finset (Subformula L μ n)) (k) : Fintype ((languageFinset Γ).func k) :=
  Fintype.subtype (Γ.biUnion (languageFuncIndexed · k)) (by simp[languageFuncIndexed])

noncomputable instance (Γ : Finset (Subformula L μ n)) (k) : Fintype ((languageFinset Γ).rel k) :=
  Fintype.subtype (Γ.biUnion (languageRelIndexed · k)) (by simp[languageRelIndexed])

def toSubLanguageFinsetSelf {Γ : Finset (Subformula L μ n)} {p} (h : p ∈ Γ) : Subformula (languageFinset Γ) μ n :=
  p.toSubLanguage' _ _ (fun _ _ hf => ⟨p, h, hf⟩) (fun _ _ hr => ⟨p, h, hr⟩)

@[simp] lemma lMap_toSubLanguageFinsetSelf {Γ : Finset (Subformula L μ n)} {p} (h : p ∈ Γ) :
    lMap L.ofSubLanguage (toSubLanguageFinsetSelf h) = p :=
  lMap_toSubLanguage' _ _ _ _ _

end Subformula

namespace Structure

instance subLanguageStructure {pf : ∀ k, Language.func L k → Prop} {pr : ∀ k, L.rel k → Prop}
  {M : Type w} (s : Structure L M) : Structure (Language.subLanguage L pf pr) M :=
  s.lMap (Language.ofSubLanguage L)

noncomputable def extendStructure (Φ : L₁ →ᵥ L₂) {M : Type w} [Inhabited M] (s : Structure L₁ M) : Structure L₂ M where
  func := fun {k} f₂ v => Classical.epsilon (fun y => ∃ f₁ : L₁.func k, Φ.func f₁ = f₂ ∧ y = s.func f₁ v)
  rel  := fun {k} r₂ v => ∃ r₁ : L₁.rel k, Φ.rel r₁ = r₂ ∧ s.rel r₁ v

namespace extendStructure

variable
  (Φ : L₁ →ᵥ L₂)
  (injf : ∀ k, Function.Injective (Φ.func : L₁.func k → L₂.func k))
  (injr : ∀ k, Function.Injective (Φ.rel : L₁.rel k → L₂.rel k))
  {M : Type u} [Inhabited M] (s₁ : Structure L₁ M)
  {n} (e : Fin n → M) (ε : μ → M)

protected lemma func
  {k} (injf : Function.Injective (Φ.func : L₁.func k → L₂.func k)) (f₁ : L₁.func k) (v : Fin k → M) :
    (s₁.extendStructure Φ).func (Φ.func f₁) v = s₁.func f₁ v := by
  simp[extendStructure]
  have : ∃ y, ∃ f₁' : L₁.func k, Φ.func f₁' = Φ.func f₁ ∧ y = s₁.func f₁' v := ⟨s₁.func f₁ v, f₁, rfl, rfl⟩
  rcases Classical.epsilon_spec this with ⟨f', f'eq, h⟩
  rcases injf f'eq with rfl; exact h

protected lemma rel
  {k} (injr : Function.Injective (Φ.rel : L₁.rel k → L₂.rel k)) (r₁ : L₁.rel k) (v : Fin k → M) :
    (s₁.extendStructure Φ).rel (Φ.rel r₁) v ↔ s₁.rel r₁ v := by
  simp[extendStructure]; refine ⟨by intros h; rcases h with ⟨r₁', e, h⟩; rcases injr e; exact h, by intros h; refine ⟨r₁, rfl, h⟩⟩

lemma val_lMap
    (injf : ∀ k, Function.Injective (Φ.func : L₁.func k → L₂.func k))
    (s₁ : Structure L₁ M) (t : Subterm L₁ μ n) :
    Subterm.val (s₁.extendStructure Φ) e ε (t.lMap Φ) = Subterm.val s₁ e ε t := by
  induction t <;> simp[*, Subterm.lMap_func, Subterm.val_func]
  case func k f v ih =>
    exact extendStructure.func Φ s₁ (injf k) f (fun i => Subterm.val s₁ e ε (v i))

open Subformula

lemma eval_lMap {p : Subformula L₁ μ n} :
    Eval (s₁.extendStructure Φ) e ε (lMap Φ p) ↔ Eval s₁ e ε p := by
  induction p using Subformula.rec' <;> simp[*, val_lMap Φ e ε injf s₁, Subformula.lMap_rel, Subformula.lMap_nrel, eval_rel, eval_nrel]
  · case hrel k r v =>
    exact extendStructure.rel Φ s₁ (injr k) r (fun i => Subterm.val s₁ e ε (v i))
  · case hnrel k r v =>
    simpa[not_iff_not] using
      extendStructure.rel Φ s₁ (injr k) r (fun i => Subterm.val s₁ e ε (v i))

lemma models_lMap (σ : Sentence L₁) :
    Logic.Semantics.models (s₁.extendStructure Φ) (Subformula.lMap Φ σ) ↔ Logic.Semantics.models s₁ σ := by
  simp[Logic.Semantics.models, Val, eval_lMap Φ injf injr]

end extendStructure

end Structure

section lMap

variable
  (Φ : L₁ →ᵥ L₂)
  (injf : ∀ k, Function.Injective (Φ.func : L₁.func k → L₂.func k))
  (injr : ∀ k, Function.Injective (Φ.rel : L₁.rel k → L₂.rel k))

lemma lMap_models_lMap_iff {T : Theory L₁} {σ : Sentence L₁} :
    Theory.lMap Φ T ⊨ Subformula.lMap Φ σ ↔ T ⊨ σ := by
  constructor
  · simp; intro h M _ s₁ hs₁
    exact (Structure.extendStructure.models_lMap Φ injf injr s₁ σ).mp $
      h M (s₁.extendStructure Φ)
      (by simp[Logic.Semantics.modelsTheory, Theory.lMap];
          intro σ hσ; exact (Structure.extendStructure.models_lMap (Φ := Φ) injf injr s₁ σ).mpr (hs₁ hσ))
  · exact lMap_models_lMap

open Logic

lemma satisfiableₛ_lMap {T : Theory L₁} (s : Semantics.Satisfiableₛ T) :
    Semantics.Satisfiableₛ (Subformula.lMap Φ '' T) := by
  rcases s with ⟨M, i, s, hM⟩
  exact ⟨M, i, s.extendStructure Φ, by simp; intro σ hσ; exact (Structure.extendStructure.models_lMap Φ injf injr s σ).mpr (hM hσ)⟩

end lMap

end FirstOrder

end LO
