import Logic.Predicate.FirstOrder.Formula

variable {L L₁ L₂ L₃ : Language} {μ : Type _}

namespace Language

namespace Hom
variable (Φ : Hom L₁ L₂) {n : ℕ}

open FirstOrder

def onSubFormula₁' (Φ : Hom L₁ L₂) : ∀ {n}, SubFormula L₁ μ n → SubFormula L₂ μ n
  | _, ⊤                   => ⊤ 
  | _, ⊥                   => ⊥ 
  | _, SubFormula.rel r v  => SubFormula.rel (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
  | _, SubFormula.nrel r v => SubFormula.nrel (Φ.onRel r) (fun i => Φ.onSubTerm (v i))
  | _, p ⋏ q               => Φ.onSubFormula₁' p ⋏ Φ.onSubFormula₁' q
  | _, p ⋎ q               => Φ.onSubFormula₁' p ⋎ Φ.onSubFormula₁' q
  | _, ∀' p                => ∀' Φ.onSubFormula₁' p
  | _, ∃' p                => ∃' Φ.onSubFormula₁' p

lemma onSubFormula₁'_neg {n} (p : SubFormula L₁ μ n) :
    Φ.onSubFormula₁' (~p) = ~Φ.onSubFormula₁' p :=
  by induction p using SubFormula.rec' <;> simp[*, onSubFormula₁', ←SubFormula.neg_eq]

def onSubFormula₁ (Φ : Hom L₁ L₂) {n} : SubFormula L₁ μ n →L SubFormula L₂ μ n where
  toFun := Φ.onSubFormula₁'
  map_top' := by simp[onSubFormula₁']
  map_bot' := by simp[onSubFormula₁']
  map_and' := by simp[onSubFormula₁']
  map_or'  := by simp[onSubFormula₁']
  map_neg' := by simp[onSubFormula₁'_neg]
  map_imp' := by simp[SubFormula.imp_eq, onSubFormula₁'_neg, ←SubFormula.neg_eq, onSubFormula₁']

lemma onSubFormula₁_rel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onSubFormula₁ (SubFormula.rel r v) = SubFormula.rel (Φ.onRel r) (fun i => Φ.onSubTerm (v i)) := rfl

lemma onSubFormula₁_nrel {k} (r : L₁.rel k) (v : Fin k → SubTerm L₁ μ n) :
    Φ.onSubFormula₁ (SubFormula.nrel r v) = SubFormula.nrel (Φ.onRel r) (fun i => Φ.onSubTerm (v i)) := rfl

@[simp] lemma onSubFormula₁_all (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (∀' p) = ∀' Φ.onSubFormula₁ p := rfl

@[simp] lemma onSubFormula₁_ex (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (∃' p) = ∃' Φ.onSubFormula₁ p := rfl

end Hom

end Language

namespace FirstOrder

namespace SubFormula
variable {L₁ L₂ : Language} (Φ : L₁ →ᵥ L₂) {μ₁ μ₂ : Type _} {n₁ n₂ : ℕ}

lemma onSubFormula₁_bind (bound : Fin n₁ → SubTerm L₁ μ₂ n₂) (free : μ₁ → SubTerm L₁ μ₂ n₂) (p) :
    Φ.onSubFormula₁ (bind bound free p) =
    bind (fun x => Φ.onSubTerm (bound x)) (fun x => Φ.onSubTerm (free x)) (Φ.onSubFormula₁ p) := by
  induction p using rec' generalizing μ₂ n₂ <;>
  simp[*, SubTerm.onSubTerm_bind, Matrix.comp_vecCons, Function.comp, SubTerm.onSubTerm_bShift,
    Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel, bind_rel, bind_nrel]

lemma onSubFormula₁_map (bound : Fin n₁ → Fin n₂) (free : μ₁ → μ₂) (p) :
    Φ.onSubFormula₁ (map bound free p) = map bound free (Φ.onSubFormula₁ p) :=
  by simp[map, onSubFormula₁_bind]

lemma onSubFormula₁_subst (u) (p : SubFormula L₁ μ (n + 1)) :
    Φ.onSubFormula₁ (subst u p) = subst (Φ.onSubTerm u) (Φ.onSubFormula₁ p) :=
  by simp[subst, onSubFormula₁_bind, Matrix.comp_vecConsLast, Function.comp]

lemma onSubFormula₁_shift (p : SyntacticSubFormula L₁ n) : Φ.onSubFormula₁ (shift p) = shift (Φ.onSubFormula₁ p) :=
  by simp[shift, onSubFormula₁_map]

lemma onSubFormula₁_free (p : SyntacticSubFormula L₁ (n + 1)) : Φ.onSubFormula₁ (free p) = free (Φ.onSubFormula₁ p) :=
  by simp[free, onSubFormula₁_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma onSubFormula₁_fix (p : SyntacticSubFormula L₁ n) : Φ.onSubFormula₁ (fix p) = fix (Φ.onSubFormula₁ p) :=
  by simp[fix, onSubFormula₁_bind]; congr; funext x; cases x <;> simp

lemma onSubFormula₁_emb (p : SubFormula L₁ Empty n) :
    (Φ.onSubFormula₁ (emb p) : SubFormula L₂ μ n) = emb (Φ.onSubFormula₁ p) :=
  by simp[emb, onSubFormula₁_map]

end SubFormula

variable {L : Language} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace SubFormula

noncomputable def languageFunc : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.func k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.languageFunc (v i))
  | _, nrel _ v => Finset.bunionᵢ Finset.univ (fun i => SubTerm.languageFunc (v i))
  | _, p ⋏ q    => languageFunc p ∪ languageFunc q 
  | _, p ⋎ q    => languageFunc p ∪ languageFunc q 
  | _, ∀' p     => languageFunc p 
  | _, ∃' p     => languageFunc p 

noncomputable def languageRel : ∀ {n}, SubFormula L μ n → Finset (Σ k, L.rel k)
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, rel  r _ => {⟨_, r⟩}
  | _, nrel r _ => {⟨_, r⟩}
  | _, p ⋏ q    => languageRel p ∪ languageRel q 
  | _, p ⋎ q    => languageRel p ∪ languageRel q 
  | _, ∀' p     => languageRel p 
  | _, ∃' p     => languageRel p

lemma languageFunc_rel_ss {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) (i) :
    (v i).languageFunc ⊆ (rel r v).languageFunc :=
  by intros x; simp[languageFunc]; intros h; exact ⟨i, h⟩

def toSubLanguage' (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) : ∀ {n} (p : SubFormula L μ n),
    (∀ k f, ⟨k, f⟩ ∈ p.languageFunc → pf k f) →
    (∀ k r, ⟨k, r⟩ ∈ p.languageRel → pr k r) →
    SubFormula (L.subLanguage pf pr) μ n
  | _, ⊤,        _,  _  => ⊤
  | _, ⊥,        _,  _  => ⊥
  | _, rel r v,  hf, hr =>
      rel ⟨r, hr _ r (by simp[languageRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (languageFunc_rel_ss r v i h)))
  | _, nrel r v, hf, hr =>
      nrel ⟨r, hr _ r (by simp[languageRel])⟩
        (fun i => (v i).toSubLanguage' pf pr (fun k f h => hf k f (languageFunc_rel_ss r v i h)))
  | _, p ⋏ q,    hf, hr =>
      toSubLanguage' pf pr p (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋏ 
      toSubLanguage' pf pr q (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, p ⋎ q,    hf, hr =>
      toSubLanguage' pf pr p (fun k f h => hf k f (Finset.mem_union_left _ h)) (fun k r h => hr k r (Finset.mem_union_left _ h)) ⋎
      toSubLanguage' pf pr q (fun k f h => hf k f (Finset.mem_union_right _ h)) (fun k r h => hr k r (Finset.mem_union_right _ h))
  | _, ∀' p,     hf, hr => ∀' toSubLanguage' pf pr p (fun k f h => hf k f h) (fun k r h => hr k r h)
  | _, ∃' p,     hf, hr => ∃' toSubLanguage' pf pr p (fun k f h => hf k f h) (fun k r h => hr k r h)

lemma ofSubFormula_toSubLanguage'
  (pf : ∀ k, L.func k → Prop) (pr : ∀ k, L.rel k → Prop) {n} (p : SubFormula L μ n)
  (hf : ∀ k f, ⟨k, f⟩ ∈ p.languageFunc → pf k f) (hr : ∀ k r, ⟨k, r⟩ ∈ p.languageRel → pr k r) :
    L.ofSubLanguage.onSubFormula₁ (p.toSubLanguage' pf pr hf hr) = p := by
  induction p using rec' <;>
  simp[*, toSubLanguage', Language.Hom.onSubFormula₁_rel, Language.Hom.onSubFormula₁_nrel]

noncomputable def languageFuncIndexed (p : SubFormula L μ n) (k) : Finset (L.func k) :=
  Finset.preimage (languageFunc p) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective _)

noncomputable def languageRelIndexed (p : SubFormula L μ n) (k) : Finset (L.rel k) :=
  Finset.preimage (languageRel p) (Sigma.mk k) (Set.injOn_of_injective sigma_mk_injective _)

abbrev language (p : SubFormula L μ n) : Language :=
  Language.subLanguage L (fun k f => ⟨k, f⟩ ∈ languageFunc p) (fun k r => ⟨k, r⟩ ∈ languageRel p) 

-- delete
noncomputable instance (p : SubFormula L μ n) (k) : Fintype (p.language.func k) :=
  Fintype.subtype (languageFuncIndexed p k) (by simp[languageFuncIndexed])

-- delete
noncomputable instance (p : SubFormula L μ n) (k) : Fintype (p.language.rel k) :=
  Fintype.subtype (languageRelIndexed p k) (by simp[languageRelIndexed])

def toSubLanguageSelf (p : SubFormula L μ n) : SubFormula p.language μ n :=
  p.toSubLanguage' (fun k f => ⟨k, f⟩ ∈ languageFunc p) (fun k r => ⟨k, r⟩ ∈ languageRel p)
    (by simp) (by simp)

lemma ofSubFormula_toSubLanguageSelf (p : SubFormula L μ n) :
    L.ofSubLanguage.onSubFormula₁ p.toSubLanguageSelf = p :=
  ofSubFormula_toSubLanguage' _ _ _ _ _

abbrev languageFinset (Γ : Finset (SubFormula L μ n)) : Language :=
  Language.subLanguage L (fun k f => ∃ p ∈ Γ, ⟨k, f⟩ ∈ languageFunc p) (fun k r => ∃ p ∈ Γ, ⟨k, r⟩ ∈ languageRel p) 

noncomputable instance (Γ : Finset (SubFormula L μ n)) (k) : Fintype ((languageFinset Γ).func k) :=
  Fintype.subtype (Γ.bunionᵢ (languageFuncIndexed · k)) (by simp[languageFuncIndexed])

noncomputable instance (Γ : Finset (SubFormula L μ n)) (k) : Fintype ((languageFinset Γ).rel k) :=
  Fintype.subtype (Γ.bunionᵢ (languageRelIndexed · k)) (by simp[languageRelIndexed])

def toSubLanguageFinsetSelf {Γ : Finset (SubFormula L μ n)} {p} (h : p ∈ Γ) : SubFormula (languageFinset Γ) μ n :=
  p.toSubLanguage' _ _ (fun _ _ hf => ⟨p, h, hf⟩) (fun _ _ hr => ⟨p, h, hr⟩)

@[simp] lemma ofSubFormula_toSubLanguageFinsetSelf {Γ : Finset (SubFormula L μ n)} {p} (h : p ∈ Γ) :
    L.ofSubLanguage.onSubFormula₁ (toSubLanguageFinsetSelf h) = p :=
  ofSubFormula_toSubLanguage' _ _ _ _ _

end SubFormula
