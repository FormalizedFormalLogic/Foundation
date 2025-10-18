import Foundation.IntFO.Basic.Deduction

namespace LO.FirstOrder

namespace Semiterm

variable {L : Language} [L.Relational]

lemma bvar_or_fvar_of_relational (t : Semiterm L ξ n) : (∃ x, t = #x) ∨ (∃ x, t = &x) :=
  match t with
  |        #x => by simp
  |        &x => by simp
  | .func f _ => Language.Relational.func_empty _ |>.elim' f

lemma fvar_of_relational (t : Term L ξ) : ∃ x, t = &x := by
  rcases bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact finZeroElim (α := fun _ ↦ _) x
  · exact ⟨x, rfl⟩

variable {M : Type*} (bv : Fin n → M) (fv : ξ → M)

def relationalVal : Semiterm L ξ n → M
  |        #x => bv x
  |        &x => fv x
  | .func f _ => Language.Relational.func_empty _ |>.elim' f

variable {bv fv}

@[simp] lemma relationalVal_bvar : (#x : Semiterm L ξ n).relationalVal bv fv = bv x := rfl

@[simp] lemma relationalVal_fvar : (&x : Semiterm L ξ n).relationalVal bv fv = fv x := rfl

lemma relationalVal_rew {bv : Fin n₂ → M} {fv : ξ₂ → M} (ω : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    relationalVal bv fv (ω t) = relationalVal (relationalVal bv fv ∘ ω ∘ bvar) (relationalVal bv fv ∘ ω ∘ fvar) t := by
  rcases bvar_or_fvar_of_relational t with (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp

@[simp] lemma relationalVal_bShift (x : M) (t : Semiterm L ξ n) :
    relationalVal (x :> bv) fv (Rew.bShift t) = relationalVal bv fv t := by
  simp [relationalVal_rew, Function.comp_def]

end Semiterm

open Frame

structure RelationalKripkeModel (L : Language) [L.Relational] where
  World : Type*
  [preorder : Preorder World]
  Carrier : Type*
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Carrier) → Prop
  rel_monotone : w ≥ v → Rel w R t → Rel v R t

instance (L : Language) [L.Relational] : CoeSort (RelationalKripkeModel L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.World⟩

instance {L : Language} [L.Relational] (𝓚 : RelationalKripkeModel L) : CoeSort 𝓚.World (Type _) := ⟨fun w ↦ 𝓚.Domain w⟩

instance {L : Language} [L.Relational] (𝓚 : RelationalKripkeModel L) : Preorder 𝓚.World := 𝓚.preorder

namespace RelationalKripkeModel

variable {L : Language} [L.Relational] {𝓚 : RelationalKripkeModel L}

def Val {n} (w : 𝓚) (bv : Fin n → Carrier 𝓚) (fv : ξ → Carrier 𝓚) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => 𝓚.Rel w R fun i ↦ (t i).relationalVal bv fv
  |        ⊤ => True
  |        ⊥ => False
  |    φ ⋏ ψ => Val w bv fv φ ∧ Val w bv fv ψ
  |    φ ⋎ ψ => Val w bv fv φ ∨ Val w bv fv ψ
  |    φ ➝ ψ => ∀ v ≤ w, Val v bv fv φ → Val v bv fv ψ
  |     ∀' φ => ∀ v ≤ w, ∀ x : v, Val v (x.val :> bv) fv φ
  |     ∃' φ => ∃ x : w, Val w (x.val :> bv) fv φ

local notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Val w bv fv φ

abbrev Valb {n} (w : 𝓚) (bv : Fin n → Carrier 𝓚) : Semisentenceᵢ L n → Prop := 𝓚.Val w bv Empty.elim

scoped notation:45 w " ⊩/" bv φ:46 => Valb w bv φ

variable (w : 𝓚) (bv : Fin n → Carrier 𝓚) (fv : ξ → Carrier 𝓚)

@[simp] lemma val_verum : w ⊩[bv|fv] ⊤ := by trivial

@[simp] lemma val_falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩

variable {w bv fv}

@[simp] lemma val_rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ 𝓚.Rel w R fun i ↦ (t i).relationalVal bv fv := by rfl

@[simp] lemma val_and {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋏ ψ ↔ w ⊩[bv|fv] φ ∧ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma val_or {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋎ ψ ↔ w ⊩[bv|fv] φ ∨ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma val_imply {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ ➝ ψ ↔ ∀ v ≤ w, Val v bv fv φ → Val v bv fv ψ := by rfl

@[simp] lemma val_all {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∀' φ ↔ ∀ v ≤ w, ∀ x : v, Val v (x.val :> bv) fv φ := by rfl

@[simp] lemma val_ex {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∃' φ ↔ ∃ x : w, w ⊩[x :> bv|fv] φ := by rfl

@[simp] lemma val_neg {φ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] ∼φ ↔ ∀ v ≤ w, ¬v ⊩[bv|fv] φ := by rfl

@[simp] lemma val_conj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋀Γ ↔ ∀ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [val_conj (Γ := ψ :: Γ)]

@[simp] lemma val_disj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋁Γ ↔ ∃ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [val_disj (Γ := ψ :: Γ)]

lemma val_rew {bv : Fin n₂ → Carrier 𝓚} {fv : ξ₂ → Carrier 𝓚} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    w ⊩[bv|fv] (ω ▹ φ) ↔
    w ⊩[fun x ↦ (ω #x).relationalVal bv fv|fun x ↦ (ω &x).relationalVal bv fv] φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ w
  case hRel k R t =>
    simp only [Semiformulaᵢ.rew_rel, val_rel]
    apply iff_of_eq; congr; funext x
    simp [Semiterm.relationalVal_rew ω (t x), Function.comp_def]
  case hImp φ ψ ihφ ihψ =>
    simp [*]
  case hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hVerum => simp
  case hFalsum => simp
  case hAll φ ih =>
    have (x : Carrier 𝓚) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]
  case hEx φ ih =>
    have (x : Carrier 𝓚) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]

@[simp] lemma val_free {fv : ℕ → 𝓚.Carrier} {φ : SyntacticSemiformulaᵢ L (n + 1)} :
    v ⊩[bv|↑x :>ₙ fv] Rewriting.free φ ↔ v ⊩[bv <: x|fv] φ := by
  have : (fun i ↦ Semiterm.relationalVal (L := L) bv (x :>ₙ fv) (Rew.free #i)) = (bv <: x) := by
    ext i; cases i using Fin.lastCases <;> simp
  simp [Rewriting.free, val_rew, this]

lemma val_subst (w : Fin k → Semiterm L ξ n) (φ : Semiformulaᵢ L ξ k) :
    v ⊩[bv|fv] (φ ⇜ w) ↔ v ⊩[fun i ↦ (w i).relationalVal bv fv|fv] φ := by
  simp [Rewriting.subst, val_rew]

@[simp] lemma val_subst₀ (φ : Formulaᵢ L ξ) :
    v ⊩[bv|fv] φ/[] ↔ v ⊩[![]|fv] φ := by
  simp [val_subst, Matrix.empty_eq]

@[simp] lemma val_subst₁ (t : Semiterm L ξ n) (φ : Semiformulaᵢ L ξ 1) :
    v ⊩[bv|fv] φ/[t] ↔ v ⊩[![t.relationalVal bv fv]|fv] φ := by
  simp [val_subst, Matrix.constant_eq_singleton]

@[simp] lemma val_emb {φ : Semisentenceᵢ L n} :
    v ⊩[bv|fv] (Rewriting.emb φ) ↔ v ⊩[bv|Empty.elim] φ := by
  simp [Rewriting.emb, val_rew, Empty.eq_elim]

lemma Val.monotone
    {n} {bv : Fin n → Carrier 𝓚} {fv : ξ → Carrier 𝓚}
    (h : v ≤ w) {φ} : w ⊩[bv|fv] φ → v ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => 𝓚.rel_monotone h
  |        ⊤ => id
  |        ⊥ => id
  |    φ ⋏ ψ => by
    rintro ⟨hl, hr⟩
    exact ⟨hl.monotone h, hr.monotone h⟩
  |    φ ⋎ ψ => by
    rintro (hl | hr)
    · left; exact hl.monotone h
    · right; exact hr.monotone h
  |    φ ➝ ψ => fun Hw v' hvv' Hv' ↦
    Hw v' (le_trans hvv' h) Hv'
  |    ∀' φ => fun Hw v' hvv' x ↦ Hw v' (le_trans hvv' h) x
  |    ∃' φ => by
    rintro ⟨x, Hw⟩
    exact ⟨⟨x, 𝓚.domain_antimonotone h x.prop⟩, Hw.monotone h⟩

variable (𝓚)

def Force (φ : Sentenceᵢ L) : Prop := ∀ w : 𝓚, w ⊩[![]|Empty.elim] φ

instance : Semantics (Sentenceᵢ L) (RelationalKripkeModel L) := ⟨fun 𝓚 φ ↦ 𝓚.Force φ⟩

variable {𝓚}

variable {Λ : Hilbertᵢ L}

open HilbertProofᵢ Semantics

lemma sound!_forces (w : 𝓚) (fv : ℕ → 𝓚.Carrier) (hfv : ∀ i, fv i ∈ 𝓚.Domain w) {φ} : 𝗜𝗻𝘁¹ ⊢! φ → w ⊩[![]|fv] φ
  |     eaxm h => by
    have : ∃ ψ, Axioms.EFQ ψ = φ := by simpa [Hilbertᵢ.Intuitionistic] using h
    rcases this with ⟨ψ, rfl⟩
    rintro v hvw ⟨⟩
  | mdp bφψ bφ => by simpa using sound!_forces w fv hfv bφψ w (by simp) (sound!_forces w fv hfv bφ)
  |      gen b => fun v hwv x ↦ by
    simpa using sound!_forces v (x :>ₙ fv) (by rintro (i | i) <;> simp [fun i ↦ 𝓚.domain_antimonotone hwv (hfv i)]) b
  | verum => by simp
  | imply₁ φ ψ => by
    intro w₁ hw₁w₀ hw₁φ w₂ hw₁w₂ hw₂φ
    exact hw₁φ.monotone hw₁w₂
  | imply₂ φ ψ χ => by
    intro w₁ hw₁w₀ hw₁ w₂ hw₂w₁ hw₂ w₃ hw₃w₂ hw₃
    have : w₃ ⊩[![]|fv] ψ := hw₂ w₃ hw₃w₂ hw₃
    exact hw₁ w₃ (le_trans hw₃w₂ hw₂w₁) hw₃ w₃ (by rfl) this
  | and₁ φ ψ => by
    rintro v hvw ⟨hφ, hψ⟩
    exact hφ
  | and₂ φ ψ => by
    rintro v hvw ⟨hφ, hψ⟩
    exact hψ
  | and₃ φ ψ => by
    intro v₁ hv₁w hφ v₂ hv₂v₁ hψ
    exact ⟨hφ.monotone hv₂v₁, hψ⟩
  | or₁ φ ψ => by
    intro v hvw hφ
    left; exact hφ
  | or₂ φ ψ => by
    intro v hvw hψ
    right; exact hψ
  | or₃ φ ψ χ => by
    rintro w₁ hw₁w hφχ w₂ hw₂w₁ hψχ w₃ hw₃w₂ (hφ | hψ)
    · exact hφχ w₃ (le_trans hw₃w₂ hw₂w₁) hφ
    · exact hψχ w₃ hw₃w₂ hψ
  | all₁ φ t => by
    rcases t.fvar_of_relational with ⟨x, rfl⟩
    intro v hvw hφ
    suffices v ⊩[![fv x]|fv] φ by simpa [val_subst, Matrix.constant_eq_singleton]
    simpa using hφ v (by rfl) ⟨fv x, 𝓚.domain_antimonotone hvw (hfv x)⟩
  | all₂ φ ψ => by
    intro w₁ hw₁ H w₂ hw₂₁ hφ w₃ hw₃₂ x
    exact H w₃ (le_trans hw₃₂ hw₂₁) x w₃ (by rfl) (by simpa using hφ.monotone hw₃₂)
  | ex₁ t φ => by
    rcases t.fvar_of_relational with ⟨x, rfl⟩
    intro v hvw hφ
    have : v ⊩[![fv x]|fv] φ := by simpa using hφ
    exact ⟨⟨fv x, 𝓚.domain_antimonotone hvw (hfv x)⟩, by simpa using this⟩
  | ex₂ φ ψ => by
    rintro w₁ hw₁ H w₂ hw₂₁ ⟨x, hφ⟩
    simpa using H w₂ hw₂₁ x w₂ (by rfl) hφ

lemma sound {T : Theoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L)} (b : T ⊢ φ) : 𝓚 ⊧* T → 𝓚 ⊧ φ := fun H w ↦ by
  rcases 𝓚.domain_nonempty w with ⟨x, hx⟩
  have : (Rewriting.emb '' T.theory) *⊢[𝗜𝗻𝘁¹] ↑φ := b
  rcases Entailment.Context.provable_iff.mp this with ⟨Γ, HΓ, b⟩
  have : w ⊩[![]|fun _ ↦ x] ⋀Γ ➝ ↑φ := sound!_forces (L := L) w (fun _ ↦ x) (by simp [hx]) b.get
  have : w ⊩[![]|fun _ : ℕ ↦ x] ↑φ := by
    apply this w (by rfl)
    suffices ∀ φ ∈ Γ, w ⊩[![]|fun _ ↦ x] φ by simpa
    intro φ hφ
    rcases show ∃ x ∈ T.theory, ↑x = φ by simpa using HΓ φ hφ with ⟨φ, hφ', rfl⟩
    simpa using H.RealizeSet hφ' w
  simpa using this

instance (T : Theoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L)) : Sound T (Semantics.models (RelationalKripkeModel L) T) := ⟨fun b _ H ↦ sound b H⟩

end RelationalKripkeModel

end LO.FirstOrder
