module

public import Foundation.FirstOrder.Intuitionistic.LJ
public import Foundation.FirstOrder.Kripke.Basic

@[expose] public section
/-! # Kripke semantics for intuitionistic first-order logic -/

namespace LO.FirstOrder

variable {L : Language} [L.Relational]

namespace KripkeModel

variable {W : Type*} [Preorder W] {C : Type*} [KripkeModel L W C]

def Forces {n} (w : W) (bv : Fin n → C) (fv : ξ → C) : Semiformulaᵢ L ξ n → Prop
  | .rel R t => Rel w R fun i ↦ (t i).relationalVal bv fv
  |        ⊥ => False
  |    φ ⋏ ψ => Forces w bv fv φ ∧ Forces w bv fv ψ
  |    φ ⋎ ψ => Forces w bv fv φ ∨ Forces w bv fv ψ
  |    φ 🡒 ψ => ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ
  |     ∀¹ φ => ∀ v ≤ w, ∀ x : v, Forces v (x.val :> bv) fv φ
  |     ∃¹ φ => ∃ x : w, Forces w (x.val :> bv) fv φ

scoped notation:45 w " ⊩[" bv "|" fv "] " φ:46 => Forces w bv fv φ

abbrev Forcesb {n} (w : W) (bv : Fin n → C) : Semisentenceᵢ L n → Prop := Forces w bv Empty.elim

scoped notation:45 w " ⊩/" bv φ:46 => Forcesb w bv φ

namespace Forces

variable (w v : W) (bv : Fin n → C) (fv : ξ → C)

@[simp] lemma verum : w ⊩[bv|fv] ⊤ := fun v _ ↦ by rintro ⟨⟩

@[simp] lemma falsum : ¬w ⊩[bv|fv] ⊥ := by rintro ⟨⟩

variable {w v bv fv}

@[simp] lemma rel {k} {R : L.Rel k} {t} :
    w ⊩[bv|fv] .rel R t ↔ Rel w R fun i ↦ (t i).relationalVal bv fv := by rfl

@[simp] lemma and {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋏ ψ ↔ w ⊩[bv|fv] φ ∧ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma or {φ ψ : Semiformulaᵢ L ξ n} : w ⊩[bv|fv] φ ⋎ ψ ↔ w ⊩[bv|fv] φ ∨ w ⊩[bv|fv] ψ := by rfl

@[simp] lemma imply {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ 🡒 ψ ↔ ∀ v ≤ w, Forces v bv fv φ → Forces v bv fv ψ := by rfl

@[simp] lemma not {φ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] ∼φ ↔ ∀ v ≤ w, ¬Forces v bv fv φ := by rfl

@[simp] lemma iff {φ ψ : Semiformulaᵢ L ξ n} :
    w ⊩[bv|fv] φ 🡘 ψ ↔ ∀ v ≤ w, Forces v bv fv φ ↔ Forces v bv fv ψ := by
  simp [LogicalConnective.iff]; grind

@[simp] lemma all {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∀¹ φ ↔ ∀ v ≤ w, ∀ x : v, Forces v (x.val :> bv) fv φ := by rfl

@[simp] lemma ex {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∃¹ φ ↔ ∃ x : w, w ⊩[↑x :> bv|fv] φ := by rfl

@[simp] lemma conj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋀Γ ↔ ∀ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [conj (Γ := ψ :: Γ)]

@[simp] lemma disj {Γ : List (Semiformulaᵢ L ξ n)} :
    w ⊩[bv|fv] ⋁Γ ↔ ∃ φ ∈ Γ, w ⊩[bv|fv] φ :=
  match Γ with
  |          [] => by simp
  |         [φ] => by simp
  | φ :: ψ :: Γ => by simp [disj (Γ := ψ :: Γ)]

lemma rew {bv : Fin n₂ → C} {fv : ξ₂ → C} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformulaᵢ L ξ₁ n₁} :
    w ⊩[bv|fv] (ω ▹ φ) ↔
    w ⊩[fun x ↦ (ω #x).relationalVal bv fv|fun x ↦ (ω &x).relationalVal bv fv] φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n₂ w
  case hRel k R t =>
    simp only [Semiformulaᵢ.rew_rel, rel]
    apply iff_of_eq; congr; funext x
    simp [Semiterm.relationalVal_rew ω (t x), Function.comp_def]
  case hImp φ ψ ihφ ihψ =>
    simp [*]
  case hAnd φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp [ihφ, ihψ]
  case hFalsum => simp
  case hAll φ ih =>
    have (x : C) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]
  case hExs φ ih =>
    have (x : C) : (fun i ↦ (ω.q #i).relationalVal (x :> bv) fv) = (x :> fun i ↦ (ω #i).relationalVal bv fv) := by
      funext i; cases i using Fin.cases <;> simp
    simp [ih, this]

@[simp] lemma free {v : W} {fv : ℕ → C} {φ : Semipropositionᵢ L (n + 1)} :
    v ⊩[bv|↑x :>ₙ fv] Rewriting.free φ ↔ v ⊩[bv <: x|fv] φ := by
  have : (fun i ↦ Semiterm.relationalVal (L := L) bv (x :>ₙ fv) (Rew.free #i)) = (bv <: x) := by
    ext i; cases i using Fin.lastCases <;> simp
  simp [Rewriting.free, Forces.rew, this]

lemma subst {v : W} (w : Fin k → Semiterm L ξ n) (φ : Semiformulaᵢ L ξ k) :
    v ⊩[bv|fv] (φ ⇜ w) ↔ v ⊩[fun i ↦ (w i).relationalVal bv fv|fv] φ := by
  simp [Rewriting.subst, Forces.rew]

@[simp] lemma subst₀ (φ : Formulaᵢ L ξ) :
    v ⊩[bv|fv] φ/[] ↔ v ⊩[![]|fv] φ := by
  simp [Forces.subst, Matrix.empty_eq]

@[simp] lemma forces_subst₁ (t : Semiterm L ξ n) (φ : Semiformulaᵢ L ξ 1) :
    v ⊩[bv|fv] φ/[t] ↔ v ⊩[![t.relationalVal bv fv]|fv] φ := by
  simp [Forces.subst, Matrix.constant_eq_singleton]

@[simp] lemma forces_emb {φ : Semisentenceᵢ L n} :
    v ⊩[bv|fv] (Rewriting.emb φ) ↔ v ⊩[bv|Empty.elim] φ := by
  simp [Rewriting.emb, Forces.rew, Empty.eq_elim]

lemma monotone
    {n} {bv : Fin n → C} {fv : ξ → C} {φ} : w ⊩[bv|fv] φ → ∀ v ≤ w, v ⊩[bv|fv] φ :=
  match φ with
  | .rel R v => rel_monotone
  |        ⊥ => by rintro ⟨⟩
  |    φ ⋏ ψ => by
    rintro ⟨hl, hr⟩ v h
    exact ⟨hl.monotone _ h, hr.monotone _ h⟩
  |    φ ⋎ ψ => by
    rintro (hl | hr) v h
    · left; exact hl.monotone _ h
    · right; exact hr.monotone _ h
  |    φ 🡒 ψ => fun Hw v' h v hvv' Hv ↦
    Hw v (le_trans hvv' h) Hv
  |     ∀¹ φ => fun Hw w h v' hvv' x ↦ Hw v' (le_trans hvv' h) x
  |     ∃¹ φ => by
    rintro ⟨x, Hw⟩ v h
    exact ⟨⟨x, domain_antimonotone h x.prop⟩, Hw.monotone _ h⟩

@[simp] lemma triple_negation_elim {φ : Semiformulaᵢ L ξ n} :
    (∀ v ≤ w, ∃ x ≤ v, ∀ y ≤ x, ¬y ⊩[bv|fv] φ) ↔ (∀ v ≤ w, ¬v ⊩[bv|fv] φ) := by
  constructor
  · intro h v hvw Hv
    rcases h v hvw with ⟨x, hxv, Hx⟩
    exact Hx x (by rfl) (Hv.monotone x hxv)
  · intro h v hvw
    refine ⟨v, by rfl, fun x hxv ↦ h x (le_trans hxv hvw)⟩

@[simp] lemma all_of_constantDomain [ConstantDomain W] {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∀¹ φ ↔ ∀ x : C, w ⊩[x :> bv|fv] φ := by
  constructor
  · intro h x
    exact all.mp h w (by rfl) ⟨x, by simp⟩
  · rintro h v hvw ⟨x, _⟩
    simpa using monotone (h x) v hvw

@[simp] lemma ex_of_constantDomain [ConstantDomain W] {φ : Semiformulaᵢ L ξ (n + 1)} :
    w ⊩[bv|fv] ∃¹ φ ↔ ∃ x : C, w ⊩[x :> bv|fv] φ := by simp

def ForcesHead (w : W) (fv : ℕ → C) : LJ.Head L → Prop
  | none   => False
  | some φ => w ⊩[![]|fv] φ

@[simp] lemma forcesHead_none (w : W) (fv : ℕ → C) : ForcesHead w fv none = False := rfl

@[simp] lemma forcesHead_some (w : W) (fv : ℕ → C) (φ : Propositionᵢ L) :
    ForcesHead w fv (some φ) = (w ⊩[![]|fv] φ) := rfl

/-- Soundness of LJ with respect to intuitionistic Kripke forcing.
- [Min00, Chapter 2]
-/
theorem sound {Γ : LJ.Sequent L} {Ξ : LJ.Head L} :
    (d : Γ ⊢ᴸᴶ¹ Ξ) → (w : W) → (fv : ℕ → C) → (∀ i, w ⊩↓ fv i) →
      (∀ φ ∈ Γ, w ⊩[![]|fv] φ) → ForcesHead w fv Ξ
  | .identity R v, w, fv, _, hΓ => hΓ _ (by simp)
  | .cut (φ := φ) dφ d, w, fv, hfv, hΓ =>
      sound d w fv hfv (fun ψ hψ ↦ by
        rcases Multiset.mem_add.mp hψ with hψ | hψ
        · exact hΓ ψ (Multiset.mem_add.mpr <| Or.inr hψ)
        · have : ψ = φ := by simpa using hψ
          subst ψ
          exact sound dφ w fv hfv fun θ hθ ↦
            hΓ θ (Multiset.mem_add.mpr <| Or.inl hθ))
  | .contraction (Ξ := Ξ) d hΔ hΞ, w, fv, hfv, hΓ => by
      have hd := sound d w fv hfv fun φ hφ ↦ hΓ φ (hΔ hφ)
      cases Ξ <;> cases hΞ <;> simp_all [ForcesHead]
  | .verum, _, _, _, _ => by simp [ForcesHead]
  | .falsum, _, _, _, hΓ => hΓ (⊥ : Propositionᵢ L) (by simp)
  | .positiveImply (φ := φ) d, w, fv, hfv, hΓ => by
      intro v hvw hφ
      exact sound d v fv (fun i ↦ domain_monotone (hfv i) v hvw) fun θ hθ ↦ by
        rcases Multiset.mem_add.mp hθ with hθ | hθ
        · exact (hΓ θ hθ).monotone v hvw
        · have : θ = φ := by simpa using hθ
          simpa [this] using hφ
  | .negativeImply (φ := φ) (ψ := ψ) dφ dψ, w, fv, hfv, hΓ => by
      have hφ : w ⊩[![]|fv] φ := sound dφ w fv hfv fun θ hθ ↦
        hΓ θ (Multiset.mem_add.mpr <| Or.inl <| Multiset.mem_add.mpr <| Or.inl hθ)
      have hi : w ⊩[![]|fv] φ 🡒 ψ := hΓ _ (by simp)
      have hψ := hi w (by rfl) hφ
      exact sound dψ w fv hfv fun θ hθ ↦ by
        rcases Multiset.mem_add.mp hθ with hθ | hθ
        · exact hΓ θ (Multiset.mem_add.mpr <| Or.inl <| Multiset.mem_add.mpr <| Or.inr hθ)
        · have : θ = ψ := by simpa using hθ
          simpa [this] using hψ
  | .positiveAnd dφ dψ, w, fv, hfv, hΓ =>
      ⟨sound dφ w fv hfv hΓ, sound dψ w fv hfv hΓ⟩
  | .negativeAnd (φ := φ) (ψ := ψ) d, w, fv, hfv, hΓ => by
      have h : w ⊩[![]|fv] φ ⋏ ψ := hΓ _ (by simp)
      rcases h with ⟨hφ, hψ⟩
      exact sound d w fv hfv fun θ hθ ↦ by
        rcases Multiset.mem_add.mp hθ with hθ | hθ
        · exact hΓ θ (Multiset.mem_add.mpr <| Or.inl hθ)
        · simp only [Multiset.mem_add, Multiset.mem_atom_iff] at hθ
          rcases hθ with hθ | hθ
          · simpa [hθ] using hφ
          · simpa [hθ] using hψ
  | .positiveOrLeft d, w, fv, hfv, hΓ => Or.inl <| sound d w fv hfv hΓ
  | .positiveOrRight d, w, fv, hfv, hΓ => Or.inr <| sound d w fv hfv hΓ
  | .negativeOr (φ := φ) (ψ := ψ) dφ dψ, w, fv, hfv, hΓ => by
      have h : w ⊩[![]|fv] φ ⋎ ψ := hΓ _ (by simp)
      rcases h with hφ | hψ
      · exact sound dφ w fv hfv fun θ hθ ↦ by
          rcases Multiset.mem_add.mp hθ with hθ | hθ
          · exact hΓ θ (Multiset.mem_add.mpr <| Or.inl hθ)
          · have : θ = φ := by simpa using hθ
            simpa [this] using hφ
      · exact sound dψ w fv hfv fun θ hθ ↦ by
          rcases Multiset.mem_add.mp hθ with hθ | hθ
          · exact hΓ θ (Multiset.mem_add.mpr <| Or.inl hθ)
          · have : θ = ψ := by simpa using hθ
            simpa [this] using hψ
  | .positiveForall d, w, fv, hfv, hΓ => by
      intro v hvw x
      simpa [ForcesHead] using sound d v (x.val :>ₙ fv)
        (by rintro (i | i) <;> simp [fun i ↦ domain_monotone (hfv i) v hvw])
        (fun θ hθ ↦ by
          rcases Multiset.mem_map.mp hθ with ⟨ψ, hψ, rfl⟩
          simpa [Rewriting.shift, Forces.rew] using (hΓ ψ hψ).monotone v hvw)
  | .negativeForall (φ := φ) (t := t) d, w, fv, hfv, hΓ => by
      obtain ⟨x, ht⟩ := t.fvar_of_relational
      have hAll : w ⊩[![]|fv] ∀¹ φ := hΓ _ (by simp)
      have hφ := hAll w (by rfl) ⟨fv x, hfv x⟩
      exact sound d w fv hfv fun θ hθ ↦ by
        rcases Multiset.mem_add.mp hθ with hθ | hθ
        · exact hΓ θ (Multiset.mem_add.mpr <| Or.inl hθ)
        · have : θ = φ/[t] := by simpa using hθ
          simpa [this, ht] using hφ
  | .positiveExists (t := t) d, w, fv, hfv, hΓ => by
      obtain ⟨x, ht⟩ := t.fvar_of_relational
      exact ⟨⟨fv x, hfv x⟩, by simpa [ht] using sound d w fv hfv hΓ⟩
  | .negativeExists (φ := φ) (Ξ := Ξ) d, w, fv, hfv, hΓ => by
      have hEx : w ⊩[![]|fv] ∃¹ φ := hΓ _ (by simp)
      rcases hEx with ⟨x, hx⟩
      have hd := sound d w (x.val :>ₙ fv) (by rintro (i | i) <;> simp [hfv]) (fun θ hθ ↦ by
        rcases Multiset.mem_add.mp hθ with hθ | hθ
        · rcases Multiset.mem_map.mp hθ with ⟨ψ, hψ, rfl⟩
          simpa [Rewriting.shift, Forces.rew] using hΓ ψ (by simp [hψ])
        · have : θ = Rewriting.free φ := by simpa using hθ
          simpa [this] using hx)
      cases Ξ with
      | none => exact hd
      | some ψ =>
          simpa [ForcesHead, LJ.Head.shift, Rewriting.shift, Forces.rew] using hd

end Forces

abbrev Forces₀ (w : W) (φ : Sentenceᵢ L) : Prop := w ⊩[![]|Empty.elim] φ

instance : ForcingRelation W (Sentenceᵢ L) := ⟨Forces₀⟩

lemma forces₀_def {w : W} {φ : Sentenceᵢ L} : w ⊩ φ ↔ w ⊩[![]|Empty.elim] φ := by rfl

namespace Forces₀

lemma monotone {w : W} {φ} : w ⊩ φ → ∀ v ≤ w, v ⊩ φ :=
  fun h hw ↦ Forces.monotone h hw

instance : ForcingRelation.IntKripke W (· ≥ ·) where
  verum w := by rintro _ _ ⟨⟩
  falsum w := by rintro ⟨⟩
  and w := by simp [forces₀_def]
  or w := by simp [forces₀_def]
  imply w := by simp [forces₀_def, Forces.imply]
  not w := by simp [forces₀_def, Forces.not]
  monotone := monotone

open Semantics

lemma sound {T : Theoryᵢ L} (b : T ⊢ φ) : W ∀⊩* T → W ∀⊩ φ := fun H w ↦ by
  rcases domain_nonempty' w with ⟨x, hx⟩
  rcases b with ⟨Γ, hΓ, d⟩
  have hd := Forces.sound d w (fun _ ↦ x) (by simpa using hx) fun ψ hψ ↦ by
    rcases Multiset.mem_map.mp hψ with ⟨σ, hσ, rfl⟩
    simpa [forces₀_def] using H σ (hΓ σ hσ) w
  simpa [forces₀_def, Forces.ForcesHead] using hd

end Forces₀

end KripkeModel

-- `World`'s and `Carrier`'s universes only occur together (via `Domain : World → Set Carrier`),
-- which is intentional here rather than a sign of an unnecessary parameter; keeping them
-- separate documents that the two carriers need not live in the same universe.
set_option linter.checkUnivs false in
/-- Kripke model for intuitionistic first-order logic -/
structure IntKripke (L : Language) [L.Relational] where
  World : Type*
  [nonempty : Nonempty World]
  [preorder : Preorder World]
  Carrier : Type*
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Carrier) → Prop
  rel_monotone : Rel w R t → ∀ v ≤ w, Rel v R t

namespace IntKripke

variable (𝓚 : IntKripke L)

instance : CoeSort (IntKripke L) (Type _) := ⟨fun 𝓚 ↦ 𝓚.World⟩

instance : CoeSort 𝓚 (Type _) := ⟨fun w ↦ 𝓚.Domain w⟩

instance : Nonempty 𝓚 := 𝓚.nonempty

instance : Preorder 𝓚 := 𝓚.preorder

instance : ForcingExists 𝓚 𝓚.Carrier := ⟨fun p x ↦ x ∈ 𝓚.Domain p⟩

instance kripke : KripkeModel L 𝓚 𝓚.Carrier where
  Domain := 𝓚.Domain
  domain_nonempty := 𝓚.domain_nonempty
  domain_antimonotone := 𝓚.domain_antimonotone
  Rel := 𝓚.Rel
  rel_monotone := 𝓚.rel_monotone

open KripkeModel

instance : Semantics (IntKripke L) (Sentenceᵢ L) := ⟨fun 𝓚 φ ↦ 𝓚 ∀⊩ φ⟩

variable {𝓚}

lemma models_def : 𝓚 ⊧ φ ↔ 𝓚 ∀⊩ φ := by rfl

lemma sound {T : Theoryᵢ L} (b : T ⊢ φ) : 𝓚 ⊧* T → 𝓚 ⊧ φ := fun H ↦
  Forces₀.sound (W := 𝓚) b fun _ hφ ↦ H.models_set hφ

instance (T : Theoryᵢ L) : Sound T (Semantics.models (IntKripke L) T) :=
  ⟨fun b _ H ↦ sound b H⟩

lemma sound_empty (b : (∅ : Theoryᵢ L) ⊢ φ) : 𝓚 ⊧ φ := 𝓚.sound b (by simp)

instance : Semantics.Top (IntKripke L) := ⟨fun 𝓚 ↦ by simpa [models_def] using ForcingRelation.AllForces.verum⟩

instance : Semantics.Bot (IntKripke L) := ⟨fun 𝓚 ↦ by
  have : Inhabited 𝓚 := Classical.inhabited_of_nonempty'
  simp [models_def]⟩

instance : Semantics.And (IntKripke L) := ⟨by simp [models_def]⟩

end IntKripke

end LO.FirstOrder
