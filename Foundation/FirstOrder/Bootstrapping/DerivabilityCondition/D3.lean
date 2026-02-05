module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.PeanoMinus

@[expose] public section
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D3}$ and formalized $\Sigma_1$-completeness
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

open Classical

open LO.Entailment LO.Entailment.FiniteContext

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

local prefix:max "#'" => Semiterm.bvar  (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

local postfix:max "⇞" => Semiterm.shift

local postfix:max "⤉" => Semiformula.shift

local infix:40 " ⤕ " => Semiterm.subst

local infix:40 " ⤔ " => Semiformula.subst

variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝗣𝗔⁻ ⪯ T]

variable {T}

lemma eq_comm {t₁ t₂ : Term V ℒₒᵣ} :
    T.internalize V ⊢ t₁ ≐ t₂ → T.internalize V ⊢ t₂ ≐ t₁ := fun h ↦ eq_symm T _ _ ⨀ h

noncomputable abbrev toNumVec (w : Fin n → V) : SemitermVec V ℒₒᵣ n k := ((𝕹 ·)⨟ w)

variable (T)

theorem term_complete {n : ℕ} (t : FirstOrder.ClosedSemiterm ℒₒᵣ n) (w : Fin n → V) :
    T.internalize V ⊢ (toNumVec w ⤕ ⌜t⌝) ≐  𝕹 (t.valbm V w) :=
  match t with
  |                         #z => by simp
  |                         &x => Empty.elim x
  | .func Language.Zero.zero v => by simp
  |   .func Language.One.one v => by simp
  |   .func Language.Add.add v => by
      suffices
          T.internalize V ⊢ (toNumVec w ⤕ ⌜v 0⌝) + (toNumVec w ⤕ ⌜v 1⌝) ≐ 𝕹 ((v 0).valbm V w + (v 1).valbm V w) by
        simpa [Rew.func, Semiterm.val_func]
      have ih : T.internalize V ⊢ (toNumVec w ⤕ ⌜v 0⌝) + (toNumVec w ⤕ ⌜v 1⌝) ≐ 𝕹((v 0).valbm V w) + 𝕹((v 1).valbm V w) :=
        subst_add_eq_add T _ _ _ _ ⨀ term_complete (v 0) w ⨀ term_complete (v 1) w
      have : T.internalize V ⊢ 𝕹((v 0).valbm V w) + 𝕹((v 1).valbm V w) ≐ 𝕹((v 0).valbm V w + (v 1).valbm V w) := numeral_add T _ _
      exact eq_trans ih this
  |   .func Language.Mul.mul v => by
      suffices
          T.internalize V ⊢ (toNumVec w ⤕ ⌜v 0⌝) * (toNumVec w ⤕ ⌜v 1⌝) ≐ 𝕹((v 0).valbm V w * (v 1).valbm V w) by
        simpa [Rew.func, Semiterm.val_func]
      have ih :
          T.internalize V ⊢ (toNumVec w ⤕ ⌜v 0⌝) * (toNumVec w ⤕ ⌜v 1⌝) ≐ 𝕹((v 0).valbm V w) * 𝕹((v 1).valbm V w) :=
        subst_mul_eq_mul T _ _ _ _ ⨀ term_complete (v 0) w ⨀ term_complete (v 1) w
      have :
          T.internalize V ⊢ 𝕹((v 0).valbm V w) * 𝕹((v 1).valbm V w) ≐ 𝕹((v 0).valbm V w * (v 1).valbm V w) := numeral_mul T _ _
      exact eq_trans ih this

open FirstOrder.Arithmetic

theorem bold_sigma_one_complete {n} {φ : Semisentence ℒₒᵣ n} (hp : Hierarchy 𝚺 1 φ) {w} :
    V ⊧/w φ → T.internalize V ⊢ (toNumVec w ⤔ ⌜φ⌝) := by
  revert w
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum => intro n; simp
  case hEQ =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≐ (toNumVec w ⤕ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valbm V w = t₂.valbm V w := by simpa using h
    have h₀ : T.internalize V ⊢     𝕹(t₁.valbm V w) ≐ 𝕹(t₂.valbm V w) := by simp [this]
    have h₁ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≐ 𝕹(t₁.valbm V w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₂⌝) ≐ 𝕹(t₂.valbm V w) := term_complete T t₂ w
    exact eq_trans (eq_trans h₁ h₀) (eq_comm h₂)
  case hNEQ =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≉ (toNumVec w ⤕ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valbm V w ≠ t₂.valbm V w := by simpa using h
    have h₀ : T.internalize V ⊢     𝕹(t₁.valbm V w) ≉ 𝕹(t₂.valbm V w) := by simpa using numeral_ne T this
    have h₁ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≐ 𝕹(t₁.valbm V w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₂⌝) ≐ 𝕹(t₂.valbm V w) := term_complete T t₂ w
    exact subst_ne T _ _ _ _ ⨀ eq_comm h₁ ⨀ eq_comm h₂ ⨀ h₀
  case hLT =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) <' (toNumVec w ⤕ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valbm V w < t₂.valbm V w := by simpa using h
    have h₀ : T.internalize V ⊢     𝕹(t₁.valbm V w) <' 𝕹(t₂.valbm V w) := by simpa using numeral_lt T this
    have h₁ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≐ 𝕹(t₁.valbm V w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₂⌝) ≐ 𝕹(t₂.valbm V w) := term_complete T t₂ w
    exact subst_lt T _ _ _ _ ⨀ eq_comm h₁ ⨀ eq_comm h₂ ⨀ h₀
  case hNLT =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ ((toNumVec w ⤕ ⌜t₁⌝) ≮' (toNumVec w ⤕ ⌜t₂⌝)) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valbm V w ≥ t₂.valbm V w := by simpa using h
    have h₀ : T.internalize V ⊢     𝕹(t₁.valbm V w) ≮' 𝕹(t₂.valbm V w) := by simpa using numeral_nlt T this
    have h₁ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₁⌝) ≐ 𝕹(t₁.valbm V w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ⤕ ⌜t₂⌝) ≐ 𝕹(t₂.valbm V w) := term_complete T t₂ w
    exact subst_nlt T _ _ _ _ ⨀ eq_comm h₁ ⨀ eq_comm h₂ ⨀ h₀
  case hAnd =>
    intro n φ ψ _ _ ihφ ihψ w h
    have H : V ⊧/w φ ∧ V ⊧/w ψ := by simpa using  h
    simpa using K!_intro (ihφ H.1) (ihψ H.2)
  case hOr =>
    intro n φ ψ _ _ ihφ ihψ w h
    suffices T.internalize V ⊢ (toNumVec w ⤔ ⌜φ⌝) ⋎ (toNumVec w ⤔ ⌜ψ⌝) by simpa
    have : V ⊧/w φ ∨ V ⊧/w ψ := by simpa using h
    rcases this with (h | h)
    · apply A!_intro_left (ihφ h)
    · apply A!_intro_right (ihψ h)
  case hBall =>
    intro n t φ _ ih w h
    have h : ∀ i < t.valbm V w, V ⊧/(i :> w) φ := by
      simpa using h
    suffices T.internalize V ⊢ ((toNumVec w).q ⤔ ⌜φ⌝).ball (toNumVec w ⤕ ⌜t⌝) by
      simpa [Semiterm.empty_typed_quote_def, ←Rew.emb_bShift_term, Semiformula.ball, ball, Semiformula.imp_def]
    have : T.internalize V ⊢ ((toNumVec w).q ⤔ ⌜φ⌝).ball 𝕹(t.valbm V w) := by
      apply ball_intro
      intro i hi
      suffices T.internalize V ⊢ (toNumVec (i :> w) ⤔ ⌜φ⌝) by
        simpa [Semiformula.substs_substs, Matrix.map_map_comp']
      exact ih (h i hi)
    exact ball_replace T ((toNumVec w).q ⤔ ⌜φ⌝) _ _ ⨀ (eq_comm <| term_complete T t w) ⨀ this
  case hEx =>
    intro n φ hφ ih w hφ
    have : ∃ a, V ⊧/(a :> w) φ := by simpa using hφ
    rcases this with ⟨i, hφ⟩
    suffices T.internalize V ⊢ ∃' ((toNumVec w).q ⤔ ⌜φ⌝) by simpa
    apply TProof.ex! (𝕹 i)
    suffices T.internalize V ⊢ (toNumVec (i :> w) ⤔ ⌜φ⌝) by
      simpa [Semiformula.substs_substs, Matrix.map_map_comp']
    exact ih hφ

theorem sigma_one_provable_of_models {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
     V ⊧ₘ σ → T.internalize V ⊢ ⌜σ⌝ := by
  intro h
  have : T.internalize V ⊢ (toNumVec ![] ⤔ ⌜σ⌝) :=
    bold_sigma_one_complete T hσ (by simpa [models_iff] using h)
  simpa using this

/-- Hilbert–Bernays provability condition D3 -/
theorem sigma_one_complete {σ : Sentence ℒₒᵣ} (hσ : Hierarchy 𝚺 1 σ) :
    V ⊧ₘ σ → T.Provable (⌜σ⌝ : V) := fun h ↦ by
  simpa [tprovable_iff_provable]
    using Bootstrapping.Arithmetic.sigma_one_provable_of_models T hσ h

theorem provable_internalize {σ : Sentence ℒₒᵣ} :
    T.Provable (⌜σ⌝ : V) → T.Provable (⌜T.provabilityPred σ⌝ : V) := by
  simpa [models_iff] using sigma_one_complete (V := V) (σ := T.provabilityPred σ) T (by simp)

end LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
