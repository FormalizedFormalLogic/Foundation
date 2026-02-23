module

public import Foundation.FirstOrder.Polarity
public import Foundation.LinearLogic.FirstOrder.Calculus

/-! # Girard's embedding of classical logic into linear logic -/

@[expose] public section

namespace LO.FirstOrder

variable {L : Language}

/-! ## $\mathbf{LL}$ to $\mathbf{LK}$ -/

namespace LinearLogic

namespace Semiformula

/-- Forget the linear structure and return a classical first-order formula. -/
def forget : Semiformula L ξ n → FirstOrder.Semiformula L ξ n
  |  rel r v => .rel r v
  | nrel r v => .nrel r v
  | 1 | ⊤ => ⊤
  | ⊥ | 0 => ⊥
  | φ ⨂ ψ | φ ＆ ψ => φ.forget ⋏ ψ.forget
  | φ ⅋ ψ | φ ⨁ ψ => φ.forget ⋎ ψ.forget
  | ∀⁰ φ => ∀⁰ φ.forget
  | ∃⁰ φ => ∃⁰ φ.forget
  | ！φ => φ.forget
  | ？φ => φ.forget

@[simp] lemma forget_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).forget = .rel r v := rfl

@[simp] lemma forget_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).forget = .nrel r v := rfl

@[simp] lemma forget_one : (1 : Semiformula L ξ n).forget = ⊤ := rfl

@[simp] lemma forget_verum : (⊤ : Semiformula L ξ n).forget = ⊤ := rfl

@[simp] lemma forget_falsum : (⊥ : Semiformula L ξ n).forget = ⊥ := rfl

@[simp] lemma forget_zero : (0 : Semiformula L ξ n).forget = ⊥ := rfl

@[simp] lemma forget_tensor (φ ψ : Semiformula L ξ n) : (φ ⨂ ψ).forget = φ.forget ⋏ ψ.forget := rfl

@[simp] lemma forget_with (φ ψ : Semiformula L ξ n) : (φ ＆ ψ).forget = φ.forget ⋏ ψ.forget := rfl

@[simp] lemma forget_par (φ ψ : Semiformula L ξ n) : (φ ⅋ ψ).forget = φ.forget ⋎ ψ.forget := rfl

@[simp] lemma forget_plus (φ ψ : Semiformula L ξ n) : (φ ⨁ ψ).forget = φ.forget ⋎ ψ.forget := rfl

@[simp] lemma forget_all (φ : Semiformula L ξ (n + 1)) : (∀⁰ φ).forget = ∀⁰ φ.forget := rfl

@[simp] lemma forget_exs (φ : Semiformula L ξ (n + 1)) : (∃⁰ φ).forget = ∃⁰ φ.forget := rfl

@[simp] lemma forget_bang (φ : Semiformula L ξ n) : (！φ).forget = φ.forget := rfl

@[simp] lemma forget_quest (φ : Semiformula L ξ n) : (？φ).forget = φ.forget := rfl

@[simp] lemma forget_neg (φ : Semiformula L ξ n) : (∼φ).forget = ∼(φ.forget) := by
  induction φ using rec' <;> simp [*]

@[simp] lemma forget_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    (ω ▹ φ).forget = ω ▹ φ.forget := by
  induction φ using rec' generalizing n₂ <;> simp [*, rew_rel, rew_nrel, FirstOrder.Semiformula.rew_rel, FirstOrder.Semiformula.rew_nrel]

end Semiformula

abbrev Sequent.forget (Γ : Sequent L) : FirstOrder.Sequent L :=
  Γ.map Semiformula.forget

namespace Sequent

@[simp] lemma forget_shift (Γ : Sequent L) : Sequent.forget (Γ⁺) = (Γ.forget)⁺ := by
  simp [Sequent.forget, Rewriting.shifts]

end Sequent

namespace Derivation

def forget {Γ : Sequent L} : ⊢ᴸ Γ → ⊢ᵀ Γ.forget
  | .identity φ => FirstOrder.Derivation.em (φ := φ.forget) (by simp) (by simp)
  | cut (φ := φ) (Γ := Γ) (Δ := Δ) d₁ d₂ =>
    have dp : ⊢ᵀ φ.forget :: Sequent.forget (Γ ++ Δ) := d₁.forget.wk (by simp)
    have dn : ⊢ᵀ ∼φ.forget :: Sequent.forget (Γ ++ Δ) := d₂.forget.wk (by simp)
    dp.cut dn
  | exchange d h => d.forget.wk (by have := h.subset; grind)
  | one => .verum
  | falsum d => d.forget.wk <| by simp
  | par (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    have : ⊢ᵀ φ.forget :: ψ.forget :: Sequent.forget Γ := d.forget.cast (by simp)
    this.or
  | tensor (Γ := Γ) (Δ := Δ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    have dφ : ⊢ᵀ φ.forget :: Sequent.forget (Γ ++ Δ) := d₁.forget.wk (by simp)
    have dψ : ⊢ᵀ ψ.forget :: Sequent.forget (Γ ++ Δ) := d₂.forget.wk (by simp)
    dφ.and dψ
  | verum _ => .verum' <| by simp
  | .with (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    have dφ : ⊢ᵀ φ.forget :: Sequent.forget Γ := d₁.forget.cast (by simp)
    have dψ : ⊢ᵀ ψ.forget :: Sequent.forget Γ := d₂.forget.cast (by simp)
    dφ.and dψ
  | plusRight (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    have : ⊢ᵀ φ.forget :: ψ.forget :: Sequent.forget Γ := d.forget.wk (by simp)
    this.or
  | plusLeft (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    have : ⊢ᵀ φ.forget :: ψ.forget :: Sequent.forget Γ := d.forget.wk (by simp)
    this.or
  | all (Γ := Γ) (φ := φ) d =>
    have : ⊢ᵀ φ.forget.free :: (Sequent.forget Γ)⁺ := d.forget.cast (by simp)
    this.all
  | exs (Γ := Γ) (φ := φ) t d =>
    have : ⊢ᵀ φ.forget/[t] :: Sequent.forget Γ := d.forget.cast (by simp)
    this.exs
  | weakening (Γ := Γ) (φ := φ) d => d.forget.wk (by simp)
  | contraction (Γ := Γ) (φ := φ) d => d.forget.wk (by simp)
  | dereliction (Γ := Γ) (φ := φ) d =>  d.forget.cast (by simp)
  | ofCourse d _ => d.forget.cast (by simp)

end Derivation

namespace Proof

theorem forget {φ : Sentence L} : 𝐋𝐋 ⊢ φ → 𝐋𝐊 ⊢ φ.forget := fun h ↦ by
  have : 𝐋𝐋₀ ⊢ (φ : Statement L) := h
  exact FirstOrder.Proof.cast.mpr ⟨by simpa using Derivation.forget this.get⟩

end Proof

end LinearLogic

/-! ## $\mathbf{LK}$ to $\mathbf{LL}$ -/


namespace Semiformula

/-- Girard embedding -/
def girard {n} : (φ : Semiformula L ξ n) → LinearLogic.Semiformula L ξ n
  |  rel r v => ！.rel r v
  | nrel r v => ？.nrel r v
  |        ⊤ => 1
  |        ⊥ => ⊥
  |    φ ⋏ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girard ⨂ ψ.girard
    |  true, false => φ.girard ⨂ ！ψ.girard
    | false,  true => ！φ.girard ⨂ ψ.girard
    | false, false => φ.girard ＆ ψ.girard
  |    φ ⋎ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girard ⨁ ψ.girard
    |  true, false => ？φ.girard ⅋ ψ.girard
    | false,  true => φ.girard ⅋ ？ψ.girard
    | false, false => φ.girard ⅋ ψ.girard
  |     ∀⁰ φ =>
    match φ.polarity with
    |  true => ∀⁰ ？φ.girard
    | false => ∀⁰ φ.girard
  |     ∃⁰ φ =>
    match φ.polarity with
    |  true => ∃⁰ φ.girard
    | false => ∃⁰ ！φ.girard

@[simp] lemma girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).girard = ！.rel r v := rfl

@[simp] lemma girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girard = ？.nrel r v := rfl

@[simp] lemma girard_verum : (⊤ : Semiformula L ξ n).girard = 1 := rfl

@[simp] lemma girard_falsum : (⊥ : Semiformula L ξ n).girard = ⊥ := rfl

@[simp] lemma girard_neg (φ : Semiformula L ξ n) : (∼φ).girard = ∼(φ.girard) := by
  match φ with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    |  true, false => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    | false,  true => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    | false, false => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
  |    φ ⋎ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    |  true, false => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    | false,  true => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
    | false, false => simp [girard, hφ, hψ, girard_neg φ, girard_neg ψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girard, hφ, girard_neg φ]
    | false => simp [girard, hφ, girard_neg φ]
  |     ∃⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girard, hφ, girard_neg φ]
    | false => simp [girard, hφ, girard_neg φ]

@[simp] lemma girard_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    (ω ▹ φ).girard = ω ▹ φ.girard :=
  match φ with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    |  true, false => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    | false,  true => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    | false, false => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
  |    φ ⋎ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    |  true, false => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    | false,  true => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
    | false, false => by simp [girard, hφ, hψ, girard_rew ω φ, girard_rew ω ψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girard, hφ, girard_rew _ φ]
    | false => by simp [girard, hφ, girard_rew _ φ]
  |     ∃⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girard, hφ, girard_rew _ φ]
    | false => by simp [girard, hφ, girard_rew _ φ]

def Girard (φ : Semiformula L ξ n) : LinearLogic.Semiformula L ξ n :=
  match φ.polarity with
  |  true => ？φ.girard
  | false => φ.girard

@[simp] lemma Girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).Girard = ？！.rel r v := rfl

@[simp] lemma Girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).Girard = ？.nrel r v := rfl

@[simp] lemma Girard_verum : (⊤ : Semiformula L ξ n).Girard = ？1 := rfl

@[simp] lemma Girard_falsum : (⊥ : Semiformula L ξ n).Girard = ⊥ := rfl

@[simp] lemma Girard_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    (ω ▹ φ).Girard = ω ▹ φ.Girard := by
  match h : φ.polarity with
  |  true => simp [Girard, h, girard_rew ω φ]
  | false => simp [Girard, h, girard_rew ω φ]

lemma girard_negative {φ : Semiformula L ξ n} (h : φ.Negative) : φ.girard.Negative := by
  match φ with
  |  rel _ _ => simp_all
  | nrel _ _ => simp_all
  |        ⊤ => simp_all
  |        ⊥ => simp_all
  |    φ ⋏ ψ =>
    have hφ : φ.polarity = false := by simp [Negative] at h; tauto
    have hψ : ψ.polarity = false := by simp [Negative] at h; tauto
    simp [girard, hφ, hψ, girard_negative hφ, girard_negative hψ]
  |    φ ⋎ ψ =>
    have hφ : φ.polarity = false ∨ ψ.polarity = false := by simp [Negative] at h; grind
    rcases hφ with (hφ | hψ)
    · match hψ : ψ.polarity with
      |  true => simp [girard, hφ, hψ, girard_negative hφ]
      | false => simp [girard, hφ, hψ, girard_negative hφ, girard_negative hψ]
    · match hφ : φ.polarity with
      |  true => simp [girard, hφ, hψ, girard_negative hψ]
      | false => simp [girard, hφ, hψ, girard_negative hφ, girard_negative hψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girard, hφ]
    | false => simp [girard, hφ, girard_negative hφ]

lemma girard_positive {φ : Semiformula L ξ n} (h : φ.Positive) : φ.girard.Positive := by
  have : (∼φ).Negative := by simpa
  simpa using girard_negative this

@[simp] lemma girard_negative_iff {φ : Semiformula L ξ n} : φ.girard.Negative ↔ φ.Negative := by
  constructor
  · contrapose
    intro h
    have : φ.girard.Positive := girard_positive (by simpa using h)
    grind
  · intro h; exact girard_negative h

@[simp] lemma girard_positive_iff {φ : Semiformula L ξ n} : φ.girard.Positive ↔ φ.Positive := by
  constructor
  · contrapose
    intro h
    have : φ.girard.Negative := girard_negative (by simpa using h)
    grind
  · intro h; exact girard_positive h

@[simp] lemma Girard_negative (φ : Semiformula L ξ n) : φ.Girard.Negative :=
  match h : φ.polarity with
  |  true => by simp [Girard, h]
  | false => by simp [Girard, h, girard_negative h]

@[simp] lemma forget_girard (φ : Semiformula L ξ n) : φ.girard.forget = φ :=
  match φ with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    |  true, false => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    | false,  true => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    | false, false => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
  |    φ ⋎ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    |  true, false => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    | false,  true => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
    | false, false => by simp [girard, hφ, hψ, forget_girard φ, forget_girard ψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girard, hφ, forget_girard φ]
    | false => by simp [girard, hφ, forget_girard φ]
  |     ∃⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girard, hφ, forget_girard φ]
    | false => by simp [girard, hφ, forget_girard φ]

@[simp] lemma forget_Girard (φ : Semiformula L ξ n) : φ.Girard.forget = φ :=
  match h : φ.polarity with
  |  true => by simp [Girard, h]
  | false => by simp [Girard, h]

end Semiformula

abbrev Sequent.Girard (Γ : Sequent L) : LinearLogic.Sequent L :=
  Γ.map Semiformula.Girard

namespace Sequent

@[simp] lemma girard_negative (Γ : Sequent L) : Γ.Girard.Negative := by
  simp [Sequent.Girard, LinearLogic.Sequent.Negative]

@[simp] lemma shifts_Girard (Γ : Sequent L) : (Γ.Girard)⁺ = Girard (Γ⁺ : Sequent L) := by
  simp [Sequent.Girard, Rewriting.shifts]

end Sequent

namespace Derivation

open LinearLogic

variable [L.DecidableEq]

local postfix:max "†" => Semiformula.girard
local postfix:max "‡" => Semiformula.Girard
local postfix:max "‡" => Sequent.Girard

def toLL {Γ : Sequent L} : ⊢ᵀ Γ → ⊢ᴸ Γ‡
  | .axL R v =>
    have : ⊢ᴸ [？！.rel R v, ？.nrel R v] :=
      LinearLogic.Derivation.identity (！.rel R v) |>.dereliction
    this
  | .cut (φ := φ) d₁ d₂ =>
    match h : φ.polarity with
    |  true =>
      have b₁ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ ∼φ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have b₂ : ⊢ᴸ ∼？φ† :: Γ‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).negativeWk (by simp) (by simp)
    | false =>
      have b₂ : ⊢ᴸ ∼！φ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have b₁ : ⊢ᴸ ！φ† :: Γ‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).negativeWk (by simp) (by simp)
  | .wk d h => d.toLL.negativeWk (List.map_subset Semiformula.Girard h) (by simp)
  | .verum => LinearLogic.Derivation.one.dereliction
  | .and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    match h₁ : φ.polarity, h₂ : ψ.polarity with
    | true, true =>
      have dφ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dψ : ⊢ᴸ ？ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼φ†, ∼ψ†, ？(φ† ⨂ ψ†)] := (LinearLogic.Derivation.identity φ†).tensor (LinearLogic.Derivation.identity ψ†) |>.dereliction.rotate
      have : ⊢ᴸ [∼？φ†, ∼ψ†, ？(φ† ⨂ ψ†)] := this.negativeOfCourse (by simpa using h₂)
      have : ⊢ᴸ ∼ψ† :: ？(φ† ⨂ ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      have : ⊢ᴸ ∼？ψ† :: ？(φ† ⨂ ψ†) :: Γ‡ := this.negativeOfCourse (by simp)
      (dψ.cut this).negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | true, false =>
      have dφ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dψ : ⊢ᴸ ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼φ†, ∼！ψ†, ？(φ† ⨂ ！ψ†)] := (LinearLogic.Derivation.identity φ†).tensor (LinearLogic.Derivation.identity (！ψ†)) |>.dereliction.rotate
      have : ⊢ᴸ [∼？φ†, ∼！ψ†, ？(φ† ⨂ ！ψ†)] := this.ofCourse (by simp)
      have : ⊢ᴸ ∼！ψ† :: ？(φ† ⨂ ！ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      (dψ.negativeOfCourse (by simp)).cut this |>.negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | false, true =>
      have : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dφ : ⊢ᴸ ！φ† :: Γ‡ := this.negativeOfCourse (by simp)
      have dψ : ⊢ᴸ ？ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼！φ†, ∼ψ†, ？(！φ† ⨂ ψ†)] := (LinearLogic.Derivation.identity (！φ†)).tensor (LinearLogic.Derivation.identity ψ†) |>.dereliction.rotate
      have : ⊢ᴸ [∼！φ†, ∼？ψ†, ？(！φ† ⨂ ψ†)] := (this.rotate.ofCourse (by simp)).invRotate
      have : ⊢ᴸ ∼？ψ† :: ？(！φ† ⨂ ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      (dψ.cut this).negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | false, false =>
      have dφ : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dψ : ⊢ᴸ ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (dφ.with dψ).cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    match h₁ : φ.polarity, h₂ : ψ.polarity with
    | true, true =>
      have : ⊢ᴸ ？φ† :: ？ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ ∼(！∼φ† ⨂ ！∼ψ†) :: Γ‡ := this.par.cast (by simp)
      have : ⊢ᴸ [！∼φ† ⨂ ！∼ψ†, ？(φ† ⨁ ψ†)] := LinearLogic.Derivation.expComm _ _
      this.cut d |>.cast (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂])
    | true, false =>
      have : ⊢ᴸ ？φ† :: ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, true =>
      have : ⊢ᴸ φ† :: ？ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, false =>
      have : ⊢ᴸ φ† :: ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .all (φ := φ) (Γ := Γ) d =>
    match h : φ.polarity with
    |  true =>
      have : ⊢ᴸ (？φ†).free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girard, h])
      this.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have : ⊢ᴸ φ†.free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girard, h])
      this.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
  | .exs (Γ := Γ) (φ := φ) t d =>
    match h : φ.polarity with
    |  true =>
      have d : ⊢ᴸ (？φ†)/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have e : ⊢ᴸ [∼(？φ†)/[t], ？(∃⁰ φ†)] :=
        (LinearLogic.Derivation.identity (φ†/[t])).exs.dereliction.rotate.ofCourse (by simp)
      (d.cut e).invRotate.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have : ⊢ᴸ φ†/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ (！φ†)/[t] :: Γ‡ := this.negativeOfCourse (by simp)
      this.exs.dereliction.cast (by simp [Semiformula.Girard, Semiformula.girard, h])

end Derivation

namespace Proof

variable [L.DecidableEq]

theorem girard {φ : Sentence L} : 𝐋𝐊 ⊢ φ → 𝐋𝐋 ⊢ φ.Girard := fun h ↦ ⟨by
  have : 𝐋𝐊₀ ⊢ (φ : SyntacticFormula L) := by simpa using Proof.cast.mp h
  simpa using Derivation.toLL this.get⟩

theorem girard_faithful {φ : Sentence L} : 𝐋𝐊 ⊢ φ ↔ 𝐋𝐋 ⊢ φ.Girard :=
  ⟨girard, fun h ↦ by simpa using LinearLogic.Proof.forget h⟩

end Proof

end LO.FirstOrder
