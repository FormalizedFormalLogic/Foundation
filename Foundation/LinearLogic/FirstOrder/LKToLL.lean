module

public import Foundation.FirstOrder.Polarity
public import Foundation.LinearLogic.FirstOrder.Calculus

/-! # Girard's embedding of classical logic into linear logic -/

@[expose] public section

namespace List

variable {α : Type*}


end List

namespace LO.FirstOrder

variable {L : Language}

namespace Semiformula

def girardₗ {n} : (φ : Semiformula L ξ n) → LinearLogic.Semiformula L ξ n
  |  rel r v => ！.rel r v
  | nrel r v => ？.nrel r v
  |        ⊤ => 1
  |        ⊥ => ⊥
  |    φ ⋏ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girardₗ ⨂ ψ.girardₗ
    |  true, false => φ.girardₗ ⨂ ！ψ.girardₗ
    | false,  true => ！φ.girardₗ ⨂ ψ.girardₗ
    | false, false => φ.girardₗ ＆ ψ.girardₗ
  |    φ ⋎ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girardₗ ⨁ ψ.girardₗ
    |  true, false => ？φ.girardₗ ⅋ ψ.girardₗ
    | false,  true => φ.girardₗ ⅋ ？ψ.girardₗ
    | false, false => φ.girardₗ ⅋ ψ.girardₗ
  |     ∀⁰ φ =>
    match φ.polarity with
    |  true => ∀⁰ ？φ.girardₗ
    | false => ∀⁰ φ.girardₗ
  |     ∃⁰ φ =>
    match φ.polarity with
    |  true => ∃⁰ φ.girardₗ
    | false => ∃⁰ ！φ.girardₗ

@[simp] lemma girardₗ_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).girardₗ = ！.rel r v := rfl

@[simp] lemma girardₗ_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girardₗ = ？.nrel r v := rfl

@[simp] lemma girardₗ_verum : (⊤ : Semiformula L ξ n).girardₗ = 1 := rfl

@[simp] lemma girardₗ_falsum : (⊥ : Semiformula L ξ n).girardₗ = ⊥ := rfl

@[simp] lemma girardₗ_neg (φ : Semiformula L ξ n) : (∼φ).girardₗ = ∼(φ.girardₗ) := by
  match φ with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    |  true, false => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    | false,  true => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    | false, false => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
  |    φ ⋎ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    |  true, false => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    | false,  true => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
    | false, false => simp [girardₗ, hφ, hψ, girardₗ_neg φ, girardₗ_neg ψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girardₗ, hφ, girardₗ_neg φ]
    | false => simp [girardₗ, hφ, girardₗ_neg φ]
  |     ∃⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girardₗ, hφ, girardₗ_neg φ]
    | false => simp [girardₗ, hφ, girardₗ_neg φ]

@[simp] lemma girardₗ_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    (ω ▹ φ).girardₗ = ω ▹ φ.girardₗ :=
  match φ with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    φ ⋏ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    |  true, false => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    | false,  true => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    | false, false => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
  |    φ ⋎ ψ =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    |  true, false => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    | false,  true => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
    | false, false => by simp [girardₗ, hφ, hψ, girardₗ_rew ω φ, girardₗ_rew ω ψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girardₗ, hφ, girardₗ_rew _ φ]
    | false => by simp [girardₗ, hφ, girardₗ_rew _ φ]
  |     ∃⁰ φ =>
    match hφ : φ.polarity with
    |  true => by simp [girardₗ, hφ, girardₗ_rew _ φ]
    | false => by simp [girardₗ, hφ, girardₗ_rew _ φ]

def Girardₗ (φ : Semiformula L ξ n) : LinearLogic.Semiformula L ξ n :=
  match φ.polarity with
  |  true => ？φ.girardₗ
  | false => φ.girardₗ

@[simp] lemma Girardₗ_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).Girardₗ = ？！.rel r v := rfl

@[simp] lemma Girardₗ_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).Girardₗ = ？.nrel r v := rfl

@[simp] lemma Girardₗ_verum : (⊤ : Semiformula L ξ n).Girardₗ = ？1 := rfl

@[simp] lemma Girardₗ_falsum : (⊥ : Semiformula L ξ n).Girardₗ = ⊥ := rfl

@[simp] lemma Girardₗ_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) :
    (ω ▹ φ).Girardₗ = ω ▹ φ.Girardₗ := by
  match h : φ.polarity with
  |  true => simp [Girardₗ, h, girardₗ_rew ω φ]
  | false => simp [Girardₗ, h, girardₗ_rew ω φ]

lemma girardₗ_negative {φ : Semiformula L ξ n} (h : φ.Negative) : φ.girardₗ.Negative := by
  match φ with
  |  rel _ _ => simp_all
  | nrel _ _ => simp_all
  |        ⊤ => simp_all
  |        ⊥ => simp_all
  |    φ ⋏ ψ =>
    have hφ : φ.polarity = false := by simp [Negative] at h; tauto
    have hψ : ψ.polarity = false := by simp [Negative] at h; tauto
    simp [girardₗ, hφ, hψ, girardₗ_negative hφ, girardₗ_negative hψ]
  |    φ ⋎ ψ =>
    have hφ : φ.polarity = false ∨ ψ.polarity = false := by simp [Negative] at h; grind
    rcases hφ with (hφ | hψ)
    · match hψ : ψ.polarity with
      |  true => simp [girardₗ, hφ, hψ, girardₗ_negative hφ]
      | false => simp [girardₗ, hφ, hψ, girardₗ_negative hφ, girardₗ_negative hψ]
    · match hφ : φ.polarity with
      |  true => simp [girardₗ, hφ, hψ, girardₗ_negative hψ]
      | false => simp [girardₗ, hφ, hψ, girardₗ_negative hφ, girardₗ_negative hψ]
  |     ∀⁰ φ =>
    match hφ : φ.polarity with
    |  true => simp [girardₗ, hφ]
    | false => simp [girardₗ, hφ, girardₗ_negative hφ]

lemma girardₗ_positive {φ : Semiformula L ξ n} (h : φ.Positive) : φ.girardₗ.Positive := by
  have : (∼φ).Negative := by simpa
  simpa using girardₗ_negative this

@[simp] lemma girardₗ_negative_iff {φ : Semiformula L ξ n} : φ.girardₗ.Negative ↔ φ.Negative := by
  constructor
  · contrapose
    intro h
    have : φ.girardₗ.Positive := girardₗ_positive (by simpa using h)
    grind
  · intro h; exact girardₗ_negative h

@[simp] lemma girardₗ_positive_iff {φ : Semiformula L ξ n} : φ.girardₗ.Positive ↔ φ.Positive := by
  constructor
  · contrapose
    intro h
    have : φ.girardₗ.Negative := girardₗ_negative (by simpa using h)
    grind
  · intro h; exact girardₗ_positive h

@[simp] lemma Girardₗ_negative (φ : Semiformula L ξ n) : φ.Girardₗ.Negative :=
  match h : φ.polarity with
  |  true => by simp [Girardₗ, h]
  | false => by simp [Girardₗ, h, girardₗ_negative h]

end Semiformula

abbrev Sequent.Girardₗ (Γ : Sequent L) : LinearLogic.Sequent L :=
  Γ.map Semiformula.Girardₗ

namespace Sequent

@[simp] lemma girardₗ_negative (Γ : Sequent L) : Γ.Girardₗ.Negative := by
  simp [Sequent.Girardₗ, LinearLogic.Sequent.Negative]

@[simp] lemma shifts_Girardₗ (Γ : Sequent L) : (Γ.Girardₗ)⁺ = Girardₗ (Γ⁺ : Sequent L) := by
  simp [Sequent.Girardₗ, Rewriting.shifts]

end Sequent

namespace Derivation

open LinearLogic

variable [L.DecidableEq]

local postfix:max "†" => Semiformula.girardₗ
local postfix:max "‡" => Semiformula.Girardₗ
local postfix:max "‡" => Sequent.Girardₗ

def toLL {Γ : Sequent L} : ⊢ᵀ Γ → ⊢ᴸ Γ‡
  | .axL R v =>
    have : ⊢ᴸ [？！.rel R v, ？.nrel R v] :=
      LinearLogic.Derivation.identity (！.rel R v) |>.dereliction
    this
  | .cut (φ := φ) d₁ d₂ =>
    match h : φ.polarity with
    |  true =>
      have b₁ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have : ⊢ᴸ ∼φ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have b₂ : ⊢ᴸ ∼？φ† :: Γ‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).negativeWk (by simp) (by simp)
    | false =>
      have b₂ : ⊢ᴸ ∼！φ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have b₁ : ⊢ᴸ ！φ† :: Γ‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).negativeWk (by simp) (by simp)
  | .wk d h => d.toLL.negativeWk (List.map_subset Semiformula.Girardₗ h) (by simp)
  | .verum => LinearLogic.Derivation.one.dereliction
  | .and (Γ := Γ) (φ := φ) (ψ := ψ) d₁ d₂ =>
    match h₁ : φ.polarity, h₂ : ψ.polarity with
    | true, true =>
      have dφ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h₁])
      have dψ : ⊢ᴸ ？ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h₂])
      have : ⊢ᴸ [∼φ†, ∼ψ†, ？(φ† ⨂ ψ†)] := (LinearLogic.Derivation.identity φ†).tensor (LinearLogic.Derivation.identity ψ†) |>.dereliction.rotate
      have : ⊢ᴸ [∼？φ†, ∼ψ†, ？(φ† ⨂ ψ†)] := this.negativeOfCourse (by simpa using h₂)
      have : ⊢ᴸ ∼ψ† :: ？(φ† ⨂ ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      have : ⊢ᴸ ∼？ψ† :: ？(φ† ⨂ ψ†) :: Γ‡ := this.negativeOfCourse (by simp)
      (dψ.cut this).negativeWk (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]) (by simp)
    | true, false =>
      have dφ : ⊢ᴸ ？φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h₁])
      have dψ : ⊢ᴸ ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h₂])
      have : ⊢ᴸ [∼φ†, ∼！ψ†, ？(φ† ⨂ ！ψ†)] := (LinearLogic.Derivation.identity φ†).tensor (LinearLogic.Derivation.identity (！ψ†)) |>.dereliction.rotate
      have : ⊢ᴸ [∼？φ†, ∼！ψ†, ？(φ† ⨂ ！ψ†)] := this.ofCourse (by simp)
      have : ⊢ᴸ ∼！ψ† :: ？(φ† ⨂ ！ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      (dψ.negativeOfCourse (by simp)).cut this |>.negativeWk (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]) (by simp)
    | false, true =>
      have : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h₁])
      have dφ : ⊢ᴸ ！φ† :: Γ‡ := this.negativeOfCourse (by simp)
      have dψ : ⊢ᴸ ？ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h₂])
      have : ⊢ᴸ [∼！φ†, ∼ψ†, ？(！φ† ⨂ ψ†)] := (LinearLogic.Derivation.identity (！φ†)).tensor (LinearLogic.Derivation.identity ψ†) |>.dereliction.rotate
      have : ⊢ᴸ [∼！φ†, ∼？ψ†, ？(！φ† ⨂ ψ†)] := (this.rotate.ofCourse (by simp)).invRotate
      have : ⊢ᴸ ∼？ψ† :: ？(！φ† ⨂ ψ†) :: Γ‡ := (dφ.cut this).exchange (by grind)
      (dψ.cut this).negativeWk (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]) (by simp)
    | false, false =>
      have dφ : ⊢ᴸ φ† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girardₗ, h₁])
      have dψ : ⊢ᴸ ψ† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girardₗ, h₂])
      (dφ.with dψ).cast <| by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]
  | .or (Γ := Γ) (φ := φ) (ψ := ψ) d =>
    match h₁ : φ.polarity, h₂ : ψ.polarity with
    | true, true =>
      have : ⊢ᴸ ？φ† :: ？ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h₁, h₂])
      have d : ⊢ᴸ ∼(！∼φ† ⨂ ！∼ψ†) :: Γ‡ := this.par.cast (by simp)
      have : ⊢ᴸ [！∼φ† ⨂ ！∼ψ†, ？(φ† ⨁ ψ†)] := LinearLogic.Derivation.expComm _ _
      this.cut d |>.cast (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂])
    | true, false =>
      have : ⊢ᴸ ？φ† :: ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]
    | false, true =>
      have : ⊢ᴸ φ† :: ？ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]
    | false, false =>
      have : ⊢ᴸ φ† :: ψ† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h₁, h₂]
  | .all (φ := φ) (Γ := Γ) d =>
    match h : φ.polarity with
    |  true =>
      have : ⊢ᴸ (？φ†).free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girardₗ, h])
      this.all.cast (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h])
    | false =>
      have : ⊢ᴸ φ†.free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girardₗ, h])
      this.all.cast (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h])
  | .exs (Γ := Γ) (φ := φ) t d =>
    match h : φ.polarity with
    |  true =>
      have d : ⊢ᴸ (？φ†)/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have e : ⊢ᴸ [∼(？φ†)/[t], ？(∃⁰ φ†)] :=
        (LinearLogic.Derivation.identity (φ†/[t])).exs.dereliction.rotate.ofCourse (by simp)
      (d.cut e).invRotate.cast (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h])
    | false =>
      have : ⊢ᴸ φ†/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girardₗ, h])
      have : ⊢ᴸ (！φ†)/[t] :: Γ‡ := this.negativeOfCourse (by simp)
      this.exs.dereliction.cast (by simp [Semiformula.Girardₗ, Semiformula.girardₗ, h])

end Derivation


end LO.FirstOrder
