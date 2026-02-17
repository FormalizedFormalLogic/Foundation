module

public import Foundation.FirstOrder.Polarity
public import Foundation.LinearLogic.FirstOrder.Calculus

/-! # Girard's embedding of classical logic into linear logic -/

@[expose] public section

namespace LO.FirstOrder

variable {L : Language}

namespace Semiformula

def girardₗ {n} : (φ : Semiformula L ξ n) → LinearLogic.Semiformula L ξ n
  |  rel r v => .rel r v
  | nrel r v => ！.nrel r v
  |        ⊤ => 1
  |        ⊥ => ⊥
  |    φ ⋏ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girardₗ ⨂ ψ.girardₗ
    |  true, false => ！φ.girardₗ ⨂ ψ.girardₗ
    | false,  true => φ.girardₗ ⨂ ！ψ.girardₗ
    | false, false => φ.girardₗ ＆ ψ.girardₗ
  |    φ ⋎ ψ =>
    match φ.polarity, ψ.polarity with
    |  true,  true => φ.girardₗ ⨁ ψ.girardₗ
    |  true, false => φ.girardₗ ⅋ ？ψ.girardₗ
    | false,  true => ？φ.girardₗ ⅋ ψ.girardₗ
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
    (rel r v).girardₗ = .rel r v := rfl

@[simp] lemma girardₗ_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girardₗ = ！.nrel r v := rfl

@[simp] lemma girardₗ_verum : (⊤ : Semiformula L ξ n).girardₗ = 1 := rfl

@[simp] lemma girardₗ_falsum : (⊥ : Semiformula L ξ n).girardₗ = ⊥ := rfl

end Semiformula

namespace Derivation



end Derivation


end LO.FirstOrder
