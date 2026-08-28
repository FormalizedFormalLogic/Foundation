module

public import Foundation.Vorspiel.Order.BooleanAlgebra.Extension
public import Mathlib.Order.Ideal

/-!
# Countable atomless Boolean algebras are isomorphic

Any two countable, nontrivial, atomless (equivalently, densely ordered) Boolean algebras are
order isomorphic (`iso_of_countable_atomless`).
-/

@[expose] public section

open BooleanSubalgebra

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]

lemma BooleanSubalgebra.coe_bot_finite : ((⊥ : BooleanSubalgebra α) : Set α).Finite := by
  rw [coe_bot]; exact (Set.finite_singleton _).insert _

variable (α β) in
/-- A partial isomorphism between `α` and `β`: an order isomorphism between two finite
Boolean subalgebras. -/
structure PartialIso where
  domSubalg : BooleanSubalgebra α
  codSubalg : BooleanSubalgebra β
  finite_dom : (domSubalg : Set α).Finite
  finite_cod : (codSubalg : Set β).Finite
  iso : domSubalg ≃o codSubalg

namespace PartialIso

instance : Preorder (PartialIso α β) where
  le f g := ∃ hA : f.domSubalg ≤ g.domSubalg, ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x
  le_refl _ := ⟨le_refl _, fun _ ↦ rfl⟩
  le_trans _ _ _ := fun ⟨hfg, hfg'⟩ ⟨hgh, hgh'⟩ ↦
    ⟨hfg.trans hgh, fun x ↦ (hgh' ⟨x, hfg x.2⟩).trans (hfg' x)⟩

noncomputable instance [Nontrivial α] [Nontrivial β] : Inhabited (PartialIso α β) :=
  ⟨⟨⊥, ⊥, coe_bot_finite, coe_bot_finite, botOrderIso⟩⟩

def comm : PartialIso α β → PartialIso β α :=
  fun f => ⟨f.codSubalg, f.domSubalg, f.finite_cod, f.finite_dom, f.iso.symm⟩

section

variable {f g : PartialIso α β}

lemma le_def :
    f ≤ g ↔ ∃ hA : f.domSubalg ≤ g.domSubalg,
      ∀ x : f.domSubalg, (g.iso ⟨x, hA x.2⟩ : β) = f.iso x := Iff.rfl

lemma cod_le_of_le (hfg : f ≤ g) : f.codSubalg ≤ g.codSubalg := by
  obtain ⟨hA, hval⟩ := hfg
  intro v hv
  have h : (g.iso ⟨f.iso.symm ⟨v, hv⟩, hA (f.iso.symm ⟨v, hv⟩).2⟩ : β) = v := by
    rw [hval, OrderIso.apply_symm_apply]
  exact h ▸ (g.iso _).2

lemma symm_agree_of_le (hfg : f ≤ g) (v : f.codSubalg) :
    (g.iso.symm ⟨v, cod_le_of_le hfg v.2⟩ : α) = f.iso.symm v := by
  obtain ⟨hA, hval⟩ := id hfg
  have h : g.iso ⟨f.iso.symm v, hA (f.iso.symm v).2⟩ = ⟨v, cod_le_of_le hfg v.2⟩ :=
    Subtype.ext (by rw [hval, OrderIso.apply_symm_apply])
  rw [← h, OrderIso.symm_apply_apply]

lemma comm_le_comm (hfg : f ≤ g) : f.comm ≤ g.comm :=
  ⟨cod_le_of_le hfg, symm_agree_of_le hfg⟩

variable {I : Order.Ideal (PartialIso α β)}

lemma eval_eq_of_mem_of_mem (hf : f ∈ I) (hg : g ∈ I) {a : α}
    (haf : a ∈ f.domSubalg) (hag : a ∈ g.domSubalg) :
    (f.iso ⟨a, haf⟩ : β) = g.iso ⟨a, hag⟩ := by
  obtain ⟨m, _, ⟨_, hfm⟩, ⟨_, hgm⟩⟩ := I.directed f hf g hg
  rw [← hfm ⟨a, haf⟩, ← hgm ⟨a, hag⟩]

lemma symm_eval_eq_of_mem_of_mem (hf : f ∈ I) (hg : g ∈ I) {b : β}
    (hbf : b ∈ f.codSubalg) (hbg : b ∈ g.codSubalg) :
    (f.iso.symm ⟨b, hbf⟩ : α) = g.iso.symm ⟨b, hbg⟩ := by
  obtain ⟨m, _, hfm, hgm⟩ := I.directed f hf g hg
  rw [← symm_agree_of_le hfm ⟨b, hbf⟩, ← symm_agree_of_le hgm ⟨b, hbg⟩]

end

theorem exists_le_mem_dom [Nontrivial β] [DenselyOrdered β]
    (f : PartialIso α β) (a : α) : ∃ g : PartialIso α β, f ≤ g ∧ a ∈ g.domSubalg := by
  obtain ⟨b, h⟩ := exists_isCompanion f.finite_dom f.iso a
  exact ⟨⟨_, _, closure_insert_finite f.finite_dom a, closure_insert_finite f.finite_cod b,
    IsCompanion.extend h⟩, ⟨le_closure_insert, IsCompanion.extend_coe h⟩, self_mem_closure_insert⟩

/-- The cofinal family of partial isomorphisms whose domain contains `a`. -/
def definedAtLeft [Nontrivial β] [DenselyOrdered β] (a : α) : Order.Cofinal (PartialIso α β) where
  carrier := {f | a ∈ f.domSubalg}
  isCofinal f := by
    obtain ⟨g, hfg, hmem⟩ := exists_le_mem_dom f a
    exact ⟨g, hmem, hfg⟩

/-- The cofinal family of partial isomorphisms whose codomain contains `b`. -/
def definedAtRight [Nontrivial α] [DenselyOrdered α] (b : β) : Order.Cofinal (PartialIso α β) where
  carrier := {f | b ∈ f.codSubalg}
  isCofinal f := by
    obtain ⟨g, hmem, hfg⟩ := (definedAtLeft (β := α) b).isCofinal f.comm
    exact ⟨g.comm, hmem, comm_le_comm hfg⟩

end PartialIso

open PartialIso

theorem iso_of_countable_atomless
    [Countable α] [Nontrivial α] [DenselyOrdered α]
    [Countable β] [Nontrivial β] [DenselyOrdered β] :
    Nonempty (α ≃o β) := by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let toCofinal : α ⊕ β → Order.Cofinal (PartialIso α β) := fun p ↦
    Sum.recOn p definedAtLeft definedAtRight
  let I : Order.Ideal (PartialIso α β) := Order.idealOfCofinals default toCofinal
  have hF : ∀ a : α, ∃ b : β, ∃ f ∈ I, ∃ h : a ∈ f.domSubalg, (f.iso ⟨a, h⟩ : β) = b := by
    intro a
    obtain ⟨f, hmem, hI⟩ := Order.cofinal_meets_idealOfCofinals default toCofinal (Sum.inl a)
    exact ⟨f.iso ⟨a, hmem⟩, f, hI, hmem, rfl⟩
  have hG : ∀ b : β, ∃ a : α, ∃ f ∈ I, ∃ h : b ∈ f.codSubalg, (f.iso.symm ⟨b, h⟩ : α) = a := by
    intro b
    obtain ⟨f, hmem, hI⟩ := Order.cofinal_meets_idealOfCofinals default toCofinal (Sum.inr b)
    exact ⟨f.iso.symm ⟨b, hmem⟩, f, hI, hmem, rfl⟩
  choose F hFspec using hF
  choose G hGspec using hG
  have hleft : ∀ a, G (F a) = a := by
    intro a
    obtain ⟨f, hfI, haf, hfa⟩ := hFspec a
    obtain ⟨g, hgI, hb, hgb⟩ := hGspec (F a)
    have hbf : F a ∈ f.codSubalg := hfa ▸ (f.iso ⟨a, haf⟩).2
    have h : (f.iso.symm ⟨F a, hbf⟩ : α) = G (F a) := by
      rw [symm_eval_eq_of_mem_of_mem hfI hgI hbf hb, hgb]
    rw [← h, show (⟨F a, hbf⟩ : f.codSubalg) = f.iso ⟨a, haf⟩ from Subtype.ext hfa.symm,
      OrderIso.symm_apply_apply]
  have hright : ∀ b, F (G b) = b := by
    intro b
    obtain ⟨g, hgI, hbg, hgb⟩ := hGspec b
    obtain ⟨f, hfI, ha, hfa⟩ := hFspec (G b)
    have hag : G b ∈ g.domSubalg := hgb ▸ (g.iso.symm ⟨b, hbg⟩).2
    rw [← hfa, eval_eq_of_mem_of_mem hfI hgI ha hag,
      show (⟨G b, hag⟩ : g.domSubalg) = g.iso.symm ⟨b, hbg⟩ from Subtype.ext hgb.symm,
      OrderIso.apply_symm_apply]
  have hrel : ∀ a₁ a₂ : α, F a₁ ≤ F a₂ ↔ a₁ ≤ a₂ := by
    intro a₁ a₂
    obtain ⟨f, hfI, h₁, hf₁⟩ := hFspec a₁
    obtain ⟨g, hgI, h₂, hf₂⟩ := hFspec a₂
    obtain ⟨m, hmI, ⟨hfm, _⟩, ⟨hgm, _⟩⟩ := I.directed f hfI g hgI
    rw [← hf₁, ← hf₂, eval_eq_of_mem_of_mem hfI hmI h₁ (hfm h₁),
      eval_eq_of_mem_of_mem hgI hmI h₂ (hgm h₂), Subtype.coe_le_coe, m.iso.le_iff_le,
      Subtype.mk_le_mk]
  exact ⟨⟨⟨F, G, hleft, hright⟩, hrel _ _⟩⟩
