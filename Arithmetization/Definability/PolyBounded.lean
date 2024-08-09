import Arithmetization.Definability.Hierarchy

namespace LO.FirstOrder.Arith

open LO.Arith

variable {L : Language} [L.ORing] {ξ : Type*} {n : ℕ}

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻] [Structure L M] [Structure.ORing L M] [Structure.Monotone L M]

variable {Γ : HierarchySymbol}

variable (L Γ)

class Bounded (f : (Fin k → M) → M) : Prop where
  bounded : ∃ t : Semiterm L M k, ∀ v : Fin k → M, f v ≤ t.valm M v id

abbrev Bounded₁ (f : M → M) : Prop := Bounded L (k := 1) (fun v ↦ f (v 0))

abbrev Bounded₂ (f : M → M → M) : Prop := Bounded L (k := 2) (fun v ↦ f (v 0) (v 1))

abbrev Bounded₃ (f : M → M → M → M) : Prop := Bounded L (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))

instance (f : (Fin k → M) → M) [h : Bounded ℒₒᵣ f] : Bounded L f := by
  rcases h with ⟨t, ht⟩
  exact ⟨Semiterm.lMap Language.oringEmb t, by simpa⟩

variable {L Γ}

namespace Bounded

@[simp] lemma var {k} (i : Fin k) : Bounded L fun v : Fin k → M ↦ v i := ⟨#i, by intro _; simp⟩

@[simp] lemma const {k} (c : M) : Bounded L (fun _ : Fin k → M ↦ c) := ⟨&c, by intro _; simp⟩

@[simp] lemma term_retraction (t : Semiterm L M n) (e : Fin n → Fin k) :
    Bounded L fun v : Fin k → M ↦ Semiterm.valm M (fun x ↦ v (e x)) id t :=
  ⟨Rew.substs (fun x ↦ #(e x)) t, by intro _; simp [Semiterm.val_substs]⟩

@[simp] lemma term (t : Semiterm L M k) : Bounded L fun v : Fin k → M => Semiterm.valm M v id t :=
  ⟨t, by intro _; simp⟩

lemma retraction {f : (Fin k → M) → M} (hf : Bounded L f) (e : Fin k → Fin n) :
    Bounded L fun v ↦ f (fun i ↦ v (e i)) := by
  rcases hf with ⟨t, ht⟩
  exact ⟨Rew.substs (fun x ↦ #(e x)) t, by intro; simp [Semiterm.val_substs, ht]⟩

lemma comp {k} {f : (Fin l → M) → M} {g : Fin l → (Fin k → M) → M} (hf : Bounded L f) (hg : ∀ i, Bounded L (g i)) :
    Bounded L (fun v ↦ f (g · v)) where
  bounded := by
    rcases hf.bounded with ⟨tf, htf⟩
    choose tg htg using fun i ↦ (hg i).bounded
    exact ⟨Rew.substs tg tf, by
      intro v; simp [Semiterm.val_substs]
      exact le_trans (htf (g · v)) (Structure.Monotone.term_monotone tf (fun i ↦ htg i v) (by simp))⟩

end Bounded

lemma Bounded₁.comp {f : M → M} {k} {g : (Fin k → M) → M} (hf : Bounded₁ L f) (hg : Bounded L g) :
    Bounded L (fun v ↦ f (g v)) := Bounded.comp hf (l := 1) (fun _ ↦ hg)

lemma Bounded₂.comp {f : M → M → M} {k} {g₁ g₂ : (Fin k → M) → M}
    (hf : Bounded₂ L f) (hg₁ : Bounded L g₁) (hg₂ : Bounded L g₂) :
    Bounded L (fun v ↦ f (g₁ v) (g₂ v)) := Bounded.comp hf (g := ![g₁, g₂]) (fun i ↦ by cases i using Fin.cases <;> simp [*])

lemma Bounded₃.comp {f : M → M → M → M} {k} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : Bounded₃ L f) (hg₁ : Bounded L g₁) (hg₂ : Bounded L g₂) (hg₃ : Bounded L g₃) :
    Bounded L (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := Bounded.comp hf (g := ![g₁, g₂, g₃])
      (fun i ↦ by
        cases' i using Fin.cases with i <;> simp [*]
        cases' i using Fin.cases with i <;> simp [*])

namespace Bounded₂

instance add : Bounded₂ L ((· + ·) : M → M → M) where
  bounded := ⟨‘x y | x + y’, by intro _; simp⟩

instance mul : Bounded₂ L ((· * ·) : M → M → M) where
  bounded := ⟨‘x y | x * y’, by intro _; simp⟩

instance hAdd : Bounded₂ L (HAdd.hAdd : M → M → M) where
  bounded := ⟨‘x y | x + y’, by intro _; simp⟩

instance hMul : Bounded₂ L (HMul.hMul : M → M → M) where
  bounded := ⟨‘x y | x * y’, by intro _; simp⟩

end Bounded₂

variable (L Γ)

def DefinableBoundedFunction {k} (f : (Fin k → M) → M) := Bounded L f ∧ DefinableFunction L Γ f

abbrev DefinableBoundedFunction₁ (f : M → M) : Prop := DefinableBoundedFunction L Γ (k := 1) (fun v => f (v 0))

abbrev DefinableBoundedFunction₂ (f : M → M → M) : Prop := DefinableBoundedFunction L Γ (k := 2) (fun v => f (v 0) (v 1))

abbrev DefinableBoundedFunction₃ (f : M → M → M → M) : Prop := DefinableBoundedFunction L Γ (k := 3) (fun v => f (v 0) (v 1) (v 2))

variable {L Γ}

lemma DefinableBoundedFunction.bounded {f : (Fin k → M) → M} (h : DefinableBoundedFunction L Γ f) : Bounded L f := h.1

lemma DefinableBoundedFunction₁.bounded {f : M → M} (h : DefinableBoundedFunction₁ L Γ f) : Bounded₁ L f := h.1

lemma DefinableBoundedFunction₂.bounded {f : M → M → M} (h : DefinableBoundedFunction₂ L Γ f) : Bounded₂ L f := h.1

lemma DefinableBoundedFunction₃.bounded {f : M → M → M → M} (h : DefinableBoundedFunction₃ L Γ f) : Bounded₃ L f := h.1

lemma DefinableBoundedFunction.definable {f : (Fin k → M) → M} (h : DefinableBoundedFunction L Γ f) : DefinableFunction L Γ f := h.2

lemma DefinableBoundedFunction₁.definable {f : M → M} (h : DefinableBoundedFunction₁ L Γ f) : DefinableFunction₁ L Γ f := h.2

lemma DefinableBoundedFunction₂.definable {f : M → M → M} (h : DefinableBoundedFunction₂ L Γ f) : DefinableFunction₂ L Γ f := h.2

lemma DefinableBoundedFunction₃.definable {f : M → M → M → M} (h : DefinableBoundedFunction₃ L Γ f) : DefinableFunction₃ L Γ f := h.2

namespace DefinableBoundedFunction

lemma of_polybounded_of_definable (f : (Fin k → M) → M) [hb : Bounded L f] [hf : DefinableFunction L Γ f] :
    DefinableBoundedFunction L Γ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₁ (f : M → M) [hb : Bounded₁ L f] [hf : DefinableFunction₁ L Γ f] :
    DefinableBoundedFunction₁ L Γ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₂ (f : M → M → M) [hb : Bounded₂ L f] [hf : DefinableFunction₂ L Γ f] :
    DefinableBoundedFunction₂ L Γ f := ⟨hb, hf⟩

@[simp] lemma of_polybounded_of_definable₃ (f : M → M → M → M) [hb : Bounded₃ L f] [hf : DefinableFunction₃ L Γ f] :
    DefinableBoundedFunction₃ L Γ f := ⟨hb, hf⟩

lemma retraction {f : (Fin k → M) → M} (hf : DefinableBoundedFunction L Γ f) (e : Fin k → Fin n) :
    DefinableBoundedFunction L Γ fun v ↦ f (fun i ↦ v (e i)) := ⟨hf.bounded.retraction e, hf.definable.retraction e⟩

lemma of_zero {Γ' Γ} {f : (Fin k → M) → M} (h : DefinableBoundedFunction L (Γ', 0) f) :
    DefinableBoundedFunction L (Γ, 0) f := by
  rcases h with ⟨hb, h⟩
  exact ⟨hb, .of_zero h _⟩

lemma of_delta {f : (Fin k → M) → M} (h : DefinableBoundedFunction L (𝚫, m) f) {Γ} : DefinableBoundedFunction L (Γ, m) f :=
  ⟨h.bounded, h.definable.of_delta⟩

end DefinableBoundedFunction

namespace Definable

variable {P Q : (Fin k → M) → Prop}

lemma ball_lt₀ {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableBoundedFunction L Γ f) (h : Definable L Γ (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ (fun v ↦ ∀ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  have : DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm M v id bf, x = f v ∧ ∀ y < x, P v y)
    (HSemiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HSemiformula.ball (#0) (HSemiformula.rew (Rew.substs (#0 :> fun i => #i.succ.succ)) p))) := by
    simpa [←le_iff_lt_succ] using (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).ball #0)).bex ‘!!bf + 1’
  exact .of_iff _ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩) ⟨_, this⟩

lemma bex_lt₀ {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableBoundedFunction L Γ f) (h : Definable L Γ (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ (fun v ↦ ∃ x < f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  have : DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm M v id bf, x = f v ∧ ∃ y < x, P v y)
    (HSemiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HSemiformula.bex (#0) (HSemiformula.rew (Rew.substs (#0 :> fun i => #i.succ.succ)) p))) := by
    simpa [←le_iff_lt_succ] using (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).bex #0)).bex ‘!!bf + 1’
  exact .of_iff _ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩) ⟨_, this⟩

lemma ball_le₀ {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableBoundedFunction L Γ f) (h : Definable L Γ (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ (fun v ↦ ∀ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  have : DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm M v id bf, x = f v ∧ ∀ y ≤ x, P v y)
    (HSemiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HSemiformula.ball ‘x | x + 1’ (HSemiformula.rew (Rew.substs (#0 :> fun i => #i.succ.succ)) p))) := by
    simpa [←le_iff_lt_succ] using (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).ball ‘x | x + 1’)).bex ‘!!bf + 1’
  exact .of_iff _ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩) ⟨_, this⟩

lemma bex_le₀ {P : (Fin k → M) → M → Prop} {f : (Fin k → M) → M}
    (hf : DefinableBoundedFunction L Γ f) (h : Definable L Γ (fun w ↦ P (w ·.succ) (w 0))) :
    Definable L Γ (fun v ↦ ∃ x ≤ f v, P v x) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  rcases hf.definable with ⟨f_graph, hf_graph⟩
  rcases h with ⟨p, hp⟩
  have : DefinedWithParam (fun v ↦ ∃ x ≤ Semiterm.valm M v id bf, x = f v ∧ ∃ y ≤ x, P v y)
    (HSemiformula.bex ‘!!bf + 1’
      (f_graph ⋏ HSemiformula.bex ‘x | x + 1’ (HSemiformula.rew (Rew.substs (#0 :> fun i => #i.succ.succ)) p))) := by
    simpa [←le_iff_lt_succ] using (hf_graph.and ((hp.retraction (0 :> (·.succ.succ))).bex ‘x | x + 1’)).bex ‘!!bf + 1’
  exact .of_iff _ (fun v ↦ ⟨fun h ↦ ⟨f v, hbf v, rfl, h⟩, by rintro ⟨y, hy, rfl, h⟩; exact h⟩) ⟨_, this⟩

end Definable

namespace DefinableBoundedFunction

lemma of_iff {g : (Fin k → M) → M} (f) (h : ∀ v, f v = g v) (H : DefinableBoundedFunction L Γ f) : DefinableBoundedFunction L Γ g := by
  have : f = g := by funext v; simp [h]
  rcases this; exact H

@[simp] lemma var {k} (i : Fin k) : DefinableBoundedFunction L Γ (fun v : Fin k → M ↦ v i) := ⟨by simp, by simp⟩

@[simp] lemma const {k} (c : M) : DefinableBoundedFunction L Γ (fun _ : Fin k → M ↦ c) := ⟨by simp, by simp⟩

@[simp] lemma term_retraction (t : Semiterm L M n) (e : Fin n → Fin k) :
    DefinableBoundedFunction L Γ fun v : Fin k → M ↦ Semiterm.valm M (fun x ↦ v (e x)) id t := ⟨by simp, by simp⟩

@[simp] lemma term (t : Semiterm L M k) :
  DefinableBoundedFunction L Γ fun v : Fin k → M ↦ Semiterm.valm M v id t := ⟨by simp, by simp⟩

end DefinableBoundedFunction

namespace Definable

lemma bcomp₁ {k} {P : M → Prop} {f : (Fin k → M) → M} [hP : DefinablePred L Γ P] (hf : DefinableBoundedFunction L Γ f) :
    Definable L Γ (fun v ↦ P (f v)) := by
  rcases hf.bounded with ⟨bf, hbf⟩
  have : Definable L Γ fun v ↦ ∃ z ≤ Semiterm.valm M v id bf, z = f v ∧ P z :=
    bex_le₀ (by simp) (and hf.definable <| hP.retraction (fun _ ↦ 0))
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f v, hbf v, rfl, h⟩
    · rintro ⟨_, _, rfl, h⟩; exact h)

lemma bcomp₂ {k} {R : M → M → Prop} {f₁ f₂ : (Fin k → M) → M}
    [hR : DefinableRel L Γ R] (hf₁ : DefinableBoundedFunction L Γ f₁) (hf₂ : DefinableBoundedFunction L Γ f₂) :
    Definable L Γ (fun v ↦ R (f₁ v) (f₂ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  have : Definable L Γ (fun v ↦
      ∃ z₁ ≤ Semiterm.valm M v id bf₁, ∃ z₂ ≤ Semiterm.valm M v id bf₂, z₁ = f₁ v ∧ z₂ = f₂ v ∧ R z₁ z₂) :=
    bex_le₀ (DefinableBoundedFunction.term _) <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _)
      <| and (hf₁.definable.rel.retraction _)
        <| and (by simpa using hf₂.definable.rel.retraction (0 :> (·.succ.succ)))
          <| by simpa using hR.retraction (n := k + 2) ![1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, rfl, rfl, h⟩; exact h)

lemma bcomp₃ {k} {R : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hR : DefinableRel₃ L Γ R] (hf₁ : DefinableBoundedFunction L Γ f₁) (hf₂ : DefinableBoundedFunction L Γ f₂) (hf₃ : DefinableBoundedFunction L Γ f₃) :
    Definable L Γ (fun v ↦ R (f₁ v) (f₂ v) (f₃ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  have : Definable L Γ (fun v ↦
      ∃ z₁ ≤ Semiterm.valm M v id bf₁, ∃ z₂ ≤ Semiterm.valm M v id bf₂, ∃ z₃ ≤ Semiterm.valm M v id bf₃,
        z₁ = f₁ v ∧ z₂ = f₂ v ∧ z₃ = f₃ v ∧ R z₁ z₂ z₃) :=
    bex_le₀ (DefinableBoundedFunction.term _) <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _)
      <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _)
        <| and (by simpa using hf₁.definable.rel.retraction (n := k + 3) (2 :> (·.succ.succ.succ)))
          <| and (by simpa using hf₂.definable.rel.retraction (n := k + 3) (1 :> (·.succ.succ.succ)))
            <| and (by simpa using hf₃.definable.rel.retraction (n := k + 3) (0 :> (·.succ.succ.succ)))
              <| by simpa using hR.retraction (n := k + 3) ![2, 1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, f₃ v, hbf₃ v, rfl, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, _, _, rfl, rfl, rfl, h⟩; exact h)

lemma bcomp₄ {k} {R : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hR : DefinableRel₄ L Γ R] (hf₁ : DefinableBoundedFunction L Γ f₁) (hf₂ : DefinableBoundedFunction L Γ f₂) (hf₃ : DefinableBoundedFunction L Γ f₃) (hf₄ : DefinableBoundedFunction L Γ f₄) :
    Definable L Γ (fun v ↦ R (f₁ v) (f₂ v) (f₃ v) (f₄ v)) := by
  rcases hf₁.bounded with ⟨bf₁, hbf₁⟩
  rcases hf₂.bounded with ⟨bf₂, hbf₂⟩
  rcases hf₃.bounded with ⟨bf₃, hbf₃⟩
  rcases hf₄.bounded with ⟨bf₄, hbf₄⟩
  have : Definable L Γ (fun v ↦
      ∃ z₁ ≤ Semiterm.valm M v id bf₁, ∃ z₂ ≤ Semiterm.valm M v id bf₂, ∃ z₃ ≤ Semiterm.valm M v id bf₃, ∃ z₄ ≤ Semiterm.valm M v id bf₄,
        z₁ = f₁ v ∧ z₂ = f₂ v ∧ z₃ = f₃ v ∧ z₄ = f₄ v ∧ R z₁ z₂ z₃ z₄) :=
    bex_le₀ (DefinableBoundedFunction.term _) <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _)
      <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _) <| bex_le₀ (DefinableBoundedFunction.term_retraction _ _)
        <| and (by simpa using hf₁.definable.rel.retraction (n := k + 4) (3 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₂.definable.rel.retraction (n := k + 4) (2 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₃.definable.rel.retraction (n := k + 4) (1 :> (·.succ.succ.succ.succ)))
        <| and (by simpa using hf₄.definable.rel.retraction (n := k + 4) (0 :> (·.succ.succ.succ.succ)))
        <| by simpa using hR.retraction (n := k + 4) ![3, 2, 1, 0]
  exact this.of_iff _ (by
    intro v; constructor
    · intro h; exact ⟨f₁ v, hbf₁ v, f₂ v, hbf₂ v, f₃ v, hbf₃ v, f₄ v, hbf₄ v, rfl, rfl, rfl, rfl, h⟩
    · rintro ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, h⟩; exact h)

end Definable

lemma DefinableFunction₁.bcomp {k} {f : M → M} {g : (Fin k → M) → M}
    (hf : DefinableFunction₁ L Γ f) (hg : DefinableBoundedFunction L Γ g) :
    DefinableFunction L Γ (fun v ↦ f (g v)) := by
  have := Definable.bcomp₂ (k := k + 1) (R := Function.Graph f) (DefinableBoundedFunction.var 0) (hg.retraction Fin.succ)
  simpa using this

lemma DefinableFunction₂.bcomp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : DefinableFunction₂ L Γ f) (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) :
    DefinableFunction L Γ (fun v ↦ f (g₁ v) (g₂ v)) := by
  have := Definable.bcomp₃ (k := k + 1) (R := Function.Graph₂ f) (DefinableBoundedFunction.var 0) (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ)
  simpa using this

lemma DefinableFunction₃.bcomp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : DefinableFunction₃ L Γ f) (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) (hg₃ : DefinableBoundedFunction L Γ g₃)  :
    DefinableFunction L Γ (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := by
  have := Definable.bcomp₄ (k := k + 1) (R := Function.Graph₃ f) (DefinableBoundedFunction.var 0) (hg₁.retraction Fin.succ) (hg₂.retraction Fin.succ) (hg₃.retraction Fin.succ)
  simpa using this

lemma DefinableBoundedFunction₁.comp {k} {f : M → M} {g : (Fin k → M) → M} (hf : DefinableBoundedFunction₁ L Γ f) (hg : DefinableBoundedFunction L Γ g) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g v)) := ⟨hf.bounded.comp hg.bounded, hf.definable.bcomp hg⟩

lemma DefinableBoundedFunction₂.comp {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    (hf : DefinableBoundedFunction₂ L Γ f) (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g₁ v) (g₂ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded, hf.definable.bcomp hg₁ hg₂⟩

lemma DefinableBoundedFunction₃.comp {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    (hf : DefinableBoundedFunction₃ L Γ f) (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) (hg₃ : DefinableBoundedFunction L Γ g₃) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := ⟨hf.bounded.comp hg₁.bounded hg₂.bounded hg₃.bounded, hf.definable.bcomp hg₁ hg₂ hg₃⟩

lemma DefinableBoundedFunction.comp₁ {k} {f : M → M} {g : (Fin k → M) → M}
    [hfb : Bounded₁ L f] [hfd : DefinableFunction₁ L Γ f] (hg : DefinableBoundedFunction L Γ g) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g v)) := DefinableBoundedFunction₁.comp ⟨hfb, hfd⟩ hg

lemma DefinableBoundedFunction.comp₂ {k} {f : M → M → M} {g₁ g₂ : (Fin k → M) → M}
    [hfb : Bounded₂ L f] [hfd : DefinableFunction₂ L Γ f] (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g₁ v) (g₂ v)) := DefinableBoundedFunction₂.comp ⟨hfb, hfd⟩ hg₁ hg₂

lemma DefinableBoundedFunction.comp₃ {k} {f : M → M → M → M} {g₁ g₂ g₃ : (Fin k → M) → M}
    [hfb : Bounded₃ L f] [hfd : DefinableFunction₃ L Γ f] (hg₁ : DefinableBoundedFunction L Γ g₁) (hg₂ : DefinableBoundedFunction L Γ g₂) (hg₃ : DefinableBoundedFunction L Γ g₃) :
    DefinableBoundedFunction L Γ (fun v ↦ f (g₁ v) (g₂ v) (g₃ v)) := DefinableBoundedFunction₃.comp ⟨hfb, hfd⟩ hg₁ hg₂ hg₃

section

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26
open Lean.Parser.Tactic (config)

open Definable

lemma DefinablePred.infer {R : M → Prop} [DefinablePred L Γ R] : DefinablePred L Γ R := inferInstance
lemma DefinableRel.infer {R : M → M → Prop} [DefinableRel L Γ R] : DefinableRel L Γ R := inferInstance
lemma DefinableRel₃.infer {R : M → M → M → Prop} [DefinableRel₃ L Γ R] : DefinableRel₃ L Γ R := inferInstance
lemma DefinableFunction₁.infer {f : M → M} [DefinableFunction₁ L Γ f] : DefinableFunction₁ L Γ f := inferInstance
lemma DefinableFunction₂.infer {f : M → M → M} [DefinableFunction₂ L Γ f] : DefinableFunction₂ L Γ f := inferInstance
lemma DefinableFunction₃.infer {f : M → M → M → M} [DefinableFunction₃ L Γ f] : DefinableFunction₃ L Γ f := inferInstance

attribute [aesop (rule_sets := [Definability]) norm]
  sq
  Arith.pow_three
  pow_four
  Definable.const

attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction.comp₁_infer
  DefinableFunction.comp₂_infer
  DefinableFunction.comp₃_infer
  DefinableBoundedFunction.comp₁
  DefinableBoundedFunction.comp₂
  DefinableBoundedFunction.comp₃

attribute [aesop 6 (rule_sets := [Definability]) safe]
  Definable.comp₁_infer
  Definable.comp₂_infer
  Definable.comp₃_infer
  Definable.comp₄_infer
  Definable.const

attribute [aesop 7 (rule_sets := [Definability]) safe]
  Definable.bcomp₁
  Definable.bcomp₂
  Definable.bcomp₃
  Definable.bcomp₄

attribute [aesop 8 (rule_sets := [Definability]) safe]
  Definable.ball_lt
  Definable.ball_le
  Definable.ball_lt'
  Definable.ball_le'
  Definable.bex_lt
  Definable.bex_le

attribute [aesop 9 (rule_sets := [Definability]) safe]
  Definable.ball_lt₀
  Definable.ball_le₀
  Definable.bex_lt₀
  Definable.bex_le₀

attribute [aesop 10 (rule_sets := [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.iff

attribute [aesop 11 (rule_sets := [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.ex

macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)

macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))

example (c : M) : DefinableBoundedFunction₂ L (𝚺, 0) (fun x y : M ↦ c + 2 * x^2) := by definability

example {ex : M → M} [DefinableFunction₁ L 𝚺₀ ex] (c : M) :
    DefinableRel L 𝚷₀ (fun x y : M ↦ ∃ z < x + c * y, (ex x = x ∧ x < y) ↔ ex x = z ∧ ex (x + 1) = 2 * z) := by
  simp [Function.Graph.iff_left ex]
  definability?

example {ex : M → M} [h : DefinableFunction₁ L (𝚫, 1) ex] (c : M) :
    DefinableRel L (𝚺, 1) (fun x y : M ↦ ∃ z, x < y ↔ ex (ex x) = z) := by
  definability?

example {ex : M → M} [h : DefinableFunction₁ L (𝚺, 1) ex] (c : M) :
    DefinableRel L (𝚺, 1) (fun x y : M ↦ ∀ z < ex y, x < y ↔ ex (ex x) = z) := by
  definability?

end

end LO.FirstOrder.Arith
