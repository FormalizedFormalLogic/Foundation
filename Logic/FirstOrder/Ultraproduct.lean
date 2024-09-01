import Logic.FirstOrder.Basic

namespace LO

namespace FirstOrder

section

universe u v

variable {L : Language.{u}} {μ : Type v}
 {I : Type u} (A : I → Type u)
 [(i : I) → Nonempty (A i)] [s : (i : I) → FirstOrder.Structure L (A i)]
 (𝓤 : Ultrafilter I)

namespace Structure

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance UprodStruc : Structure L (Uprod A 𝓤) where
  func := fun _ f v => ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩
  rel  := fun _ r v => {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤

instance [Nonempty I] [(i : I) → Nonempty (A i)] : Nonempty (Uprod A 𝓤) := Nonempty.map (⟨·⟩) inferInstance

@[simp] lemma func_Uprod {k} (f : L.Func k) (v : Fin k → Uprod A 𝓤) :
    Structure.func f v = ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.Rel k) (v : Fin k → Uprod A 𝓤) :
    Structure.rel r v ↔ {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤 := of_eq rfl

end Structure

namespace Semiterm

open Structure

variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)

lemma val_Uprod (t : Semiterm L μ n) :
    t.valm (Uprod A 𝓤) e ε = ⟨fun i ↦ t.val (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i)⟩ :=
  by induction t <;> simp[*, val_func]

end Semiterm

open Structure

variable {A} {𝓤}

namespace Semiformula

variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {i : I} :
    (z.val i :> fun x ↦ (e x).val i) = (fun x ↦ ((z :> e) x).val i) :=
  by simp[Matrix.comp_vecCons (Uprod.val · i), Function.comp]

lemma eval_Uprod {p : Semiformula L μ n} :
    Evalm (Uprod A 𝓤) e ε p ↔ {i | Eval (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p} ∈ 𝓤 := by
  induction p using rec' <;>
    simp [*, Prop.top_eq_true, Prop.bot_eq_false, eval_rel, eval_nrel, Semiterm.val_Uprod]
  case hverum => exact Filter.univ_mem
  case hnrel k r v =>
    exact Ultrafilter.compl_mem_iff_not_mem.symm
  case hand =>
    exact Filter.inter_mem_iff.symm
  case hor p q ihp ihq =>
    exact Ultrafilter.union_mem_iff.symm
  case hall p _ =>
    constructor
    · intro h
      let z : Uprod A 𝓤 := ⟨fun i =>
        Classical.epsilon (fun z => ¬Eval (s i) (z :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p)⟩
      exact Filter.mem_of_superset (h z) (by
        intro i hι a
        have : Eval (s i) (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p :=
          by rw [val_vecCons_val_eq]; exact hι
        by_contra hc
        have : ¬Evalm (A i) (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p :=
          Classical.epsilon_spec (p := fun z => ¬(Eval (s i) (z :> fun x ↦ (e x).val i) _ p)) ⟨a, hc⟩
        contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro i h; simpa [val_vecCons_val_eq] using h (x.val i))
  case hex p _ =>
    constructor
    · rintro ⟨x, hx⟩
      exact Filter.mem_of_superset hx (by intro i h; use x.val i; simpa[val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 := ⟨fun i =>
        Classical.epsilon (fun z => Eval (s i) (z :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p)⟩
      use z
      exact Filter.mem_of_superset h (by
        intro i; rintro ⟨x, hx⟩
        have : Eval (s i) (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p :=
          Classical.epsilon_spec (p := fun z => Eval (s i) (z :> fun x ↦ (e x).val i) _ p) ⟨x, hx⟩
        rw[val_vecCons_val_eq] at this; exact this)

lemma val_Uprod {p : Formula L μ} :
    Evalfm (Uprod A 𝓤) ε p ↔ {i | Evalf (s i) (fun x ↦ (ε x).val i) p} ∈ 𝓤 :=
  by simp[Evalf, eval_Uprod, Matrix.empty_eq]

end Semiformula

lemma models_Uprod [Nonempty I] [(i : I) → Nonempty (A i)] {p : SyntacticFormula L} :
    (Uprod A 𝓤) ⊧ₘ p ↔ {i | (A i) ⊧ₘ p} ∈ 𝓤 := by simp [models_iff₀, Semiformula.val_Uprod, Empty.eq_elim]

variable (A)

def Semiformula.domain (p : SyntacticFormula L) := {i | A i ⊧ₘ p}

end

section

variable {L : Language.{u}} {T : Theory L}

abbrev FinSubtheory (T : Theory L) := {t : Finset (SyntacticFormula L) // ↑t ⊆ T}

variable (A : FinSubtheory T → Type u) [s : (i : FinSubtheory T) → Structure L (A i)]

instance : Nonempty (FinSubtheory T) := ⟨∅, by simp⟩

lemma ultrafilter_exists [(t : FinSubtheory T) → Nonempty (A t)]
    (H : ∀ (i : FinSubtheory T), (A i) ⊧ₘ* (i.val : Theory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Semiformula.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    haveI : DecidableEq (Set (FinSubtheory T)) := fun _ _ => Classical.propDecidable _
    simp[Finset.subset_image_iff, Semiformula.domain]
    intro t ht
    use t; use ht
    intro σ hσ
    exact (H ⟨t, ht⟩).RealizeSet hσ)

lemma compactness_aux :
    Satisfiable T ↔ ∀ i : FinSubtheory T, Satisfiable (i.val : Theory L) := by
  constructor
  · rintro h ⟨t, ht⟩; exact Semantics.Satisfiable.of_subset h ht
  · intro h
    have : ∀ i : FinSubtheory T, ∃ (M : Type u) (_ : Nonempty M) (_ : Structure L M), M ⊧ₘ* (i.val : Theory L) :=
      by intro i; exact satisfiable_iff.mp (h i)
    choose A si s hA using this
    have : ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Semiformula.domain A) T ⊆ 𝓤.sets := ultrafilter_exists A hA
    rcases this with ⟨𝓤, h𝓤⟩
    have : Structure.Uprod A 𝓤 ⊧ₘ* T := ⟨by intro σ hσ; exact models_Uprod.mpr (h𝓤 $ Set.mem_image_of_mem (Semiformula.domain A) hσ)⟩
    exact satisfiable_intro (Structure.Uprod A 𝓤) this

theorem compact :
    Satisfiable T ↔ ∀ u : Finset (SyntacticFormula L), ↑u ⊆ T → Satisfiable (u : Theory L) := by
  rw[compactness_aux]; simp

instance : Compact (SmallStruc L) := ⟨compact⟩

end

end FirstOrder

end LO
