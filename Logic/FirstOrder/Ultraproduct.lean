import Logic.FirstOrder.Basic

namespace LO

namespace FirstOrder

section

variable {L : Language.{u}} {μ : Type v}
 {I : Type u} (A : I → Type u)
 [(i : I) → Inhabited (A i)] [s : (i : I) → FirstOrder.Structure L (A i)]
 (𝓤 : Ultrafilter I)

namespace Structure

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance UprodStruc : Structure.{u,u} L (Uprod A 𝓤) where
  func := fun _ f v => ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩
  rel  := fun _ r v => {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤

instance [Inhabited I] [(i : I) → Inhabited (A i)] : Inhabited (Uprod A 𝓤) := ⟨⟨default⟩⟩

@[simp] lemma func_Uprod {k} (f : L.Func k) (v : Fin k → Uprod A 𝓤) :
    Structure.func f v = ⟨fun i ↦ (s i).func f (fun x ↦ (v x).val i)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.Rel k) (v : Fin k → Uprod A 𝓤) :
    Structure.rel r v ↔ {i | (s i).rel r (fun x ↦ (v x).val i)} ∈ 𝓤 := of_eq rfl

end Structure

namespace Subterm

open Structure

variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)

lemma val_Uprod (t : Subterm L μ n) :
    t.val! (Uprod A 𝓤) e ε = ⟨fun i ↦ t.val (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i)⟩ :=
  by induction t <;> simp[*, val_func]

end Subterm

open Structure

variable {A} {𝓤}

namespace Subformula

variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {i : I} :
    (z.val i :> fun x ↦ (e x).val i) = (fun x ↦ ((z :> e) x).val i) :=
  by simp[Matrix.comp_vecCons (Uprod.val · i), Function.comp]

lemma eval_Uprod {p : Subformula L μ n} :
    Eval! (Uprod A 𝓤) e ε p ↔ {i | Eval (s i) (fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p} ∈ 𝓤 := by
  induction p using rec' <;>
  simp[*, Prop.top_eq_true, Prop.bot_eq_false, eval_rel, eval_nrel, Subterm.val_Uprod]
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
        have : ¬Eval! (A i) (z.val i :> fun x ↦ (e x).val i) (fun x ↦ (ε x).val i) p :=
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
    Val! (Uprod A 𝓤) ε p ↔ {i | Val (s i) (fun x ↦ (ε x).val i) p} ∈ 𝓤 :=
  by simp[Val, eval_Uprod, Matrix.empty_eq]

end Subformula

lemma models_Uprod {σ : Sentence L} :
    (Uprod A 𝓤) ⊧ σ ↔ {i | Semantics.models (s i) σ} ∈ 𝓤 :=
  by simp[models_def, Subformula.val_Uprod, Empty.eq_elim]

variable (A)

def Subformula.domain (σ : Sentence L) := {i | (A i) ⊧ σ}

end

section

variable {L : Language.{u}} {T : Theory L}

abbrev FinSubtheory (T : Theory L) := {t : Finset (Sentence L) // ↑t ⊆ T}

variable (A : FinSubtheory T → Type u) [s : (i : FinSubtheory T) → Structure L (A i)]

instance : Inhabited (FinSubtheory T) := ⟨∅, by simp⟩

lemma ultrafilter_exists (H : ∀ (i : FinSubtheory T), (A i) ⊧* (i.val : Theory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Subformula.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    haveI : DecidableEq (Set (FinSubtheory T)) := fun _ _ => Classical.propDecidable _
    simp[Finset.subset_image_iff, Subformula.domain]
    intro t ht
    use t; use ht
    intro σ hσ
    exact H ⟨t, ht⟩ hσ)

lemma compactnessAux :
    Semantics.Satisfiableₛ T ↔ ∀ i : FinSubtheory T, Semantics.Satisfiableₛ (i.val : Theory L) := by
  constructor
  · rintro h ⟨t, ht⟩; exact Semantics.Satisfiableₛ.of_subset h ht
  · intro h
    have : ∀ i : FinSubtheory T, ∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M), M ⊧* (i.val : Theory L) :=
      by intro i; exact satisfiableₛ_iff.mp (h i)
    choose A si s hA using this
    have : ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Subformula.domain A) T ⊆ 𝓤.sets := ultrafilter_exists A hA
    rcases this with ⟨𝓤, h𝓤⟩
    have : Structure.Uprod A 𝓤 ⊧* T := by intro σ hσ; exact models_Uprod.mpr (h𝓤 $ Set.mem_image_of_mem (Subformula.domain A) hσ)
    exact satisfiableₛ_intro (Structure.Uprod A 𝓤) this

theorem compactness :
    Semantics.Satisfiableₛ T ↔ ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.Satisfiableₛ (T' : Theory L) := by
  rw[compactnessAux]; simp

instance : Compact (Sentence L) := ⟨compactness⟩

end

end FirstOrder

end LO
