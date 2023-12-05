import Logic.FirstOrder.Basic.Eq

namespace LO

namespace FirstOrder

section

variable {L : Language.{u}} {μ : Type v}
 {I : Type u} (A : I → Type u) [(ι : I) → Inhabited (A ι)] [s : (ι : I) → FirstOrder.Structure L (A ι)] (𝓤 : Ultrafilter I)

namespace Structure

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance UprodStruc : Structure.{u,u} L (Uprod A 𝓤) where
  func := fun _ f v => ⟨fun ι => (s ι).func f (fun i => (v i).val ι)⟩
  rel  := fun _ r v => {ι | (s ι).rel r (fun i => (v i).val ι)} ∈ 𝓤

instance [Inhabited I] [(ι : I) → Inhabited (A ι)] : Inhabited (Uprod A 𝓤) := ⟨⟨default⟩⟩

@[simp] lemma func_Uprod {k} (f : L.func k) (v : Fin k → Uprod A 𝓤) :
    Structure.func f v = ⟨fun ι => (s ι).func f (fun i => (v i).val ι)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.rel k) (v : Fin k → Uprod A 𝓤) :
    Structure.rel r v ↔ {ι | (s ι).rel r (fun i => (v i).val ι)} ∈ 𝓤 := of_eq rfl

end Structure

namespace Subterm

open Structure

variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)

lemma val_Uprod (t : Subterm L μ n) :
    t.val! (Uprod A 𝓤) e ε = ⟨fun ι => t.val (s ι) (fun i => (e i).val ι) (fun i => (ε i).val ι)⟩ :=
  by induction t <;> simp[*, val_func]

end Subterm

open Structure

variable {A} {𝓤}

namespace Subformula

variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {ι : I} :
    (z.val ι :> fun i => (e i).val ι) = (fun i => ((z :> e) i).val ι) :=
  by simp[Matrix.comp_vecCons (Uprod.val · ι), Function.comp]

lemma eval_Uprod {p : Subformula L μ n} :
    Eval! (Uprod A 𝓤) e ε p ↔ {ι | Eval (s ι) (fun i => (e i).val ι) (fun i => (ε i).val ι) p} ∈ 𝓤 := by
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
      let z : Uprod A 𝓤 := ⟨fun ι =>
        Classical.epsilon (fun z => ¬Eval (s ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      exact Filter.mem_of_superset (h z) (by
        intro ι hι a
        have : Eval (s ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          by rw [val_vecCons_val_eq]; exact hι
        by_contra hc
        have : ¬Eval! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => ¬(Eval (s ι) (z :> fun i => (e i).val ι) _ p)) ⟨a, hc⟩
        contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro ι h; simpa [val_vecCons_val_eq] using h (x.val ι))
  case hex p _ =>
    constructor
    · rintro ⟨x, hx⟩
      exact Filter.mem_of_superset hx (by intro ι h; use x.val ι; simpa[val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 := ⟨fun ι =>
        Classical.epsilon (fun z => Eval (s ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      use z
      exact Filter.mem_of_superset h (by
        intro ι; rintro ⟨x, hx⟩
        have : Eval (s ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => Eval (s ι) (z :> fun i => (e i).val ι) _ p) ⟨x, hx⟩
        rw[val_vecCons_val_eq] at this; exact this)

lemma val_Uprod {p : Formula L μ} :
    Val! (Uprod A 𝓤) ε p ↔ {ι | Val (s ι) (fun i => (ε i).val ι) p} ∈ 𝓤 :=
  by simp[Val, eval_Uprod, Matrix.empty_eq]

end Subformula

lemma models_Uprod {σ : Sentence L} :
    (Uprod A 𝓤) ⊧ σ ↔ {ι | Semantics.models (s ι) σ} ∈ 𝓤 :=
  by simp[models_def, Subformula.val_Uprod, Empty.eq_elim]

variable (A)

def Subformula.domain (σ : Sentence L) := {ι | (A ι) ⊧ σ}

end

section

variable {L : Language.{u}} {T : Theory L}

abbrev FinSubtheory (T : Theory L) := {t : Finset (Sentence L) // ↑t ⊆ T}

variable (A : FinSubtheory T → Type u) [s : (ι : FinSubtheory T) → Structure L (A ι)]

instance : Inhabited (FinSubtheory T) := ⟨∅, by simp⟩


lemma ultrafilter_exists (H : ∀ (ι : FinSubtheory T), (A ι) ⊧* (ι.val : Theory L)) :
    ∃ 𝓤 : Ultrafilter (FinSubtheory T), Set.image (Subformula.domain A) T ⊆ 𝓤.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    haveI : DecidableEq (Set (FinSubtheory T)) := fun _ _ => Classical.propDecidable _
    simp[Finset.subset_image_iff, Subformula.domain]
    intro t ht
    use t; use ht
    intro σ hσ
    exact H ⟨t, ht⟩ hσ)

lemma compactnessAux :
    Semantics.Satisfiableₛ T ↔ ∀ ι : FinSubtheory T, Semantics.Satisfiableₛ (ι.val : Theory L) := by
  constructor
  · rintro h ⟨t, ht⟩; exact Semantics.satisfiableₛ_of_subset h ht
  · intro h
    have : ∀ ι : FinSubtheory T, ∃ (M : Type u) (_ : Inhabited M) (_ : Structure L M), M ⊧* (ι.val : Theory L) :=
      by intro ι; exact satisfiableₛ_iff.mp (h ι)
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
