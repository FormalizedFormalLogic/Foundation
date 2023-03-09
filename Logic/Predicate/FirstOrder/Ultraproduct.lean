import Logic.Predicate.FirstOrder.Semantics
import Mathlib.Order.Filter.Ultrafilter

universe u v

section

variable {L : Language.{u}} {μ : Type v} {n : ℕ} {I : Type uᵢ} [Inhabited I]
  (A : I → Type w) [(ι : I) → Inhabited (A ι)] [s : (ι : I) → Structure₁ L (A ι)] (𝓤 : Ultrafilter I)

namespace Structure₁

structure Uprod (𝓤 : Ultrafilter I) where
  val : (i : I) → A i

instance : Structure₁ L (Uprod A 𝓤) where
  func := fun f v => ⟨fun ι => func f (fun i => (v i).val ι)⟩
  rel  := fun r v => {ι | rel r (fun i => (v i).val ι)} ∈ 𝓤

@[simp] lemma func_Uprod {k} (f : L.func k) (v : Fin k → Uprod A 𝓤) :
    func f v = ⟨fun ι => func f (fun i => (v i).val ι)⟩ := rfl

@[simp] lemma rel_Uprod {k} (r : L.rel k) (v : Fin k → Uprod A 𝓤) :
    rel r v ↔ {ι | rel r (fun i => (v i).val ι)} ∈ 𝓤 := of_eq rfl

end Structure₁

namespace SubTerm
open Structure₁
variable (e : Fin n → Uprod A 𝓤) (ε : μ → Uprod A 𝓤)

lemma val_Uprod (t : SubTerm L μ n) :
    t.val! (Uprod A 𝓤) e ε = ⟨fun ι => t.val! (A ι) (fun i => (e i).val ι) (fun i => (ε i).val ι)⟩ :=
  by induction t <;> simp[*, val_func]

end SubTerm

namespace FirstOrder
open Structure₁
variable {A} {𝓤}

namespace SubFormula
variable {e : Fin n → Uprod A 𝓤} {ε : μ → Uprod A 𝓤}

lemma val_vecCons_val_eq {z : Uprod A 𝓤} {ι : I} :
    (z.val ι :> fun i => (e i).val ι) = (fun i => ((z :> e) i).val ι) :=
  by simp[Matrix.comp_vecCons (Uprod.val · ι), Function.comp]

lemma subVal_Uprod {p : SubFormula L μ n} :
    SubVal! (Uprod A 𝓤) e ε p ↔ {ι | SubVal! (A ι) (fun i => (e i).val ι) (fun i => (ε i).val ι) p} ∈ 𝓤 := by
  induction p using rec' <;>
  simp[*, Prop.top_eq_true, Prop.bot_eq_false, subVal_rel, subVal_nrel, SubTerm.val_Uprod]
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
        Classical.epsilon (fun z => ¬SubVal! (A ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      exact Filter.mem_of_superset (h z) (by 
        intro ι hι a
        have : SubVal! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          by rw [val_vecCons_val_eq]; exact hι
        by_contra hc
        have : ¬SubVal! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => ¬(SubVal! (A ι) (z :> fun i => (e i).val ι) _ p)) ⟨a, hc⟩
        contradiction)
    · intro h x
      exact Filter.mem_of_superset h (by intro ι h; simpa [val_vecCons_val_eq] using h (x.val ι))
  case hex p _ =>
    constructor
    · rintro ⟨x, hx⟩
      exact Filter.mem_of_superset hx (by intro ι h; use x.val ι; simpa[val_vecCons_val_eq] using h)
    · intro h
      let z : Uprod A 𝓤 := ⟨fun ι =>
        Classical.epsilon (fun z => SubVal! (A ι) (z :> fun i => (e i).val ι) (fun i => (ε i).val ι) p)⟩
      use z
      exact Filter.mem_of_superset h (by
        intro ι; rintro ⟨x, hx⟩
        have : SubVal! (A ι) (z.val ι :> fun i => (e i).val ι) (fun i => (ε i).val ι) p :=
          Classical.epsilon_spec (p := fun z => SubVal! (A ι) (z :> fun i => (e i).val ι) _ p) ⟨x, hx⟩
        rw[val_vecCons_val_eq] at this; exact this)

lemma val_Uprod {p : Formula L μ} :
    Val! (Uprod A 𝓤) ε p ↔ {ι | Val! (A ι) (fun i => (ε i).val ι) p} ∈ 𝓤 :=
  by simp[Val!, Val, subVal_Uprod, Matrix.empty_eq]

end SubFormula

lemma model_Uprod {σ : Sentence L} :
    Uprod A 𝓤 ⊧₁ σ ↔ {ι | A ι ⊧₁ σ} ∈ 𝓤 :=
  by simp[models_sentence_def, SubFormula.val_Uprod, Empty.eq_elim]

variable (A)

def SubFormula.domain (σ : Sentence L) := {ι | A ι ⊧₁ σ}

end FirstOrder

end

section

namespace FirstOrder

variable {L : Language.{u}} {T : CTheory L}

abbrev FinTheory (T : CTheory L) := {t : Finset (Sentence L) // ↑t ⊆ T}

variable (A : FinTheory T → Type u) [(ι : FinTheory T) → Structure₁ L (A ι)]

instance : Inhabited (FinTheory T) := ⟨∅, by simp⟩

attribute [instance] Classical.propDecidable in
lemma ultrafilter_exists (H : ∀ (σ : Sentence L) (ι : FinTheory T), σ ∈ ι.val → A ι ⊧₁ σ ) :
    ∃ U : Ultrafilter (FinTheory T), Set.image (SubFormula.domain A) T ⊆ U.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty _ (by
    simp[Finset.subset_image_iff, SubFormula.domain]
    rintro t ht
    use t; use ht
    intro σ hσ
    exact H σ _ hσ)

end FirstOrder

end

