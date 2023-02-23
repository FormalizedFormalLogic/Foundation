import Logic.Predicate.FirstOrder.Calculus

open FirstOrder Derivation

def d := derive? 4 32 (L := Language.relational (fun _ => ℕ)) 
  (∀' ( SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0] ⋎
        SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 1 ![#0]) ⟶
   ∀' ( SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 1 ![#0] ⋎
        SubFormula.rel! (Language.relational (fun _ => ℕ)) 1 0 ![#0]))