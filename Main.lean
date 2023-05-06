import «Logic»

open FirstOrder

def d : FirstOrder.Derivation₁ (L := (Language.relational (fun _ => ℕ)))
    “(([Language.toRelational 0]() → [Language.toRelational 1]()) → [Language.toRelational 0]()) → [Language.toRelational 0]()” := by proveDerivation₁

unsafe def main : IO Unit :=
  IO.println s!"{repr d}"
