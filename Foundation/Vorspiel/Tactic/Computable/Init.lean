module

public meta import Aesop
import Aesop.Frontend.Command

/-!
# The rule set of the `computable` tactic

Aesop requires a rule set to be declared in a module of its own, imported by the modules that
populate it.
-/

declare_aesop_rule_sets [Computable]
