import Aesop

declare_aesop_rule_sets [Subformula]

open Lean.Parser.Tactic (config)

macro "subformula" : attr =>
  `(attr|aesop safe forward 10 (rule_sets := [Subformula]) safe)

macro "add_subformula_rules" e:Aesop.rule_expr : command =>
  `(command| add_aesop_rules (rule_sets := [Subformula]) $e)

macro "subformula" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [Subformula]))

macro "subformula?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [Subformula]))
