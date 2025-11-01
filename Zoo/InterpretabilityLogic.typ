#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let omitLabels = ()

#let arrows = json("./InterpretabilityLogic.json").map(((from, to, type)) => {
  if omitLabels.contains(from) == false and omitLabels.contains(from) == false {
    if type == "ssub" {
      return strfmt("\"{}\" -> \"{}\"", from, to)
    } else if type == "sub" {
      return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
    } else if type == "sorry" {
      return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
    }
  }
})

#let ILMinus = $Logic("IL"^-)$
#let AxiomJ1 = $Axiom("J1")$
#let AxiomJ2 = $Axiom("J2")$
#let AxiomJ2Plus = $Axiom("J2"^+)$
#let AxiomJ4 = $Axiom("J4")$
#let AxiomJ4Plus = $Axiom("J4"^+)$
#let AxiomJ5 = $Axiom("J5")$


#figure(caption: [Interpretability Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalTheorysZoo {
    rankdir = LR;

    node [
      shape=none
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.5
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "LO.InterpretabilityLogic.ILMinus_J1_J2_J5": $ILMinus (AxiomJ1, AxiomJ2, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J2": $ILMinus (AxiomJ1, AxiomJ2)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J4Plus_J5": $ILMinus (AxiomJ1, AxiomJ4Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J4Plus": $ILMinus (AxiomJ1, AxiomJ4Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J5": $ILMinus (AxiomJ1, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1": $ILMinus (AxiomJ1)$,
      "LO.InterpretabilityLogic.ILMinus_J2Plus_J5": $ILMinus (AxiomJ2Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J2Plus": $ILMinus (AxiomJ2Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J4": $ILMinus (AxiomJ4)$,
      "LO.InterpretabilityLogic.ILMinus_J4Plus_J5": $ILMinus (AxiomJ4Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J4Plus": $ILMinus (AxiomJ4Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J5": $ILMinus (AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus": $ILMinus$,
    ),
    width: 240pt,
  )
]
