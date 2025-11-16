#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let omitLabels = ()

#let arrows = json("./InterpretabilityLogic.json").map(((from, to, type)) => {
  if omitLabels.contains(from) == false and omitLabels.contains(from) == false {
    if type == "ssub" {
      return strfmt("\"{}\" -> \"{}\"", to, from)
    } else if type == "sub" {
      return strfmt("\"{}\" -> \"{}\" [style=dashed] ", to, from)
    } else if type == "eq" {
      return (
        strfmt("\"{}\" -> \"{}\" [color=\"black:white:black\" arrowhead=\"none\"] ", to, from),
        strfmt("{{rank = same; \"{}\"; \"{}\";}}", to, from),
      ).join("\n")
    } else if type == "sorry" {
      return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", to, from)
    }
  }
})

#let LogicILMinus = $Logic("IL"^-)$
#let LogicIL = $Logic("IL")$
#let LogicCL = $Logic("CL")$
#let AxiomJ1 = $Axiom("J1")$
#let AxiomJ2 = $Axiom("J2")$
#let AxiomJ2Plus = $Axiom("J2"^+)$
#let AxiomJ4 = $Axiom("J4")$
#let AxiomJ4Plus = $Axiom("J4"^+)$
#let AxiomJ5 = $Axiom("J5")$
#let AxiomF = $Axiom("F")$
#let AxiomM = $Axiom("M")$
#let AxiomM0 = $Axiom("M"_0)$
#let AxiomW = $Axiom("W")$
#let AxiomP = $Axiom("P")$
#let AxiomP0 = $Axiom("P"_0)$
#let AxiomR = $Axiom("R")$
#let AxiomKW1Zero = $Axiom("KW1"^0)$
#let AxiomKW2 = $Axiom("KW2")$
#let AxiomRstar = $Axiom("R"^*)$
#let AxiomWstar = $Axiom("W"^*)$

#figure(caption: [Interpretability Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalTheorysZoo {
    rankdir = TB;

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
      "LO.InterpretabilityLogic.CL": $LogicCL$,
      "LO.InterpretabilityLogic.IL_F": $LogicIL(AxiomF)$,
      "LO.InterpretabilityLogic.IL_KW1Zero": $LogicIL(AxiomKW1Zero)$,
      "LO.InterpretabilityLogic.IL_KW2": $LogicIL(AxiomKW2)$,
      "LO.InterpretabilityLogic.IL_M": $LogicIL(AxiomM)$,
      "LO.InterpretabilityLogic.IL_M₀_W": $LogicIL(AxiomM0, AxiomW)$,
      "LO.InterpretabilityLogic.IL_M₀": $LogicIL(AxiomM0)$,
      "LO.InterpretabilityLogic.IL_P": $LogicIL(AxiomP)$,
      "LO.InterpretabilityLogic.IL_P₀": $LogicIL(AxiomP0)$,
      "LO.InterpretabilityLogic.IL_R_W": $LogicIL(AxiomR, AxiomW)$,
      "LO.InterpretabilityLogic.IL_R": $LogicIL(AxiomR)$,
      "LO.InterpretabilityLogic.IL_Rstar": $LogicIL(AxiomRstar)$,
      "LO.InterpretabilityLogic.IL_W": $LogicIL(AxiomW)$,
      "LO.InterpretabilityLogic.IL_Wstar": $LogicIL(AxiomWstar)$,
      "LO.InterpretabilityLogic.IL": $LogicIL$,
      "LO.InterpretabilityLogic.ILMinus_J1_J2_J5": $LogicILMinus(AxiomJ1, AxiomJ2, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J2": $LogicILMinus(AxiomJ1, AxiomJ2)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J4Plus_J5": $LogicILMinus(AxiomJ1, AxiomJ4Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J4Plus": $LogicILMinus(AxiomJ1, AxiomJ4Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J1_J5": $LogicILMinus(AxiomJ1, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J1": $LogicILMinus(AxiomJ1)$,
      "LO.InterpretabilityLogic.ILMinus_J2Plus_J5": $LogicILMinus(AxiomJ2Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J2Plus": $LogicILMinus(AxiomJ2Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J4": $LogicILMinus(AxiomJ4)$,
      "LO.InterpretabilityLogic.ILMinus_J4Plus_J5": $LogicILMinus(AxiomJ4Plus, AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus_J4Plus": $LogicILMinus(AxiomJ4Plus)$,
      "LO.InterpretabilityLogic.ILMinus_J5": $LogicILMinus(AxiomJ5)$,
      "LO.InterpretabilityLogic.ILMinus": $LogicILMinus$,
    ),
    width: 320pt,
  )
]
