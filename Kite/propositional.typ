
#import "@preview/diagraph:0.3.1": *
#import "@preview/oxifmt:0.2.1": strfmt

#set page(width: auto, height: auto, margin: 24pt)

#let Logic(L) = $upright(bold(#L))$
#let Axiom(A) = $upright(sans(#A))$

#let arrows = json("./propositional.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Kite of Propositional Logics], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalLogicsKite {
    rankdir = BT;
    node [
      shape=none
      margin=0.1
      width=0
      height=0
    ]
    edge [
      style = solid
      arrowhead = vee
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝐂𝐥": $Logic("Cl")$,
      "𝐈𝐧𝐭": $Logic("Int")$,
      "𝐊𝐂": $Logic("KC")$,
      "𝐊𝐏": $Logic("KP")$,
      "𝐋𝐂": $Logic("LC")$,
    ),
    width: 90pt,
  )
]
