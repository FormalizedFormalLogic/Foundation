#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let arrows = json("./propositional.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Propositional Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph PropositionalLogicZoo {
    rankdir = BT;
    node [
      margin=0.1
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.75
    ];
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝐂𝐥": $Logic("Cl")$,
      "𝗜𝐧𝐭": $Logic("Int")$,
      "𝐊𝐂": $Logic("KC")$,
      "𝐊𝐏": $Logic("KP")$,
      "𝐋𝐂": $Logic("LC")$,
    ),
    width: 70pt,
  )
]
