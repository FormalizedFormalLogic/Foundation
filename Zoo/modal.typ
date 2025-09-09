#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let box = $square$
#let dia = $diamond$

#let arrows = json("./modal.json").map(((from, to, type)) => {
  if type == "ssub" {
    return strfmt("\"{}\" -> \"{}\"", from, to)
  } else if type == "sub" {
    return strfmt("\"{}\" -> \"{}\" [style=dashed] ", from, to)
  } else if type == "eq" {
    return (
      strfmt("\"{}\" -> \"{}\" [color=\"black:white:black\" arrowhead=\"none\"] ", from, to),
      strfmt("{{rank = same; \"{}\"; \"{}\";}}", from, to),
    ).join("\n")
  } else if type == "sorry" {
    return strfmt("\"{}\" -> \"{}\" [color=red; style=dashed] ", from, to)
  }
})

#figure(caption: [Modal Logic Zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph ModalLogicsZoo {
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

    {rank = same; \"LO.Modal.KD\"; \"LO.Modal.KB\"; \"LO.Modal.K4\"; \"LO.Modal.K5\";}
    {rank = same; \"LO.Modal.KT\"; \"LO.Modal.KDB\"; \"LO.Modal.KD4\"; \"LO.Modal.KD5\"; \"LO.Modal.K45\";}
    {rank = same; \"LO.Modal.KTB\"; \"LO.Modal.S4\"; \"LO.Modal.KD45\"; \"LO.Modal.KB4\";}
    {rank = same; \"LO.Modal.GL\"; \"LO.Modal.Grz\";}
    {rank = same; \"LO.Modal.Triv\"; \"LO.Modal.Ver\";}
  "
        + arrows.join("\n")
        + "}",
    ),
    labels: (
      "𝐄": $Logic("E")$,
      "𝐄𝐂": $Logic("EC")$,
      "𝐄𝐂𝐍": $Logic("ECN")$,
      "𝐄𝐊": $Logic("EK")$,
      "𝐄𝐌": $Logic("EM")$,
      "𝐄𝐌𝐂": $Logic("EMC")$,
      "𝐄𝐌𝐂𝐍": $Logic("EMCN")$,
      "𝐄𝐌𝐍": $Logic("EMN")$,
      "𝐄𝐍": $Logic("EN")$,
      "LO.Modal.Dum": $Logic("Dum")$,
      "LO.Modal.DumPoint2": $Logic("Dum.2")$,
      "LO.Modal.DumPoint3": $Logic("Dum.3")$,
      "LO.Modal.D": $Logic("D")$,
      "LO.Modal.Empty": $emptyset$,
      "LO.Modal.GL": $Logic("GL")$,
      "LO.Modal.GLPoint2": $Logic("GL.2")$,
      "LO.Modal.GLPoint3": $Logic("GL.3")$,
      "LO.Modal.GLPoint3OplusBoxBot 0": $Logic("GL.3") plus.circle bot$,
      "LO.Modal.GLPoint3OplusBoxBot 1": $Logic("GL.3") plus.circle box bot$,
      "LO.Modal.GLPoint3OplusBoxBot 2": $Logic("GL.3") plus.circle box^2 bot$,
      "LO.Modal.Grz": $Logic("Grz")$,
      "LO.Modal.GrzPoint2": $Logic("Grz.2")$,
      "LO.Modal.GrzPoint2M": $Logic("Grz.2M")$,
      "LO.Modal.GrzPoint3": $Logic("Grz.3")$,
      "LO.Modal.K": $Logic("K")$,
      "LO.Modal.K4": $Logic("K4")$,
      "LO.Modal.K45": $Logic("K45")$,
      "LO.Modal.K4Hen": $Logic("K4Hen")$,
      "LO.Modal.K4Henkin": $Logic("K4") + Rule("Henkin")$,
      "LO.Modal.K4Loeb": $Logic("K4") + Rule("Löb")$,
      "LO.Modal.K4McK": $Logic("K4McK")$,
      "LO.Modal.K4Point2": $Logic("K4.2")$,
      "LO.Modal.K4Point2Z": $Logic("K4.2Z")$,
      "LO.Modal.K4Point3": $Logic("K4.3")$,
      "LO.Modal.K4Point3Z": $Logic("K4.3Z")$,
      "LO.Modal.K4Z": $Logic("K4Z")$,
      "LO.Modal.K5": $Logic("K5")$,
      "LO.Modal.KB": $Logic("KB")$,
      "LO.Modal.KB4": $Logic("KB4")$,
      "LO.Modal.KB5": $Logic("KB5")$,
      "LO.Modal.KD": $Logic("KD")$,
      "LO.Modal.KD4": $Logic("KD4")$,
      "LO.Modal.KD45": $Logic("KD45")$,
      "LO.Modal.KD5": $Logic("KD5")$,
      "LO.Modal.KDB": $Logic("KDB")$,
      "LO.Modal.KHen": $Logic("KHen")$,
      "LO.Modal.KMcK": $Logic("KMcK")$,
      "LO.Modal.KP": $Logic("KP")$,
      "LO.Modal.KT": $Logic("KT")$,
      "LO.Modal.KT4B": $Logic("KT4B")$,
      "LO.Modal.KTB": $Logic("KTB")$,
      "LO.Modal.KTc": $Logic("KTc")$,
      "LO.Modal.KTMk": $Logic("KTMk")$,
      "LO.Modal.N": $Logic("N")$,
      "LO.Modal.S": $Logic("S")$,
      "LO.Modal.S4": $Logic("S4")$,
      "LO.Modal.S4H": $Logic("S4H")$,
      "LO.Modal.S4McK": $Logic("S4McK")$,
      "LO.Modal.S4Point2": $Logic("S4.2")$,
      "LO.Modal.S4Point2McK": $Logic("S4.2McK")$,
      "LO.Modal.S4Point2Point4M": $Logic("S4.2.4M")$,
      "LO.Modal.S4Point3": $Logic("S4.3")$,
      "LO.Modal.S4Point3McK": $Logic("S4.3McK")$,
      "LO.Modal.S4Point4": $Logic("S4.4")$,
      "LO.Modal.S4Point4McK": $Logic("S4.4McK")$,
      "LO.Modal.S4Point9": $Logic("S4.4") + Axiom("M18")$,
      "LO.Modal.S5": $Logic("S5")$,
      "LO.Modal.S5Grz": $Logic("S5Grz")$,
      "LO.Modal.Triv": $Logic("Triv")$,
      "LO.Modal.Univ": $bot$,
      "LO.Modal.Ver": $Logic("Ver")$,
      "𝗣𝗔.ProvabilityLogic": [Provability logic of $Theory("PA")$]
    ),
    width: 980pt,
  )
]
