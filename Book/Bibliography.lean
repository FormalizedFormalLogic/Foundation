import VersoManual

open Verso.Genre.Manual

def CZ97 : ArXiv where
  title := inlines!"Modal Logic"
  authors := #[
    inlines!"A. Chagrov",
    inlines!"M. Zakharyaschev"
  ]
  year := 1997
  id := "...insert arXiv id here..."

def Boo94 : ArXiv where
  title := inlines!"The Logic of Provability"
  authors := #[inlines!"G. Boolos"]
  year := 1994
  id := "...insert arXiv id here..."

def CH07 : ArXiv where
  title := inlines!"A New Introduction to Modal Logic"
  authors := #[
    inlines!"G. E. Hudges",
    inlines!"M. J. Cresswell",
  ]
  year := 2007
  id := "...insert arXiv id here..."

def Seg71 : Thesis where
  title := inlines!"An Essay in Classical Modal Logic"
  author := inlines!"K. Segerberg"
  year := 1971
  degree := inlines!"Ph.D"
  university := inlines!"Stanford University"

def Kop23 : ArXiv where
  title := inlines!"The Finite Model Property of Some Non-normal Modal Logics with the Transitivity Axiom"
  authors := #[
    inlines!"K. Kopnev",
  ]
  year := 2023
  id := "2305.08605"

def Lew74 : Article where
  title := inlines!"Intensional Logics without Iterative Axioms"
  authors := #[
    inlines!"D. Lewis",
  ]
  journal := inlines!"Journal of Philosophical Logic"
  year := 1974
  month := some inlines!"October"
  volume := inlines!"3"
  number := inlines!"4"

def KO21 : Article where
  title := inlines!"Modal completeness of sublogics of the interpretability logic IL"
  authors := #[
    inlines!"Taishi. Kurahashi",
    inlines!"Yuya. Okawa",
  ]
  journal := inlines!"Mathematical Logic Quarterly"
  year := 2021
  month := some inlines!"May"
  volume := inlines!"67"
  number := inlines!"2"

-- TODO: `Book`
def Vis88 : ArXiv where
  title := inlines!"Preliminary Notes on Interpretability Logic"
  authors := #[
    inlines!"Albert. Visser",
  ]
  year := 1988
  id := "...insert arXiv id here..."

def Rov20 : Thesis where
  title := inlines!"Interpretability Logics and Generalized Veltman Semantics in Agda"
  author := inlines!"Jan Mas. Rovira"
  year := 2020
  degree := inlines!"Master"
  university := inlines!"The University of Amsterdam"

-- TODO: `incollection`
def DV90 : ArXiv where
  title := inlines!"Provability Logics for Relative Interpretability"
  authors := #[
    inlines!"Dick. de Jongh",
    inlines!"Frank. Veltman",
  ]
  year := 1990
  id := "...insert arXiv id here..."

def Joo04 : Thesis where
  title := inlines!"Interpretability Formalized"
  author := inlines!"Joost Johannes. Joosten"
  year := 2004
  degree := inlines!"Ph.D"
  university := inlines!"Utrecht University"

-- TODO: `Book`
def Vis97 : ArXiv where
  title := inlines!"An Overview of Interpretability Logic"
  authors := #[
    inlines!"Albert. Visser",
  ]
  year := 1997
  id := "...insert arXiv id here..."

-- TODO: `incollection`
def JD98 : ArXiv where
  title := inlines!"The Logic of Provability"
  authors := #[
    inlines!"Giorgi. Japaridze",
    inlines!"Dick. de Jongh",
  ]
  year := 1998
  id := "...insert arXiv id here..."

-- TODO: `incollection`
def JRMV24 : ArXiv where
  title := inlines!"An Overview of Verbrugge Semantics, a.k.a. Generalised Veltman Semantics"
  authors := #[
    inlines!"Joost J. Joosten",
    inlines!"Jan Mas. Rovira",
    inlines!"Luka. Mikec",
    inlines!"Mladen. Vuković",
  ]
  year := 2024
  id := "...insert arXiv id here..."

-- TODO: `incollection`
def Werner97 : ArXiv where
  title := inlines!"Sets in types, types in sets"
  authors := #[
    inlines!"Benjamin. Werner",
  ]
  year := 1997
  id := "none"
