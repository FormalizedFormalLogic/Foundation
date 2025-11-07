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
