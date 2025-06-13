import Book.Main

open Verso.Genre.Manual

def main := manualMain (%doc Book.Main) (config := config)
where
  config := Config.addKaTeX {
    extraFiles := [("static", "static")],
    sourceLink := some "https://github.com/FormalizedFormalLogic/Foundation",
    issueLink := some "https://github.com/FormalizedFormalLogic/Foundation/issues",
    logo := some "/static/logo.svg",
  }
