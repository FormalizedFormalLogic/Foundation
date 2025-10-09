import Book.Main

open Verso.Genre.Manual

def main := manualMain (%doc Book.Main) (config := config)
where
  config := Config.addKaTeX {
    sourceLink := some "https://github.com/FormalizedFormalLogic/Foundation",
    issueLink := some "https://github.com/FormalizedFormalLogic/Foundation/issues",
    extraFiles := [("./Book/assets", "./assets")],
    logo := some "/assets/logo.svg",
    extraCss := ["/assets/style.css"],
    htmlDepth := 2
  }
