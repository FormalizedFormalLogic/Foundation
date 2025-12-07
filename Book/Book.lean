import Book.Main

open Verso.Genre.Manual

def juliamonoFonts := (include_bin_dir "./assets/juliamono") |>.map λ (name, contents) => (name.stripPrefix "./assets/", contents)

def main := manualMain (%doc Book.Main) (config := config)
where
  config := Config.addKaTeX {
    htmlDepth := 2,
    sourceLink := some "https://github.com/FormalizedFormalLogic/Foundation",
    issueLink := some "https://github.com/FormalizedFormalLogic/Foundation/issues",
    extraFiles := [("./Book/assets", "./assets")],
    logo := some "/assets/logo.svg",
    extraCssFiles := #[("./style.css", include_str "./style.css")],
    extraDataFiles := juliamonoFonts,
  }
