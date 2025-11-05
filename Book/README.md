# Book

## Setup

Add JuliaMono (optional)

```shell
cd ./Book/assets

wget https://github.com/cormullion/juliamono/releases/download/v0.061/JuliaMono-webfonts.tar.gz
mkdir juliamono
tar -xvf JuliaMono-webfonts.tar.gz -C juliamono --strip-components 1
rm JuliaMono-webfonts.tar.gz
```

## Notes

### Format `bibliography.bib`

```
npx bibtex-tidy ./bibliography.bib --v2 --modify --remove-braces=title,journal --sort=key --sort-fields --omit=abstract,keywords,file,note
```

## Disclaimer

- [./Meta/Markdown.lean](./Meta/Markdown.lean) is borrowed from [leanprover/reference-manual](https://github.com/leanprover/reference-manual/blob/4f6e6aa472ab0da8ea87a0cd2a395049fa2b138e/Manual/Meta/Markdown.lean). Original author is _Joachim Breitner_.
