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
