# doc-gen repository for Foundation

## Build

```shell
lake build Foundation:docs
```

## Preview

```shell
miniserve .lake/build/doc
```

## Update dependencies

```shell
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
```
