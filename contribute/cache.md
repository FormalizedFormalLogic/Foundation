# Build cache

Foundation publishes its compiled modules to an R2 store shared across FormalizedFormalLogic
repositories, so a fresh clone does not have to elaborate the whole library.

Mathlib is a separate cache: `lake exe cache get`, as always.

## For contributors

After cloning, and after a `git pull` that moves you a long way:

```shell
just cache
```

If your revision was never published — the normal case on a feature branch — Lake walks back
through the history to one that was. A miss is not an error; the build just compiles from source.
Nothing to configure: reads are anonymous.

## How it works

`lake cache` ships with Lake since Lean v4.34. `lake build --no-build -o <file> <target>` writes a
build's input-to-output mapping, stored under the Git revision it came from.

- **Publishing.** `ci.yml` uploads on pushes to `master`, after every gate has passed, signing
  with AWS SigV4 using the `LAKE_CACHE_KEY` secret.
  The CI steps live in [`FormalizedFormalLogic/.github/lake-cache`][actions] as composite
  actions, shared across the organisation. Not reusable workflows: these steps have to interleave
  with the build in the same job.
- **Reading.** Lake cannot sign a download, so the read host is anonymous. CI uses it when the
  `actions/cache` tarball misses; `just cache` is the same path for contributors.

Both find their service in [`lake-cache.toml`](../lake-cache.toml) via `LAKE_CONFIG`. Committed
rather than generated per run: the endpoints are not secrets and one copy cannot drift from
another. The `LAKE_CACHE_ARTIFACT_ENDPOINT` environment variables also work, but Lake warns they
are deprecated.

`lakefile.toml` sets `platformIndependent = true` so the Linux build CI publishes serves every
platform; without it a macOS contributor would always miss.

The `actions/cache` tarball stays primary — it is faster when it hits. R2 covers what it
structurally cannot: fork PRs, evictions, new branches, and everyone outside CI.

## Cloudflare

| | |
|---|---|
| R2 bucket | `ffl-lake-cache`, shared by every FFL repository |
| Read host | `https://ffl.sno2wman.net`, custom domain on the bucket |
| Account | `411f2fda06461f8aa09a9055685d6fd9` (not a secret: it is the S3 endpoint's subdomain) |
| Zone | `sno2wman.net`, `201e8d53e79a1cd20558aa2b81412d40`, same account |

A custom domain because Cloudflare rate-limits `pub-<id>.r2.dev` and
[documents it as development-only][r2-public]; the `r2.dev` URL is disabled. It
[requires the zone in the same account][r2-custom] as the bucket. Moving off this domain later
costs one line per repository and one cold build — the cache is disposable.

A public bucket exposes every object by key (listing is not). Nothing but the cache belongs here.

[r2-public]: https://developers.cloudflare.com/r2/buckets/public-buckets/
[r2-custom]: https://developers.cloudflare.com/r2/buckets/public-buckets/#add-your-domain-to-cloudflare

### Repository configuration

| Name | Kind | Value |
|---|---|---|
| `LAKE_CACHE_ENABLED` | variable | `1` enables the cache; anything else makes every cache step in `ci.yml` a no-op |
| `LAKE_CACHE_KEY` | secret | `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` of an R2 token |

`LAKE_CACHE_ENABLED` is the kill switch: turning the cache off is a variable edit, not a revert.

The token must be an **Account API token** with **Object Read & Write** scoped to
`ffl-lake-cache` alone — the `Admin` tiers cannot be bucket-scoped and would reach unrelated
buckets in this account. Issue one per repository so revocation is independent. To rotate:
create the replacement, install it, confirm one publish on `master`, revoke the old one.

The secret shares a job with `lake build`, and Lean runs arbitrary code at elaboration time, so
code on `master` could reach it. Everything reaches `master` by reviewed PR, and PRs never see
the secret. The stronger form, if that stops being enough, is `lake cache stage` in the build job
and `lake cache put-staged` from a separate one, as [TauCeti][tauceti] does.

[tauceti]: https://github.com/TauCetiProject/TauCeti/blob/main/.github/workflows/publish-lake-cache.yml

### Cache Rule

`.art` is not [cached by default][default-cache], so artifact reads need a rule on the
`sno2wman.net` zone (Caching → Cache Rules):

```
(http.host eq "ffl.sno2wman.net" and starts_with(http.request.uri.path, "/artifacts/"))
```

Eligible for cache; Edge TTL ignore cache-control, one month. Leave `/revisions/` alone: a lookup
for an unpublished revision 404s, and a cached 404 would hide it once CI publishes.

Verify by requesting an artifact twice — `cf-cache-status` should go `MISS` then `HIT`.
`DYNAMIC` means the expression is not matching.

[default-cache]: https://developers.cloudflare.com/cache/concepts/default-cache-behavior/

### Adding another FFL repository

No Cloudflare work: Lake keys objects by `<owner>/<repo>`, so repositories share the bucket
without colliding. In the new repository:

1. Copy `lake-cache.toml` verbatim and the `cache` recipe from the `Justfile`, adjusting `--repo`.
2. Add the two [`FormalizedFormalLogic/.github/lake-cache`][actions] steps to its workflow.
3. Set the `LAKE_CACHE_ENABLED` variable and the `LAKE_CACHE_KEY` secret.
4. Set `platformIndependent = true` in its `lakefile.toml`.

[actions]: https://github.com/FormalizedFormalLogic/.github/tree/main/lake-cache

### Cost

Egress is free; reads are Class B operations, 10M/month free. Foundation is ~210 modules, so a
cold fetch is ~210 reads — the whole organisation stays well inside the free tier, before the
edge cache is counted at all.
