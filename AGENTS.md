# Formech agent guide

This file supplies project context to AI coding agents and human contributors.

## Project role

Formech is a temporary staging repository for a Lean 4 mechanism-design
prototype. Stable abstractions are expected to move into EconCSlib. Optimize for
correct semantics, small reusable interfaces, and easy migration rather than for
a large Formech-specific framework.

## Read first

Before proposing or making changes, inspect:

1. `README.md`;
2. `lean/formech.lean`;
3. `lean/single_item_fixed_price.lean`;
4. any directly relevant file under `lean/notes/`;
5. the corresponding `coq/` module only when historical comparison is useful.

The files under `lean/SJTU_AI4Math/` are supporting course/reference material,
not part of the Formech Lake library. Do not use their intentional `sorry`s to
assess the status of the Formech core.

## Validation

Run Lean commands from `lean/`:

```sh
lake env lean formech.lean
lake env lean single_item_fixed_price.lean
lake build
```

The final validation for Lean source changes is `lake build`. Do not update the
toolchain or run `lake update` as an incidental fix.

The Coq development requires its own historical toolchain. If Coq, Dune, or opam
is unavailable, report that limitation rather than claiming the Coq tree was
validated.

## Design constraints

- Preserve the distinction between mathematical propositions and executable
  Boolean predicates, and provide correctness lemmas when connecting them.
- Prefer proof-carrying interfaces for choices such as tie-breaking.
- Avoid global syntax and type-class pollution; use namespaces and scoped
  notation for reusable code.
- Prefer ordinary Lean definitions and theorems before introducing custom
  syntax or elaborators.
- If metaprogramming is added, keep the trusted result as a kernel-checked proof
  term or a theorem backed by a proved reflection result.
- Do not build a large Formech-only auction DSL without evidence from several
  mechanisms. A small generic finite checker is more portable to EconCSlib.
- Keep generated names, attributes, and public APIs independent of the current
  repository layout whenever practical.

## Repository boundaries

- `lean/` is the active implementation.
- `coq/` is imported reference material derived from `jouvelot/mech.v`; preserve
  its authorship and license notices.
- Preserve `lean/LICENSE` and the attribution of imported Lean material.
- Do not silently rewrite third-party headers or represent the whole repository
  as having one uniform license. See `THIRD_PARTY_NOTICES.md`.

## Change discipline

- Keep edits focused and avoid modifying course/reference files unless asked.
- Add assertions or theorem examples rather than relying only on raw `#eval`
  output when behavior is intended as a regression check.
- Document any finite bounds used by exhaustive verification; never present a
  bounded result as a theorem over arbitrary agents or action spaces.
- Update `README.md` when the canonical build, project status, or migration plan
  materially changes.
