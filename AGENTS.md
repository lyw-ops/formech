# Formech agent guide

This file supplies project context to AI coding agents and human contributors.

## Project role

Formech is a temporary staging repository for a Lean 4 mechanism-design
prototype. Stable abstractions are expected to move into EconCSlib. Optimize for
correct semantics, small reusable interfaces, and easy migration rather than for
a large Formech-specific framework.

The repository is intentionally Lean-only: do not add historical implementations
in other proof assistants, vendored course collections, unrelated binaries, or
generated build products.

## Read first

Before proposing or making changes, inspect:

1. `README.md`;
2. `lean/formech.lean`;
3. `lean/single_item_fixed_price.lean`.

## Validation

Run Lean commands from `lean/`:

```sh
lake env lean formech.lean
lake env lean single_item_fixed_price.lean
lake build
```

The final validation for Lean source changes is `lake build`. Do not update the
toolchain or run `lake update` as an incidental fix.

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

- `lean/` is the active implementation and the Lake package root.
- Keep only source files used by the package and files required to resolve and
  pin its Lean dependencies.
- Preserve the root `LICENSE`, `lean/LICENSE`, and applicable attribution in
  `THIRD_PARTY_NOTICES.md`.
- Do not commit `.lake/`, generated object files, editor state, or downloaded
  reference material.

## Change discipline

- Keep edits focused.
- Add assertions or theorem examples rather than relying only on raw `#eval`
  output when behavior is intended as a regression check.
- Document any finite bounds used by exhaustive verification; never present a
  bounded result as a theorem over arbitrary agents or action spaces.
- Update `README.md` when the canonical build, project status, dependencies, or
  migration plan materially changes.
