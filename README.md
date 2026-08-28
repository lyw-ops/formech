# Formech

Formech is a short-lived staging repository for formalizing mechanism design in
Lean 4 while keeping an older Coq/Mathematical Components development available
as a reference. The reusable parts of the Lean development are intended to move
into [EconCSlib](https://github.com/gametheoryinlean/EconCSLib) after their
interfaces have stabilized.

The repository is experimental. It is useful for API design, small executable
examples, and comparison with the Coq development; it is not yet a stable
mechanism-design library.

## Current focus

The Lean prototype currently provides:

- fixed-length action profiles based on `Vector`;
- agents represented by `Fin n`;
- basic mechanism and preference structures;
- mechanisms assembled from a social-welfare predicate and tie-breaking rule;
- a single-item auction wrapper with payments and utilities;
- an executable fixed-price auction example.

The next likely reusable component is a finite-mechanism interface with
computable checks and counterexample search for properties such as strategy
proofness. Any such component should remain independent of Formech-specific
syntax so that it can be moved into EconCSlib.

## Repository layout

```text
.
├── lean/
│   ├── formech.lean                    # Core Lean prototype
│   ├── single_item_fixed_price.lean    # Executable fixed-price auction
│   ├── notes/                          # Design experiments and notes
│   └── SJTU_AI4Math/                   # Supporting course/reference material
├── coq/                                # Coq mech.v reference development
├── AGENTS.md                           # Context and rules for coding agents
└── THIRD_PARTY_NOTICES.md              # Provenance and licensing boundaries
```

The canonical Lean package root is `lean/`. The `SJTU_AI4Math` directory is not
part of the Formech Lake build and contains exercises with intentional `sorry`s.
The Coq tree is not a dependency of the Lean package.

## Build the Lean prototype

Requirements:

- `elan`;
- Lean `4.33.0`, selected by `lean/lean-toolchain`;
- mathlib `v4.33.0`, pinned by `lean/lake-manifest.json`.

From the repository root:

```sh
cd lean
lake build
```

For faster checks of the two library roots:

```sh
cd lean
lake env lean formech.lean
lake env lean single_item_fixed_price.lean
```

The executable example currently evaluates two bid profiles in
`lean/single_item_fixed_price.lean`.

## Coq reference

The `coq/` directory is derived from the upstream
[jouvelot/mech.v](https://github.com/jouvelot/mech.v) project. Its README reports
testing with Coq 8.17 and Mathematical Components 1.17. This checkout has not
been revalidated as part of the initial Formech publication because the local
environment does not currently provide Coq, Dune, or opam.

Some Coq files contain `Admitted` proof obligations. Treat the tree as reference
material rather than as a fully checked dependency of the Lean prototype.

## Status and design cautions

- The current Lean API is exploratory and may change before migration.
- `Pred` is presently Boolean-valued, and `Tie_Break` does not yet carry a proof
  that the selected outcome is acceptable. Strengthening this boundary is more
  important than adding a large syntax DSL.
- Global notation and instances should be made scoped before integration into a
  larger library.
- Finite exhaustive checks can validate a concrete finite mechanism and produce
  useful counterexamples, but they do not replace theorems quantified over all
  numbers of agents or all bid domains.

## Context for AI assistants

When analyzing this repository:

1. Read `AGENTS.md`, `lean/formech.lean`, and
   `lean/single_item_fixed_price.lean` first.
2. Treat `lean/` as the active prototype and `coq/` as an upstream reference.
3. Do not infer the current Lean API solely from the Coq architecture.
4. Prefer changes that can later live under an EconCSlib mechanism-design
   namespace without Formech-specific assumptions.
5. Distinguish ordinary executable reflection from metaprogramming: a Boolean
   checker is an ordinary Lean program; a custom command that discovers a
   mechanism, runs the checker, and reports or emits declarations is meta code.

## Roadmap

1. Strengthen the core mechanism and tie-breaking interfaces.
2. Separate proposition-level specifications from Boolean decision procedures.
3. Introduce a small generic finite-mechanism interface.
4. Implement manipulation/strategy-proofness counterexample search.
5. Prove the Boolean checker correct with respect to the proposition-level
   definition.
6. Add only a thin custom command if it materially improves the workflow.
7. Migrate stable, reusable pieces into EconCSlib.

## Licensing and provenance

Repository-original material is provided under the Apache License 2.0 in
`LICENSE`, unless a file or subtree states otherwise. Imported material retains
its own notices and terms. In particular, `lean/LICENSE` and the metadata and
source headers under `coq/` must be read separately. See
`THIRD_PARTY_NOTICES.md` before redistributing either subtree.
