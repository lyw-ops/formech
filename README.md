# Formech

Formech began as a small "baby project" built during a summer school at
Shanghai Jiao Tong University (SJTU). It uses Lean 4 to explore the
formalization of mechanism design and now serves as a lightweight staging
repository. Reusable definitions and theorems are intended to move into
[EconCSlib](https://github.com/gametheoryinlean/EconCSLib) after their
interfaces stabilize.

The repository intentionally contains only the active Lean prototype, its Lake
configuration, and the documentation and licensing metadata needed to build and
redistribute it. Historical Coq sources, course materials, and unrelated binary
references are not vendored here.

## Current contents

```text
lean/
├── formech.lean                    # Core mechanism-design definitions
├── single_item_fixed_price.lean    # Fixed-price auction and truthfulness proof
├── lakefile.lean                   # Lake package definition
├── lake-manifest.json              # Locked Lean dependency graph
├── lean-toolchain                  # Pinned Lean toolchain
└── LICENSE                         # License retained for imported Lean material
```

The package currently provides fixed-length action profiles, agent and
mechanism structures, preferences and truthfulness, a single-item auction
wrapper, and an executable fixed-price auction whose truthfulness is proved in
Lean.

## Fixed-price auction

The implemented mechanism sells one indivisible item to one of `n` agents at a
publicly fixed posted price `p`. Agents are indexed by `Fin n` and submit a
natural-number bid vector `β`.

The allocation and payment rules are:

1. Agent `i` is eligible exactly when `p ≤ βᵢ`.
2. If at least one agent is eligible, `Fin.find?` selects the eligible agent
   with the smallest index. This fixed priority order is the tie-breaking rule.
3. If nobody is eligible, the result is `none` and the item is not allocated.
4. The winner pays exactly `p`; every other agent has no payment.
5. For true value `vᵢ`, the winner's utility is `vᵢ - p`, while a non-winner's
   utility is `0`.

These pieces appear in `single_item_fixed_price.lean` as `swf`, `tb`,
`payment`, and `auction`. For example, at price `10`, bids `#v[7, 12, 12]`
select zero-based agent `1`, who pays `10`; bids `#v[3, 7, 9]` leave the item
unallocated.

### Truthfulness result

`Single_Item_Fixed_Price.truthful` proves weak dominant-strategy truthfulness
for every number of agents, posted price, and true-value profile. Holding every
other bid fixed, an agent cannot obtain greater utility by changing only their
own bid instead of reporting their true value:

- if the true value is at least the price and no earlier eligible agent blocks
  them, truthful bidding wins with utility `vᵢ - p`;
- if an earlier eligible agent exists, changing the agent's own bid cannot
  change that earlier agent's priority;
- if the true value is below the price, truthful bidding loses and has utility
  `0`.

The current prototype defines bids, values, payments, and utilities using
natural numbers. Consequently Lean's natural-number subtraction truncates at
zero: winning with `vᵢ < p` also has utility `0`, rather than a negative loss.
The theorem is correct for this model, but a future economically richer model
should use integer-valued utility if it needs to represent losses from
overpayment.

## Build

Requirements:

- `elan`;
- Lean `4.33.0`, selected by `lean/lean-toolchain`;
- mathlib `v4.33.0`, pinned by `lean/lake-manifest.json`.

Run all Lean commands from the package directory:

```sh
cd lean
lake env lean formech.lean
lake env lean single_item_fixed_price.lean
lake build
```

`lake build` is the final validation command. Do not run `lake update` merely to
work around a build issue, because the checked-in manifest is part of the
reproducible Lean setup.

## Design direction

- Keep proposition-level specifications distinct from executable Boolean
  predicates, with correctness lemmas connecting them.
- Prefer proof-carrying interfaces for choices such as tie-breaking.
- Keep notation and instances scoped so reusable pieces can migrate cleanly.
- Prefer a small generic finite checker over a Formech-specific auction DSL.
- State finite bounds explicitly; bounded exhaustive checks are not unrestricted
  mathematical theorems.

## Licensing

Repository-original material is available under the Apache License 2.0 in the
root `LICENSE`. Imported Lean material retains the MIT notice in `lean/LICENSE`.
Lean, mathlib, and transitive Lake dependencies remain subject to their own
licenses; see `THIRD_PARTY_NOTICES.md`.
