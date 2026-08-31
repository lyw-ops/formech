# Third-party notices and provenance

This file records attribution and dependency licensing boundaries. It does not
replace the corresponding license texts.

## Imported Lean material

The MIT license retained at `lean/LICENSE` carries this notice:

> Copyright (c) 2025 Math_XMUM

Repository-original additions do not remove or replace the rights and
attribution associated with that material.

## Dependencies

The Lean package depends directly on Lean 4 and mathlib. Their sources are not
vendored in this Git repository; Lake resolves mathlib and its transitive
dependencies according to `lean/lakefile.lean` and `lean/lake-manifest.json`,
while `lean/lean-toolchain` selects the Lean toolchain. Each dependency remains
subject to its own license.
