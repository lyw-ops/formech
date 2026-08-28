# Third-party notices and provenance

Formech currently combines repository-original experimental material with two
imported bodies of work. This file records the visible provenance and licensing
metadata; it does not replace the license texts or notices in the relevant
files.

## Coq mech.v development

Path: `coq/`

Upstream: <https://github.com/jouvelot/mech.v>

The upstream project describes itself as a Coq and Mathematical Components
formalization of mechanism design. The copied sources retain their author and
license headers. The local `coq/coq-mech.opam` declares
`LGPL-2.1-or-later`, while a number of individual source headers say
`CeCILL-B`. Because these upstream declarations are not uniform, consumers
should inspect the relevant file headers and confirm the applicable terms with
the upstream project before redistribution or relicensing. Formech does not
override those declarations with its root Apache license.

Principal contributors named by the upstream README include Pierre Jouvelot,
Emilio Gallego Arias, Lucas Massoni Sguerra, and Zhan Jing.

## Imported Lean material

Path: `lean/`

The license file at `lean/LICENSE` is the MIT License and carries the notice:

> Copyright (c) 2025 Math_XMUM

That notice is retained verbatim. Repository-original additions do not remove
or replace the rights and attribution associated with imported material.

## Dependencies

The Lean package depends on Lean 4 and mathlib. Their sources are not vendored in
the Git repository; Lake resolves them according to `lean/lakefile.lean` and
`lean/lake-manifest.json`. Each dependency remains subject to its own license.
