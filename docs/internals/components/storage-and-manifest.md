# Internals: Storage and Manifest

Sources:
- `core/src/storage/tl_page.*`
- `core/src/storage/tl_segment.*`
- `core/src/storage/tl_manifest.*`
- `core/src/storage/tl_window.*`

## Immutable Layout

- Pages store sorted timestamp and handle columns.
- Segments group pages and metadata bounds.
- Manifest is immutable and copy-on-write published.

## Level Semantics

`Contract`
- L0 overlap is allowed.
- L1 is non-overlapping by window constraints.

## Publication

`Implementation note`
- New manifests are built off-lock, then swapped atomically in short publish sections.
- Old manifests remain valid for pinned snapshots until refcount release.

## Metadata Integrity

- min/max bounds and page catalogs are used for pruning.
- Window mapping enforces L1 partition invariants.
