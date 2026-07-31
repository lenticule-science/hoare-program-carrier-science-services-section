# Hoare Program Carrier

This is the Lean half of the former `hoare-program-measurement` micro-enterprise, split 2026-07-30 from its sibling application service, [`finite-program-measurement-service`](../finite-program-measurement-service) (zero registry dependents verified before the split).

This is not part of the Obsmetrologia mathematics library. It imports Obsmetrologia across OSS's owned-checkout seam and owns the program-specific carrier and its keratinous application.

The formal surface is a Lean library. It verifies preservation witnesses and derives the least-compatible-state result for a keratinous transition.

The generic preservation theorem is axiom-free. The current keratinous projection and least-compatible-state theorem inherit `Quot.sound` from their Obsmetrologia dependency; `make check` prints this audit explicitly.

Run `make check` to build the library and its mathematical dependency and print the axiom audit.

This package retains the enterprise's standing identity records (`lib/ownership.json`, `lib/management/roster.json`, `content/offices/formal-program-measurer.json`, `content/evm/accounts/eip155-31337.json`, and their append-only `data/` evidence) inherited unchanged from `hoare-program-measurement`; the application half was carved out fresh and holds no separate identity of its own.
