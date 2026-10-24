# Hoare Program Carrier

<!-- 561-group-standards:badges:start -->
[![Lenticule Science](https://img.shields.io/badge/561%20Group-Lenticule%20Science-5b4b8a)](https://github.com/lenticule-science)
[![License: MIT](https://img.shields.io/badge/license-MIT-5b4b8a)](LICENSE)
[![Indigenous data: CARE](https://img.shields.io/badge/Indigenous%20data-CARE-4b6f44)](https://github.com/lenticule-science/.github/blob/main/GOVERNANCE.md)
[![Tips welcome](https://img.shields.io/badge/tips-welcome-d4a017)](https://github.com/561-group/.github/blob/main/TIPS.md)
<!-- 561-group-standards:badges:end -->

This is the Lean half of the former `hoare-program-measurement` micro-enterprise, split 2026-07-30 from its sibling application service, [`finite-program-measurement-service`](../finite-program-measurement-service) (zero registry dependents verified before the split).

This is not part of the Obsmetrologia mathematics library. It imports Obsmetrologia across OSS's owned-checkout seam and owns the program-specific carrier and its keratinous application.

The formal surface is a Lean library. It verifies preservation witnesses and derives the least-compatible-state result for a keratinous transition.

The generic preservation theorem is axiom-free. The current keratinous projection and least-compatible-state theorem inherit `Quot.sound` from their Obsmetrologia dependency; `make check` prints this audit explicitly.

Run `make check` to build the library and its mathematical dependency and print the axiom audit.

This package retains the enterprise's standing identity records (`lib/ownership.json`, `lib/management/roster.json`, `content/offices/formal-program-measurer.json`, `content/evm/accounts/eip155-31337.json`, and their append-only `data/` evidence) inherited unchanged from `hoare-program-measurement`; the application half was carved out fresh and holds no separate identity of its own.

## Code

This repository holds section data only. The executable code that used to live here moved to
[`red-cup-engineering/hoare-program-carrier`](https://github.com/red-cup-engineering/hoare-program-carrier) (received 2026-10-24 from
`lenticule-science/hoare-program-carrier@2ec8c32d7677`). That engine reads this data from `SECTION_ROOT` (default: its current working directory),
so point `SECTION_ROOT` at a checkout of this repository.
