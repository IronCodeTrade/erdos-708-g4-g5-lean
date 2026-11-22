# Licence and attribution

Before you publish this repository, choose one licence and rename that file to `LICENSE`:

- `LICENSE_CC0.txt` — recommended. This matches Haoyu Chen's repository (CC0 1.0) and is the simplest choice for a mathematical formalisation.
- `LICENSE_MIT.txt` — also possible. Chen's files under `Erdos708/` remain CC0 in any case.

Then delete the licence file you did not choose, or leave both as documentation and keep the chosen one named `LICENSE`.

## Third-party code

The files

- `Erdos708/Chain/Defs.lean`
- `Erdos708/Chain/Arithmetic.lean`
- `Erdos708/Chain/Proofs/LongInterval.lean`

are taken, without mathematical changes, from Haoyu Chen's Lean development of explicit upper bounds for the Erdős–Surányi function g(n):

- https://github.com/chy4pro/erdos-708-explicit-upper-bounds
- Zenodo concept DOI: 10.5281/zenodo.22267395
- Licence: CC0 1.0 (https://creativecommons.org/publicdomain/zero/1.0/)

The lemma `Erdos708Chain.Proofs.long_interval` is due to Chen. Please keep this attribution.
