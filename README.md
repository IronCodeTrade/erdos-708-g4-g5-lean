# g(4) ≤ 8 and g(5) ≤ 10 for Erdős problem #708

This repository contains a Lean 4 formalisation of the partial bounds

```
g(4) ≤ 8    and    g(5) ≤ 10
```

for the Erdős–Surányi function of [Erdős problem #708](https://www.erdosproblems.com/708). Combined with the known lower bounds, one has `5 ≤ g(4) ≤ 8` and `6 ≤ g(5) ≤ 10`.

This does **not** resolve the \$100 question, which asks whether `g(n) ≤ 2n` (or `g(n) ≤ (2+o(1))n`) for every `n`. That question remains open.

A short English note is in the submission package (PDF) that accompanies this source.

## Statements

The Mathlib-only statements are `E708F.g4_le_8` and `E708F.g5_le_10` in `E708F/G4.lean` and `E708F/G5.lean`:

```lean
theorem E708F.g4_le_8 : ∀ (A : Finset ℕ) (M : ℕ), A.card = 4 → M ∈ A →
    (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) → ∀ x : ℕ,
    ∃ B ⊆ Finset.Icc (x + 1) (x + M),
      B.card ≤ 8 ∧ (∏ a ∈ A, a) ∣ ∏ b ∈ B, b

theorem E708F.g5_le_10 : -- the same with A.card = 5 and B.card ≤ 10
```

The quantification over `x : ℕ` means intervals of positive integers, as in Chen's formal statement. A run containing 0 is trivial, and a run of negative integers is the negative of a positive one.

There are no `sorry`s.

## Method, in brief

- If `m = max A ≤ 2n`, the whole interval of length `m` works.
- If `m ≥ 8n³`, apply Chen's `long_interval` lemma.
- In the remaining finite range (`9 ≤ m ≤ 511` for `n = 4`; `11 ≤ m ≤ 999` for `n = 5`), an exhaustive search in Lean either obtains a cost bound of at most `2n`, or an explicit partition certificate of size at most `2n`.

## Build

Toolchain: **Lean 4.36.0**, Mathlib **v4.36.0** (see `lean-toolchain` and `lakefile.toml`). The first build will download Mathlib and may take substantial disk space and time.

```bash
# optional, uses the community cache
lake exe cache get

# n = 4 is comparatively quick (about a minute on a recent desktop)
lake build E708F.G4

# n = 5 is heavy: on the original machine it took about 1.5–2 hours on 8 cores
lake build E708F.G5

# print axioms
lake env lean E708F/CheckAll.lean
```

`lake build` (default target `E708`) builds both theorems. A recorded `#print axioms` output is in `axioms_final.txt`.

Negative tests, which check that the certificate checker rejects bad certificates and that the `n = 4` enumeration fails if the budget is lowered to 4, are in `tests/Neg.lean`:

```bash
lake env lean tests/Neg.lean
```

## Axioms and the `native_decide` caveat

From `axioms_final.txt` (22 November 2026, Europe/Warsaw):

- `E708F.cert_good` and `Erdos708Chain.Proofs.long_interval` depend only on `propext`, `Classical.choice` and `Quot.sound`.
- `E708F.g4_le_8` additionally depends on the `native_decide` axioms for `allOK4` and `primeTab_ok`.
- `E708F.g5_le_10` additionally depends on 48 `native_decide` axioms for the `n = 5` chunks, together with `cov48` and `primeTab_ok`.
- `E708F.cost_good` depends on the standard axioms plus `primeTab_ok`.

`native_decide` trusts the Lean compiler and the compiled C code, not the most rigorous kernel tactic `decide`. This should be stated whenever the result is cited, until a kernel-only check exists.

## Attribution

The files under `Erdos708/` are Haoyu Chen's, used without mathematical changes, under CC0. See `NOTICE.md`. The lemma `long_interval` is due to Chen:

- https://github.com/chy4pro/erdos-708-explicit-upper-bounds
- Zenodo: 10.5281/zenodo.22267395

## AI use

The proof search, the computational work, the Lean formalisation and the accompanying write-up were produced with substantial assistance from an AI system (Grok Bot, used in Cursor), for Krzysztof Paweł Michalak (Infinitas). This is disclosed so that the work can be assessed honestly.

## Licence

See `NOTICE.md`. Choose `LICENSE_CC0.txt` (recommended) or `LICENSE_MIT.txt`, rename the chosen file to `LICENSE`, and publish.
