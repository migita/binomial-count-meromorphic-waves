# Rigidity through degree 572

Exact finite-field Gröbner computations establish continuous-convolution rigidity for every degree `0 <= d <= 572`:

`A | integral_0^x A(t) A(x-t) dt` implies `A = c x^d`.

For the manuscript this extends the counting formulas **with multiplicity** to every profile order `2 <= p <= 573`, since `d=p-1`; simplicity of the discrete matching schemes is a separate question.

The reduction lemmas in [the existing ancillary proof](../../paper/anc/rigidity/proof.tex) work for every even gap `g<q`; the older degree-72 package supplies integer identities, while this extension supplies exact finite-field computation records and the code to reproduce them.

## What is stored

- `coverage.csv`: one triple `(q,e,g)` for each `d=1,...,572`, with `2d+1=q^e+g`, `q` an odd prime and `0<=g<q` even.
- `results.jsonl`: the 1,836 selected stratum records for the 383 positive-gap pairs used by that table, including leading-ideal pure powers and checked quotient dimensions/Hilbert functions.
- `kernel.py`: exact coefficient and polynomial-remainder construction.
- `check_kernel.py`: independent polynomial division over the rationals for all 90 gap-system families; this optional check needs SymPy.
- `verify.py`: integrity, complete coverage, recorded outcomes and independent actual-degree beta-weight checks; it uses only the Python standard library.
- `replay.py`: fresh msolve computations, with exact sparse linear algebra and a full weighted Hilbert-function cross-check; it additionally needs NumPy and msolve.
- `proof.md`: why these finite-field checks imply rigidity over C.
- `computation_scope.md` and `provenance.json`: the original computation's scope and source records.
- `MANIFEST.json`: sizes and SHA-256 hashes of the package files.

The table uses prime gaps (`e=1`) except for the already proved prime-power index `d=4`, where `9=3^2`; `d=452` uses `(q,e,g)=(887,1,18)`, and no chain criterion is needed.

Computed Gröbner bases, solver binaries and research scratch directories are regenerated when needed and are not included.

## Validate the stored record

```sh
python3 verify.py
```

This checks all 572 rows, every required stratum, all file hashes and the actual-degree reduction of the beta coefficients from exact factorials; it reports explicitly that it has not rerun the Gröbner computations.

With SymPy installed, `python3 check_kernel.py` independently checks the sparse polynomial generator in exact rational arithmetic for every even gap through 18 and every stratum.

## Recompute with msolve

The recorded runs use msolve with `-g 1 -l 2 -t 1`: leading ideals and **exact** sparse linear algebra; the packaged driver has been tested with msolve 0.10.1.

```sh
python3 replay.py --msolve /path/to/msolve --q 139 --g 8
python3 replay.py --msolve /path/to/msolve --q 887 --g 18 --stratum 9
python3 replay.py --msolve /path/to/msolve --all --output /tmp/rigidity-572-replay.jsonl
```

A full replay can take about an hour or longer on one core; the recorded msolve time of the selected strata sums to approximately 52 minutes, excluding Python verification and machine-dependent overhead.

Each stratum has a default 1,500-second time limit and a 32-GiB address-space cap on POSIX, adjustable with `--timeout` and `--memory-gb`; all solver input and output files live in an automatically removed temporary directory.

Negative controls are available, for example:

```sh
python3 replay.py --msolve /path/to/msolve --q 7 --g 2 --stratum 2 --expect-nonrigid
```

The positive criterion is a power of every variable in the computed leading ideal; weighted homogeneity then makes the origin the only geometric zero, including over extension fields, and the additional staircase calculation checks the entire expected Gaussian-binomial Hilbert function.

The stored records come from the independent second-referee pipeline of 17 September 2026; fresh package checks and selected replays are recorded separately in `validation.json` and `fresh_replays.jsonl`, when present.
