# Odd Zeta Five · B40a

[![Archived v1.0.0 DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24528775.svg)](https://doi.org/10.5281/zenodo.24528775)

At least one of **ζ(7), ζ(9), ζ(11), ζ(13), ζ(15)** is irrational. The root module `OddZetaFive.lean` imports the theorem in its original namespace. The real part refers to Mathlib's complex Riemann zeta function evaluated at a positive integer.

```lean
OddZetaSix.B40a.exists_irrational_riemannZeta_seven_to_fifteen :
  ∃ s ∈ ({7, 9, 11, 13, 15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re)
```

In version 1.1.0, Lean's kernel checks all 1,375 middle-prime rows in 43 shards. The main theorem has exactly the three standard axioms in the audit below. The [paper](paper/odd_zeta_five_b40a.pdf) and [LaTeX source](paper/odd_zeta_five_b40a.tex) describe the construction.

## Construction and comparison

| Quantity | B40a |
|---|---|
| Kernel parameters | L = 50, U = 34, s = 25 |
| Denominator offsets with multiplicities | six copies of 0, four of 8, two of 9 |
| Center, rank and exponential scale | 59n + 1, h = 40n, N = 2000n² |
| Local prime and interpolation data | p = 51n + 1 prime, 8n order-six poles, five Taylor coefficients per pole |
| Specialized determinant valuation | −269n + 2 for coordinates integral at p |
| Analytic certificate | eight contour nodes per half, 34 conjugate circle pairs, 119 finite panels, infinite ray |
| Arithmetic certificate | 706 cells in the fractional part of n/p, 1,375 cells in the middle prime band, four upper-band integrals |
| Limiting rates | A ≤ −6.19, C ≤ 6.1405, A + C ≤ −0.0495 |

The six-value baseline at revision `09201a928982c1e282ba2a1a3156d8f400d4b436` includes ζ(17). Its rounded analytic and arithmetic exponents are −7.79 and 7.76. B40a's maximum pole order is twelve. After four derivatives, simple-pole cancellation and reflection leave only the five weights 7 through 15. The retained `OddZetaSix` source tree contains the modules reached from the new entry point. Historical stage targets have been removed. [Six-value baseline](https://github.com/janahesse580-star/odd-zeta-six-lean/tree/09201a928982c1e282ba2a1a3156d8f400d4b436)

## Reproduce from the repository root

With Git, elan and Python 3.10 or newer on PATH, run the following in a POSIX shell. Elan selects the toolchain from `lean-toolchain`. The first command requires network access for the dependencies and their compiled cache.

```sh
export LEAN_NUM_THREADS=2
lake exe cache get && lake build && lake env lean OddZetaFiveAudit.lean && python3 -I -S verify-certificate.py
```

To enforce the exact axiom sets in a saved audit as CI does:

```sh
lake env lean OddZetaFiveAudit.lean > audit.txt && python3 -I -S scripts/check-release.py audit audit.txt
python3 -I -S scripts/check-release.py sources
```

The Python verifier uses only the standard library. It recomputes row costs, upward rounding, row coverage, the upper-prime integral, the circle energy lower bound, the continuous panel bounds and the ray budget. It uses exact integers and fractions and bounds logarithms using the neighboring decimal numbers around a correctly rounded result. CI regenerates and compares all 72 original Lean data files and the 44 new files containing the 43 folding-witness shards and their aggregate. Both generators read the unchanged `b40a/certificate.json`. The release run gives C ≤ 6.140423661027 before the PNT margin. [Numerical transcript](reports/certificate.log) · [Regeneration transcript](reports/witness-regeneration.log)

## Axiom audit

The following is the release run of `#print axioms`.

```text
'OddZetaSix.B40a.exists_irrational_riemannZeta_seven_to_fifteen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The exact-set audit enforces these same dependencies for the arithmetic rate, analytic rate, specialized determinant valuation, and the small- and large-prime rates. Version 1.1.0 removes the last axiom introduced by `native_decide`. Each shard proves `checkFastMiddle ... = true` with `decide +kernel`. The independent Python verifier continues to recompute the original numerical bounds. [Full axiom output](reports/axioms.log)

The checker folds each half-strip into an initial site and at most three periodic runs. It computes the site maxima at the appropriate even and odd endpoints and accumulates a 16-bin histogram in one pass. The soundness proof recovers the original sorted bag and bounds its minimum by the fixed folding candidate for the row. A single integer cross multiplication proves the stored upper bound. The middle budget is `5244756877432 / 10^12`. [Checker](OddZetaSix/B40a/Certificate/FastMiddle.lean) · [Soundness proof](OddZetaSix/B40a/Certificate/FastMiddleSound.lean)

The first 32-row shard took 25.3 seconds of kernel type checking and 40.8 seconds wall time on one thread, including imports. The `#eval` computation took 0.082 seconds. The process peaked at 4,549 MiB of working set. [Pilot source](reports/Middle000-pilot.lean) · [Pilot log](reports/kernel-pilot.log) · [All 43 shard build entries](reports/kernel-shards.log)

## Build and dependency provenance

The local release run used Lean 4.34.0-rc2 (compiler revision `6a10ac8c22beadecabdbb0919c2b50214762f91d`) on Windows x86-64. It reused the pinned dependencies and compiled artifacts of unchanged modules from the v1.0.0 build. All 43 new shard modules were compiled locally, followed by a successful full-package build and standalone audit. The workflow is configured to fetch dependencies on a fresh Ubuntu runner and publish the build and audit logs. [Local build log](reports/lake-build.log) · [Dependency verification](reports/dependencies.log) · [CI workflow](.github/workflows/ci.yml)

Stage 4's earlier Linux logs report “has local changes”. In this version of Lake the warning follows a nonzero result from `git diff --exit-code HEAD`. The earlier archive contains a source comparison reporting 9,233 Mathlib files and files in the other eight packages identical to the pinned archives. It omits the old Git index, status, and diff; the specific paths or cause of the historical warning cannot be recovered from it. This release checks each checkout's HEAD against the manifest and requires an empty porcelain status. It also compares the actual bytes of every tracked Lean source to its pinned Git blob (allowing checkout line-ending conversion); 9,055 Mathlib Lean files matched. The archived Mathlib commit is `dc4b8d60d5edb3c493c3662126b1b7ccae7d67cf`.

The local `PNTDependency` is a separate source package. It vendors selected code from PrimeNumberTheoremAnd (`c39a751132c88b6e8080b74c74023fd95b3d8be0`) and LeanArchitect (`468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`), with documented source selection, pruning and a Wiener compatibility edit. The revision checks for the nine external packages are distinct from the hash checks for 22 vendored module entries. [PNT source provenance](PNTDependency/provenance.json) · [Third-party notices](PNTDependency/licenses/)

## Citing and archiving the release

Version **1.1.0** is authored by **JanaHesse580** (<JanaHesse580@gmail.com>). The root license is MIT. Vendored licenses and attribution accompany their sources. The LaTeX paper builds with `tectonic paper/odd_zeta_five_b40a.tex` or two passes of pdfLaTeX in the paper directory. [Citation metadata](CITATION.cff) · [License](LICENSE)

The badge above identifies the archived v1.0.0 release. The concept DOI identifies the software across releases. [Concept DOI](https://doi.org/10.5281/zenodo.24528774)

