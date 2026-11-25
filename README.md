# Odd Zeta Five · B40a

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24528775.svg)](https://doi.org/10.5281/zenodo.24528775)

At least one of **ζ(7), ζ(9), ζ(11), ζ(13), ζ(15)** is irrational. The root module `OddZetaFive.lean` imports the theorem in its original namespace. The real part refers to Mathlib's complex Riemann zeta function evaluated at a positive integer.

```lean
OddZetaSix.B40a.exists_irrational_riemannZeta_seven_to_fifteen :
  ∃ s ∈ ({7, 9, 11, 13, 15} : Finset ℕ), Irrational ((riemannZeta (s : ℂ)).re)
```

The proof uses one native computation to bound the cost of 1,375 arithmetic rows. Its exact contribution is recorded below. The [paper](paper/odd_zeta_five_b40a.pdf) and [LaTeX source](paper/odd_zeta_five_b40a.tex) describe the construction.

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

The Python verifier uses only the standard library. It recomputes row costs, upward rounding, row coverage, the upper-prime integral, the circle energy lower bound, the continuous panel bounds and the ray budget. It uses exact integers and fractions and bounds logarithms using the neighboring decimal numbers around a correctly rounded result. CI independently regenerates the 72 Lean data files from `b40a/certificate.json` and compares them with the checked-in sources. The release run gives C ≤ 6.140423661027 before the PNT margin. [Numerical transcript](reports/certificate.log)

## Axiom audit

The following is the release run of `#print axioms`.

```text
'OddZetaSix.B40a.exists_irrational_riemannZeta_seven_to_fifteen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 OddZetaSix.B40a.Cert.Native.middle_rows_checked._native.native_decide.ax_1_1]
```

The additional axiom is the Boolean result used by `Cert.Native.middle_rows_checked`. The source is `OddZetaSix/B40a/Certificate/ArithmeticNativeAudit.lean`. The private `budget` proof in `Arithmetic/MiddleBandRate.lean` applies it to the middle sum, which flows into `content_arithmetic_exp` and the main theorem. The exact-set check rejects sorryAx and any additional axiom. It also checks the analytic rate, the specialized determinant valuation, and the upper- and lower-prime-band rates separately. The independent Python result corroborates the finite inequality; Lean's proof still trusts its native compiler at this point. [Full axiom output](reports/axioms.log)

A performance pilot on the first 32-row shard preselected a fold index for each row and computed one candidate cost with lists. Lean was invoked with one thread and a 4,096 MiB memory limit. The process was terminated at the 120-second wall-clock limit. The pilot did not run the remaining 42 shards or change the shipped proof. The timed file and the transcript are included for inspection. [Pilot source](reports/Middle000-pilot.lean) · [Pilot log](reports/kernel-pilot.log)

## Build and dependency provenance

The local release run used Lean 4.34.0-rc2 (compiler revision `6a10ac8c22beadecabdbb0919c2b50214762f91d`) on Windows x86-64. The project started without compiled artifacts for either this repository or its vendored PNT package. The nine pinned third-party Git checkouts and their previously compiled dependencies were reused from a matching local cache. An initial Windows pass hit sharing error 32 on a cached Mathlib artifact while the temporary dependency copy was being compressed. After compression stopped, the affected PNT target built successfully. The final full-package command reused completed jobs and rechecked the finished sources. CI is configured to fetch dependencies on a fresh Ubuntu runner and publish the full build and audit logs. [Local build log](reports/lake-build.log) · [Dependency verification](reports/dependencies.log) · [CI workflow](.github/workflows/ci.yml)

Stage 4's earlier Linux logs report “has local changes”. In this version of Lake the warning follows a nonzero result from `git diff --exit-code HEAD`. The earlier archive contains a source comparison reporting 9,233 Mathlib files and files in the other eight packages identical to the pinned archives. It omits the old Git index, status, and diff; the specific paths or cause of the historical warning cannot be recovered from it. This release checks each checkout's HEAD against the manifest and requires an empty porcelain status. It also compares the actual bytes of every tracked Lean source to its pinned Git blob (allowing checkout line-ending conversion); 9,055 Mathlib Lean files matched. The archived Mathlib commit is `dc4b8d60d5edb3c493c3662126b1b7ccae7d67cf`.

The local `PNTDependency` is a separate source package. It vendors selected code from PrimeNumberTheoremAnd (`c39a751132c88b6e8080b74c74023fd95b3d8be0`) and LeanArchitect (`468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`), with documented source selection, pruning and a Wiener compatibility edit. The revision checks for the nine external packages are distinct from the hash checks for 22 vendored module entries. [PNT source provenance](PNTDependency/provenance.json) · [Third-party notices](PNTDependency/licenses/)

## Citing and archiving the release

Version **1.0.0** is authored by **JanaHesse580** (<JanaHesse580@gmail.com>). The root license is MIT. Vendored licenses and attribution accompany their sources. The LaTeX paper builds with `tectonic paper/odd_zeta_five_b40a.tex` or two passes of pdfLaTeX in the paper directory. [Citation metadata](CITATION.cff) · [License](LICENSE)

For GitHub, unpack the repository contents so that this README, `lakefile.toml` and `.github/` are at the repository root. A Windows script checks the files and can push the initial commit to a public GitHub repository. To archive version 1.0.0, enable the repository in Zenodo's GitHub integration before publishing the corresponding GitHub Release. Zenodo issues the DOI when archiving succeeds. [Windows push script](scripts/push-github.ps1) · [Zenodo's GitHub integration](https://help.zenodo.org/docs/github/)

