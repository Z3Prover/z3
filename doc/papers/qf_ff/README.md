# QF_FF integration paper: measured round-8 update

Editable source: `paper.tex`. Authors: Romain Soulat and Jean Frédéric Etienne,
Input Output Group. LNCS working draft, not a submitted or accepted paper.
The generated PDF has 10 main-text pages, one reference page, and nine appendix
pages. Generated files are placed under `output/pdf/z3-qfff-cav-round8`.

## What the update measures

- Fresh paired Z3 study: 1,256 inputs, 886 previous-default versus 888 new-policy
  successes, two gains, zero losses, +0.45% summed common-solve time.
- The 1,248 paper inputs account for 883 versus 885 Z3 successes. Historical
  cvc5 1.3.4 solves 466 (GB) and 713 (split) on exactly those inputs. There are
  29 cvc5-union-only cases left in this subset.
- Eight real-project queries are separate diagnostics: Z3 solves 3/8 under
  both policies; historical cvc5 solves 0/8.
- The previous complete 4,212-input comparison stays explicitly historical.
  No missing new-default rows are filled with previous-default results.
- cvc5 1.4.0/main correctness rechecks are not a full performance comparison.
  The paused current-main campaign is excluded from the aggregate figures.

The broad candidate runs use the frozen experimental binary with model search
explicitly enabled. The final retained build makes that setting the public
default and was checked with regression suites and representative replays.
Both identities are recorded; they are not silently treated as one binary.

## Rebuild without running solvers

Use Python with Matplotlib and NumPy, plus a standard TeX installation with
pdfLaTeX and BibTeX. From the repository root:

```sh
python3 tests/finite_field/build_cav_round8.py
cd output/pdf/z3-qfff-cav-round8
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The script checks unique input/configuration rows, exact input identities,
definite-answer agreement, and expected coverage. It produces the category
heatmap, paired cactus/scatter, historical-reference profile, isolated medians,
CSV, summary JSON, and table macros. Raw measurements are never overwritten.
The `evidence.zip` archive includes frozen reference rows, paired run records,
metadata, SAT validations, regression records, and the earlier complete-corpus
assets. It includes no executable solver and performs no network access.

`paper.tex` is the maintained document source. The earlier full-corpus numeric
macros and figures are frozen inside the evidence archive; the new subset
figures and table are recomputed from measured rows. Changing the evaluated
population requires updating the evidence and all corresponding textual claims.

## Evidence and limitations

All 559 primary SAT model replays validate. No independent UNSAT certificate
is produced. The aggregate improvement includes two confirmed short-case
slowdowns; isolated results are shown rather than hidden. The new confirmation
cohort is selected by hash, not an untouched external generator.

Full local journals and exact input/source archives are preserved in
`tests/finite_field/results/performance-round8` and the earlier evidence
folders. Those large files are outside the source commits. The compact archive
supports document regeneration, not a claim that the entire external benchmark
corpus or build environment has been published.

The bundled LNCS class and bibliography style preserve their original headers.
See `LNCS-README.md` for provenance.
