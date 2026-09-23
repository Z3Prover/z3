# CAV-style QF_FF paper and category comparisons

The updated [round-8 paper](../output/pdf/z3-qfff-cav-round8/paper.pdf) has ten
main-text pages, one reference page, and nine appendix pages. Its
[category figure](../output/pdf/z3-qfff-cav-round8/round8-benchmark-overview.png)
compares historical cvc5 1.3.4 with freshly paired Z3 policies on 1,248 paper
inputs and eight separate real-project queries. Z3 improves 886 to 888 solves
without coverage losses; summed common-solve time rises 0.45%. There are 29
cvc5-union-only cases in the paper subset. The current-main comparison remains
paused and is excluded from these totals.

The maintained LaTeX and compact evidence are in
[doc/papers/qf_ff](papers/qf_ff/README.md); figures can be regenerated without
rerunning solvers. The new default has not been measured on all 4,212 inputs.

## Historical complete-corpus report (previous Z3 default)


The [working paper](../output/pdf/z3-qfff-cav/paper.pdf) has ten pages of main
text in LNCS format, followed by references and five appendix pages. Authors:
Romain Soulat and Jean Frédéric Etienne, Input Output Group. It describes the
native integration, bounded algebra, preprocessing, theory combination,
interfaces, validation, experiments, and explicit limitations. It is not a
submitted or accepted paper.

The [overview figure](../output/pdf/z3-qfff-cav/benchmark-overview.pdf) groups all
4,212 distinct paper-artifact inputs and shows eight additional real-project
queries separately. The [interactive table](../output/pdf/z3-qfff-cav/benchmark-explorer.html)
can filter the complete input list to cvc5-only misses. CSV and editable LaTeX
are in the same output directory.

## Full round-7 binary coverage, 10 seconds

| Family | Inputs | cvc5 GB | cvc5 split | Z3+FF | cvc5 union only |
| --- | ---: | ---: | ---: | ---: | ---: |
| TV | 1,553 | 1,259 | 1,188 | 1,453 | 9 |
| TV-pureFF | 843 | 238 | 233 | 486 | 3 |
| CirC-D | 609 | 147 | 545 | 547 | 0 |
| CirC-S | 640 | 170 | 89 | 187 | 0 |
| QED2 | 100 | 37 | 59 | 71 | 3 |
| Seq | 100 | 11 | 100 | 100 | 0 |
| Small | 325 | 160 | 179 | 242 | 34 |
| ASHR | 32 | 0 | 32 | 31 | 1 |
| Examples | 10 | 10 | 9 | 9 | 1 |
| **Total** | **4,212** | **2,032** | **2,434** | **3,126** | **51** |

There are 552 Z3-only inputs and 1,035 inputs solved by none of these three
configurations. The cvc5 union is an oracle coverage diagnostic, not an
implemented solver portfolio. Of the 51 reference-only cases, 34 are in Small.
CirC-S is another important weak area: Z3 leads the comparison but still leaves
453/640 unresolved. Seven illustrative inputs were rerun after removing only the unsupported
`:incremental true` option. Six interface errors become successes; one timeout
remains. Original logs are preserved, and no other corpus input uses this option. No current Z3 run reaches the
sampled memory limit, but 1,086 time out. This is not evidence that basis growth
or memory use is no longer a concern.

All current Z3 rows use binary SHA-256
`14772994298957b7b5c9d402b7e830b6b542e48077fcf20d46845aeeb83f249e`.
We reused 1,118 exact-input/binary matches from round 7 and measured the remaining
3,094 inputs with the same 10-second/4-GiB/eight-worker protocol. cvc5 GB and
split reuse the historical **1.3.4** full-corpus pass, with the documented wrong
answer excluded. The three configurations were not newly interleaved, and this
is not a full-corpus comparison with cvc5 1.4.0.

All **1,295 current single-query SAT results** passed independent original-input
model evaluation (237 reused validations, 1,055 original replays, and three normalized-example replays). There are no
unresolved conflicting definite answers after the existing adjudication.
Models do not certify UNSAT; proof reconstruction remains unimplemented.

Raw current measurements and metadata are in
[`results/cav-overview`](../tests/finite_field/results/cav-overview/).
The [output README](../output/pdf/z3-qfff-cav/README.md) documents source data,
figure generation, reproduction, and remaining submission work. Historic reports
remain unchanged so their measurements retain their original meaning.
