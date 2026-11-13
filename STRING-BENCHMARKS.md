# String benchmarks in SMT-LIB format

Source survey dated **2026-11-13**. This report identifies public benchmark
sources and summarizes existing evidence; **no benchmarks were run**. Published
results below describe the cited artifacts and configurations, not the current
Z3 checkout or current cvc5 release.

## Summary

The best reproducible starting point is the versioned **SMT-LIB string library**,
with **SMT-COMP inputs and results** providing a directly matched published
comparison. Supplement it with application-derived collections, especially
mixed-theory and incremental workloads, and with targeted synthetic suites.
Solver regression tests are useful correctness inputs, but not an unbiased
performance sample.

There is no defensible universal ranking of Z3 and cvc5 from these sources.
On the cited SMT-COMP 2025 corpus, cvc5 solves more instances than Z3-alpha and
two of the listed Z3 base configurations; Z3-Noodler and Z3-Noodler-Mocha solve
substantially more than cvc5. These are **different solver implementations and
configurations**, not interchangeable names for stock Z3.

## 1. Versioned reference collections

### SMT-LIB benchmark library

- [Official benchmark index](https://smt-lib.org/benchmarks.shtml) and
  [release community](https://zenodo.org/communities/smt-lib).
- [SMT-LIB 2025 non-incremental release](https://zenodo.org/records/16740866),
  version 2025.08.04. Direct string-logic downloads:
  [QF_S.tar.zst](https://zenodo.org/records/16740866/files/QF_S.tar.zst?download=1),
  [QF_SLIA.tar.zst](https://zenodo.org/records/16740866/files/QF_SLIA.tar.zst?download=1),
  [QF_SNIA.tar.zst](https://zenodo.org/records/16740866/files/QF_SNIA.tar.zst?download=1).

These are actual archived SMT-LIB inputs, grouped by logic and contributor
family. `QF_S` covers quantifier-free strings/regular expressions;
`QF_SLIA` adds linear integer arithmetic, notably lengths and conversions;
`QF_SNIA` permits nonlinear integer arithmetic. The library combines
application-generated, crafted, and random inputs. Preserve family names and
the `:source`, `:category`, `:status`, and `:license` metadata rather than treating
the archive as one homogeneous workload. The release documents licensing per
benchmark and warns that extracted sizes can greatly exceed compressed sizes.

**Z3 versus cvc5:** the library is a source of inputs, not itself an experiment.
The competition results below apply to a selected, scrambled subset, not
necessarily every file in these archives. Application-family conclusions require
family-level results; aggregate logic scores cannot supply them.

### Exact SMT-COMP 2025 inputs

- [Dataset and checksums](https://zenodo.org/records/16887742).
- [Single-query archive](https://zenodo.org/records/16887742/files/single_query.tar.gz?download=1).
- The dataset also supplies separate incremental, model-validation, unsat-core,
  and parallel archives; their existence does not imply that every track contains
  string benchmarks.

The single-query archive contains the exact scrambled `.smt2` inputs used in the
competition. Retain the accompanying `.yml` files: they map scrambled filenames
back to original benchmark families and expected results. The dataset records
scrambling seed **757067271**. This is the preferred source for reproducing the
published scores, whereas the unscrambled SMT-LIB release is more convenient for
studying application provenance.

## 2. Application-derived and research-project collections

These sources expose the provenance behind many familiar string benchmark
families. Some overlap with each other and with SMT-LIB; they should not simply
be concatenated into a larger dataset.

| Source/project | Retrieval and format | Characteristics and comparison evidence |
| --- | --- | --- |
| **Kaluza / Kudzu** | Converted SMT-LIB inputs are in the [QF_SLIA release archive](https://zenodo.org/records/16740866/files/QF_SLIA.tar.zst?download=1); the [Reynolds family browser](https://explore.smt-lib.org/family/176.html) includes Kaluza and PyEx. An [individual record](https://explore.smt-lib.org/benchmark/243073.html) documents Kudzu provenance and conversion for CVC4. The [legacy Z3-str collection](https://github.com/z3str/Z3-str/tree/master/benchmark/1.kaluza) is a different dialect. | Tens of thousands of constraints originating in symbolic execution of real AJAX/JavaScript applications, mixing string operations and lengths. Original Kaluza syntax is not SMT-LIB: prefer the converted archive. Historical Z3seq/CVC4 results appear below; they do not measure cvc5. The individual record reports SAT for cvc5-fixed and Z3 4.8.11 in SMT-COMP 2021, but one input establishes no suite-wide ranking. |
| **PyEx** | [SMT-LIB family browser](https://explore.smt-lib.org/family/176.html) and QF_SLIA archive; also mirrored in the [Trau collection](https://github.com/plfm-iis/trauc_benchmarks). | Python symbolic-execution path constraints, with application string operations interacting with arithmetic. A large suite rather than a small hand-built solver example. Historical results favor CVC4 over the evaluated Z3seq configuration on coverage; do not relabel that as a cvc5 result. |
| **PISA and AppScan** | [PISA SMT2 files for CVC4](https://github.com/z3str/Z3-str/tree/master/benchmark/2.pisa/cvc4), [AppScan SMT2 files for CVC4](https://github.com/z3str/Z3-str/tree/master/benchmark/3.appscan/cvc4); [PISA example](https://github.com/z3str/Z3-str/blob/master/benchmark/2.pisa/cvc4/pisa-000.smt2). | Small security-analysis suites: 12 Java sanitizer constraints for PISA and eight security-warning constraints for AppScan. Substrings, containment, and index operations occur in PISA. The [Z3str3 paper](https://ar5iv.labs.arxiv.org/html/1704.07935#S4) reports a 20-second evaluation against CVC4: CVC4 times out on `pisa-008`, solved by Z3str3, and on one AppScan case. This is historical CVC4 evidence, not a modern cvc5 comparison. |
| **JOACO and Stranger** | [Authors' dataset page](https://ieee-dataport.org/documents/benchmark-suite-integrated-approach-effective-injection-vulnerability-analysis-web). Archives include SMT translations where supported, but not every original constraint is translatable. | Web injection/security analysis: JOACO draws on 11 Java web/security applications; the original Stranger suite has nine PHP-derived constraints. Download access is weaker than for Git repositories: IEEE requires login, and the alternative Drive links checked in this survey returned 404. The Z3str4 comparison uses only four Stranger cases and 94 JOACO cases; do not equate these counts with original applications or complete source suites. |
| **Trau / Z3-Trau collections, including SLOG, Django, BioPython** | [Benchmark repository](https://github.com/plfm-iis/trauc_benchmarks), [SLOG SMT2 files](https://github.com/plfm-iis/trauc_benchmarks/tree/master/slog), [Django SMT2 files](https://github.com/plfm-iis/trauc_benchmarks/tree/master/django_1). | A useful consolidated collection spanning Kaluza, PyEx, SLOG, and application-named Python families. Precise extraction provenance for the Django/BioPython subsets is not established by the repository alone. SLOG examples contain regex membership and may set solver-specific `:strings-exp`. The [original SLOG benchmark link](https://alcom.ee.ntu.edu.tw/src/tools.html) describes an ABC/BLIF-command subset, not an interchangeable SMT-LIB corpus. The repository README documents labels inferred from solver runs, sometimes from a single solver: treat these as provisional ground truth. Its documented comparison/labeling uses older CVC4 and Z3 revisions, not current cvc5. |
| **SCB Java-project corpus** | [Repository](https://github.com/iscas-projects/SCB), [actual Fastjson SMT2 input](https://github.com/iscas-projects/SCB/blob/master/fastjson/smt/method-com.alibaba.fastjson2.JSONBDump__dumpReference__1310106585/6065.smt2), [per-file result metadata](https://raw.githubusercontent.com/iscas-projects/SCB/master/fastjson/simple_statistics.json). | Application path-condition corpora from Fastjson, Apache Commons, Gson, Hibernate, Tomcat, and other Java projects. Actual `.smt2` files are browsable despite JAR-oriented packaging described in the README. Examples encode Java string equality and [String.length() using str.len](https://github.com/iscas-projects/SCB/blob/master/fastjson/smt/method-com.alibaba.fastjson2.internal.asm.MethodWriter__visitLdcInsn__1951126586/3133.smt2). Mixed constraints can use `ALL`, uninterpreted functions, and model/unsat-core requests, so filter for actual string operations rather than assuming every file is a string workload. Results name **Z3, cvc5, Z3-Noodler, and OSTRICH**, but do not establish sufficiently specified versions and conditions for a trustworthy aggregate ranking. On the linked length example both return UNSAT, followed by unavailable-model errors: distinguish solving from subsequent command failures. No corpus license was apparent in the inspected repository listing; verify redistribution permission. |
| **OSTRICH tests** | [SMT2 test repository](https://github.com/uuverifiers/ostrich/tree/master/tests), [input-format documentation](https://github.com/uuverifiers/ostrich/blob/master/README.md). | Targeted regex, replacement, and string-operation examples useful alongside application collections. This is a regression suite, not a uniformly application-derived corpus. Some files use nonstandard transducer syntax, for example [transducer1.smt2](https://github.com/uuverifiers/ostrich/blob/master/tests/transducer1.smt2), and cannot be assumed portable to Z3/cvc5. For comparable standard inputs, the official competition results provide stronger evidence than this test directory alone. |

### Historical application-suite comparison: Z3str4 evaluation

The [Z3str4 evaluation site](https://z3str4.github.io/) and
[paper](https://doi.org/10.1007/978-3-030-90870-6_21) compare Z3str4,
Z3seq, Z3str3, and **CVC4 1.8**, not cvc5. The site identifies the underlying
Z3 revision as
[`7e7360d`](https://github.com/Z3Prover/z3/commit/7e7360dd0c04cdee95c3f74a59908209742c5212).
The paper uses a **20-second per-instance limit**. The supplementary tables label
the count `Cor. class. (contr.)`: the parenthesized contribution is separate from
the correct-classification count reproduced here; `Tot. inst.` is the denominator.
For application suites:

| Evaluated suite | Inputs | CVC4 1.8 | Z3seq | Z3str4 |
| --- | ---: | ---: | ---: | ---: |
| Kaluza | 47,284 | 44,215 | 45,431 | 45,444 |
| PyEx | 25,421 | 24,777 | 24,099 | 24,483 |
| JOACO | 94 | 94 | 94 | 94 |
| Stranger subset | 4 | 4 | 4 | 4 |

This illustrates family dependence: the evaluated Z3seq configuration covers
more Kaluza inputs, while CVC4 covers more PyEx inputs. It does **not** establish
how current Z3 compares with current cvc5. The evaluation's linked reproduction
archive timed out during checking, so its present retrievability is uncertain;
use the independently linked source collections above where available.

## 3. Newer application and targeted submissions

The [SMT-LIB submission repository](https://github.com/SMT-LIB/benchmark-submission)
provides browsable `.smt2` files submitted for the 2026 release. Its contents are
mutable; pin a commit for a later experiment. Submission availability is not a
claim that a family was used in the 2025 competition.

| Source and retrieval | Characteristics | Z3/cvc5 comparison evidence |
| --- | --- | --- |
| **ELSTER / mgm A12 Test Data Generator**: [non-incremental files](https://github.com/SMT-LIB/benchmark-submission/tree/main/non-incremental/QF_SNIA/20260619-elster), [incremental files](https://github.com/SMT-LIB/benchmark-submission/tree/main/incremental/QF_SNIA/20260619-elster), [example with provenance](https://raw.githubusercontent.com/SMT-LIB/benchmark-submission/main/non-incremental/QF_SNIA/20260619-elster/type1/A.smt2) | Industrial German tax-form test-data generation. Strings are part of a larger Boolean/integer form model, not an isolated word-equation exercise. The example capital-gains form has 270 variables and 252 base constraints. Incremental variants add control constraints for high-coverage data, including extremal values. Files are labeled `QF_SNIA`; the inspected `type1` example restricts multiplication/division/modulo to constant factors/divisors, so the logic label alone overstates its nonlinearity. | Headers explicitly name **Z3 and CVC5** as targets. No comparative performance results were established in this survey. Keep incremental sessions separate from single-query measurements. |
| **StringRegexesLengthToInt**: [REln and RElnc files](https://github.com/SMT-LIB/benchmark-submission/tree/main/non-incremental/QF_SLIA/20260219-StringRegexesLengthToInt), [example header/input](https://raw.githubusercontent.com/SMT-LIB/benchmark-submission/main/non-incremental/QF_SLIA/20260219-StringRegexesLengthToInt/REln/long/benchmark_long_v1_w02_n01.smt2) | Generated regular-language membership combined with linear constraints over `str.len` and `str.to_int`. The source description distinguishes random, long-string, and `z3-hard` categories; long cases require lengths of at least about 1,000. Useful for interaction between regular languages and arithmetic rather than concatenation alone. | Headers target **CVC5 and Z3-Noodler** and state a 60-second limit. The `z3-hard` category was selected for failure to solve within 10 seconds on the author's machine: this is selection bias, not evidence that cvc5 wins. Inspected status is `unknown`; no complete head-to-head table was established. |
| **Post Correspondence Problem (PCP)**: [pcp-3-4-hard files](https://github.com/SMT-LIB/benchmark-submission/tree/main/non-incremental/QF_S/20260625-pcp-string/pcp-3-4-hard), [example with provenance and witness](https://raw.githubusercontent.com/SMT-LIB/benchmark-submission/main/non-incremental/QF_S/20260625-pcp-string/pcp-3-4-hard/unsolved_pcp_instance_1829.smt2) | Hard PCP instances encoded as string constraints, including regular-language constraints and replacement-based encodings. The inspected input is marked SAT and includes a witness in its source metadata. A mathematical search workload, not representative web-form validation. | Headers name **cvc5, Z3, and OSTRICH**, with a 60-second limit, but do not supply a comparative result table. Historical difficulty of the underlying PCP instances does not establish solver timeouts on these encodings. |

The inspected submission headers specify CC BY 4.0. Consult individual files
before redistributing a combined collection.

## 4. Generators and solver regression inputs

### StringFuzz

[Repository and retrieval](https://github.com/dblotsky/stringfuzz);
[CAV 2018 paper](https://doi.org/10.1007/978-3-319-96142-2_6).

StringFuzz generates and transforms SMT-LIB 2.x string/regular-expression
instances. Its generators include concatenation depth, equality, lengths,
overlaps, regexes, and random ASTs/text; transformations can perturb existing
instances. The README explicitly demonstrates feeding output to Z3str3.
This is primarily a **generator**, not a frozen downloadable performance corpus.
Record its revision, parameters, random seeds, and output dialect if later used.
Older string dialects may need conversion to current SMT-LIB.

**Z3 versus cvc5:** the 2018 work predates cvc5; it cannot establish a current
cvc5 comparison. This source is useful for controlled stress tests and robustness
testing, but generated successes or failures should not be extrapolated to
application performance. No generation or solver execution was performed here.

### Z3 and cvc5 regression repositories

- **Z3:** [z3test SMT2 regressions](https://github.com/Z3Prover/z3test/tree/master/regressions/smt2);
  for example [string-ops.smt2](https://raw.githubusercontent.com/Z3Prover/z3test/master/regressions/smt2/string-ops.smt2).
  Inputs cover string operations, arithmetic interactions, models, and incremental
  checks. The example also uses Z3-specific commands/options and `seq.*` operators:
  it is not directly a portable standard-string benchmark.
- **cvc5:** [regress0 string inputs](https://github.com/cvc5/cvc5/tree/main/test/regress/cli/regress0/strings);
  further string inputs occur under other regression levels. An illustrative
  [standard-operator case](https://raw.githubusercontent.com/cvc5/cvc5/main/test/regress/cli/regress0/strings/652-substr-len-norm.smt2)
  combines `str.at`, `str.to_int`, and regex membership, with an expected UNSAT
  result. Inspect harness directives for required options and expected output.

**Z3 versus cvc5:** these are deliberately solver-specific correctness samples,
often reduced from bugs. Neither repository provides an unbiased cross-solver
performance ranking. Portable subsets can later test semantic agreement;
extensions, disabled files, and multi-check sessions must be handled separately.

## 5. Published comparison: SMT-COMP 2025

Sources: [division results](https://smt-comp.github.io/2025/results/qf_strings-single-query/),
[QF_S](https://smt-comp.github.io/2025/results/qf_s-single-query/),
[QF_SLIA](https://smt-comp.github.io/2025/results/qf_slia-single-query/),
[QF_SNIA](https://smt-comp.github.io/2025/results/qf_snia-single-query/),
and [participants, solver archives, and system descriptions](https://smt-comp.github.io/2025/participants/).

The single-query division contains **34,228** benchmarks: **10,428 QF_S**,
**23,730 QF_SLIA**, and **70 QF_SNIA**, with a **1,200-second** time limit.
The following are the published **Solved counts in the Parallel Performance
table of the Single Query Track**, not the separate Parallel Track and not the
competition's sequential scoring adjustments.

| Entrant/configuration | QF_S | QF_SLIA | QF_SNIA | Total solved |
| --- | ---: | ---: | ---: | ---: |
| cvc5 | 9,016 | 21,585 | 70 | 30,671 |
| Z3-alpha | 8,950 | 20,504 | 70 | 29,524 |
| Z3-alpha-base (non-competing) | 8,953 | 20,398 | 70 | 29,421 |
| Z3-Noodler-base (non-competing) | 8,962 | 20,391 | 0 | 29,353 |
| Z3-Noodler | 9,943 | 23,622 | 70 | 33,635 |
| Z3-Noodler-Mocha | 10,414 | 23,626 | 70 | 34,110 |
| OSTRICH | 9,810 | 22,901 | 70 | 32,781 |

Interpretation:

- **cvc5 versus Z3-related entrants:** cvc5 solves 1,147 more than Z3-alpha,
  while Z3-Noodler and Z3-Noodler-Mocha solve 2,964 and 3,439 more than cvc5,
  respectively. Noodler/Mocha are specialized implementations, not measurements
  of the current stock Z3 string engine. The different `-base` rows also cannot
  be collapsed into one generic "Z3" result; their revisions/options matter.
- **Timeout matters:** at the published 24-second cutoff, Z3-alpha solves
  **28,480**, versus cvc5's **28,267**. Thus even the relative aggregate coverage
  of those two entrants reverses at a shorter cutoff.
- **SAT versus UNSAT matters:** at the full limit, cvc5 solves **20,275 SAT**
  and **10,396 UNSAT** cases; Z3-alpha solves **19,113 SAT** and **10,411 UNSAT**.
  The overall cvc5 coverage lead is not an UNSAT coverage lead.
- **Mixed arithmetic needs more data:** all competing entrants in the table
  solve all 70 QF_SNIA cases, all SAT. cvc5 has the best published time score
  there, but such a small, SAT-only sample says little about general nonlinear
  string/arithmetic workloads or the newer ELSTER family.
- **Do not infer a speedup from summed times.** Different solved sets,
  configurations, and competition scoring prevent a clean per-instance
  speed comparison. Use matched-instance results for that purpose.

For historical context, the [2024 division results](https://smt-comp.github.io/2024/results/qf_strings-single-query/)
report 32,195 solved by Z3-Noodler, 30,457 by cvc5, and 29,647 by Z3-alpha
on 32,659 inputs at the same nominal time limit. This supports a repeated
Noodler coverage advantage on those competition samples, **not** a longitudinal
speedup claim: both the corpus and solver artifacts changed.

## 6. Conditions for a later benchmark study

No experiment is proposed as already performed. Before drawing new conclusions:

1. Pin archive versions, repository commits, solver binaries, options, timeout,
   memory limit, and thread count. Treat stock Z3, its alternative string
   configurations, and external Z3-based solvers as separate configurations.
2. Deduplicate overlapping research collections and SMT-LIB copies. Preserve
   application/family labels and report both family-level and aggregate results;
   thousands of closely related generated queries can dominate totals.
3. Check SMT-LIB dialect and character semantics. Legacy solver syntax,
   byte-oriented encodings, Unicode handling, regex/replacement extensions,
   string-to-integer corner cases, and solver-specific options can change either
   acceptance or meaning. Preserve originals and document any conversion.
4. Separate single-query from incremental sessions, SAT from UNSAT, known from
   unknown status, and unsupported/parse-error/unknown outcomes from timeouts.
   Validate returned models or disputed answers where possible.
5. Include mixed application workloads, not just string-focused logics; the
   presence of strings does not imply that string reasoning dominates runtime.

Links above identify public landing pages, repositories, source files, and
advertised archive downloads. Large archives were not downloaded or executed
for this survey. Where no family-specific Z3/cvc5 comparison was established,
that absence is stated rather than replaced by a prediction.
