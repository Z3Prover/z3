#!/usr/bin/env python3
"""Generate the two-page LaTeX paper comparison and vector benchmark plots."""
import argparse
import collections
import json
import math
import statistics
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
from artifact_analysis import LABELS, SOLVED, family, load, summarize

NAMES = {'z3': 'Z3 + FF branch', 'cvc5': 'cvc5 / GB', 'cvc5_split': 'cvc5 / split'}
COLORS = {'z3': '#0072B2', 'cvc5': '#D55E00', 'cvc5_split': '#009E73'}
STYLES = {'z3': '-', 'cvc5': '--', 'cvc5_split': '-.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('results', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--draft', action='store_true')
    args = ap.parse_args()
    summary = summarize(args.results, args.draft)
    manifest, members, runs = load(args.results)
    args.out.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'font.family': 'serif', 'font.size': 9, 'axes.labelsize': 9,
                         'legend.fontsize': 8, 'xtick.labelsize': 8, 'ytick.labelsize': 8,
                         'pdf.fonttype': 42, 'axes.spines.top': False, 'axes.spines.right': False})
    fig, axes = plt.subplots(1, 2, figsize=(7.1, 2.25), constrained_layout=True)
    for label in LABELS:
        times = sorted(a[label]['seconds'] for a in runs.values() if label in a and a[label]['result'] in SOLVED)
        axes[0].plot(range(1,len(times)+1), times, label=NAMES[label], color=COLORS[label], linestyle=STYLES[label], linewidth=1.7)
        ratios = []
        for a in runs.values():
            if label not in a or a[label]['result'] not in SOLVED: continue
            best = min(r['seconds'] for r in a.values() if r['result'] in SOLVED)
            ratios.append(a[label]['seconds']/best)
        x = np.geomspace(1, 100, 180)
        axes[1].plot(x, [sum(r <= t for r in ratios)/len(members) for t in x],
                     color=COLORS[label], linestyle=STYLES[label], linewidth=1.7, label=NAMES[label])
    axes[0].set(xlabel='Number of solved inputs (sorted)', ylabel='Per-input wall time (s)', yscale='log', ylim=(.001, 12), title='(a) Cactus: time to solve each input')
    axes[0].legend(loc='upper left', frameon=False)
    axes[1].set(xlabel='Runtime / fastest successful solver', ylabel='Fraction of all inputs', xscale='log', xlim=(1,100), ylim=(0,1), title='(b) Performance profile')
    for ax in axes: ax.grid(alpha=.2, which='major')
    fig.savefig(args.out/'overview.pdf'); plt.close(fig)
    fig, axes = plt.subplots(1, 2, figsize=(7.1, 2.3), constrained_layout=True)
    for ax, ref in zip(axes, LABELS[1:]):
        for both in [True, False]:
            pairs = [(a['z3'],a[ref]) for a in runs.values() if 'z3' in a and ref in a
                     and (a['z3']['result'] in SOLVED and a[ref]['result'] in SOLVED) == both]
            xs = [a['seconds'] if a['result'] in SOLVED else 20 for a,b in pairs]
            ys = [b['seconds'] if b['result'] in SOLVED else 20 for a,b in pairs]
            ax.scatter(xs, ys, s=7 if both else 11, alpha=.3 if both else .45,
                       color=COLORS[ref] if both else '#555555', marker='o' if both else 'x', linewidths=.5)
        ax.plot([.001,25], [.001,25], color='#555555', linewidth=.7)
        ax.axvline(10, color='#999999', linestyle=':', linewidth=.8); ax.axhline(10, color='#999999', linestyle=':', linewidth=.8)
        ax.set(xscale='log', yscale='log', xlim=(.001,26), ylim=(.001,26), xlabel='Z3 + FF branch (s)', ylabel=NAMES[ref]+' (s)')
        ax.set_xticks([.001,.01,.1,1,10,20], ['.001','.01','.1','1','10','U'])
        ax.set_yticks([.001,.01,.1,1,10,20], ['.001','.01','.1','1','10','U'])
        ax.grid(alpha=.15)
    fig.savefig(args.out/'scatter.pdf'); plt.close(fig)

    def esc(s):
        for a,b in [('_',r'\_'),('&',r'\&'),('%',r'\%')]: s=s.replace(a,b)
        return s
    aggregate = []
    for label in LABELS:
        x=summary['total'][label]; c=x['counts']
        aggregate.append(f"{esc(NAMES[label])} & {x['solved']:,} & {c.get('sat',0):,} & {c.get('unsat',0):,} & {c.get('timeout',0):,} & {c.get('memout',0):,} & {c.get('unknown',0)+c.get('error',0):,} & {c.get('wrong',0):,} & {x['par2_mean']:.2f} " + r'\\')
    family_rows=[]
    for name, row in summary['families'].items():
        family_rows.append(f"{esc(name)} & {row['n']:,} & "+' & '.join(f"{row[k]['solved']:,}" for k in LABELS)+r' \\')
    paper_rows=[]
    for paper in ['CAV23','CAV23-main','CAV24','CAV24-main','FMCAD26','FMCAD26-UNSAT']:
        row=summary['papers'][paper]
        count = {'FMCAD26-UNSAT':408,'CAV24-main':1140,'CAV23-main':2106}.get(paper, sum(e['paper']==paper for e in manifest['entries']))
        paper_rows.append(f"{esc(paper)} & {count:,} & {row['n']:,} & "+' & '.join(f"{row[k]['solved']:,}" for k in LABELS)+r' \\')
    large = summary['field_sizes']['large (>=128 bits)']
    large_summary = (f"On {large['n']:,} inputs with fields of at least 128 bits, "
                     f"Z3 solves {large['z3']['solved']:,}, GB {large['cvc5']['solved']:,}, "
                     f"and split {large['cvc5_split']['solved']:,}.")
    macros = '\n'.join([r'\newcommand{\LargeFieldSummary}{'+large_summary+'}',
                         r'\newcommand{\AggregateRows}{'+'\n'.join(aggregate)+'}',
                         r'\newcommand{\FamilyRows}{'+'\n'.join(family_rows)+'}',
                         r'\newcommand{\PaperRows}{'+'\n'.join(paper_rows)+'}'])
    (args.out/'tables.tex').write_text(macros+'\n')
    if args.draft:
        finding = r'\textbf{Layout draft: measurements are incomplete.} This document is not a benchmark conclusion.'
    else:
        finding_path=args.results/'findings.tex'
        assert finding_path.exists(), 'write evidence-based findings after reviewing complete results'
        finding=finding_path.read_text()
    (args.out/'findings.tex').write_text(finding+'\n')
    details_path=args.results/'details.tex'
    (args.out/'details.tex').write_text(details_path.read_text() if details_path.exists() else 'Follow-up measurements and validation are pending.\n')
    tex=r'''\documentclass[10pt,a4paper]{article}
\usepackage[margin=18mm]{geometry}
\usepackage[T1]{fontenc}\usepackage{lmodern}
\usepackage{graphicx,booktabs,array,xcolor,hyperref}
\hypersetup{colorlinks=true,urlcolor=blue,pdftitle={Finite-field SMT: Z3 branch versus cvc5}}
\setlength{\parindent}{0pt}\setlength{\parskip}{5pt}
\setlength{\tabcolsep}{7pt}
\newcommand{\heading}[1]{\vspace{3pt}{\large\bfseries #1}\par}
\input{tables.tex}
\begin{document}
{\LARGE\bfseries Finite-field SMT: Z3 branch versus cvc5}\par
{\small CAV 2023, CAV 2024 and FMCAD 2026 public artifacts\hfill 22 September 2026}
\vspace{4pt}\hrule\vspace{5pt}
\input{findings.tex}

\heading{Scope and protocol}
All 6,423 finite-field SMT files in the three artifacts' benchmark suites and
illustrative examples are covered: 4,212 byte-distinct inputs, with shared inputs
run once. This is a comparison of the current \texttt{codex/qf-ff} branch and
cvc5 1.3.4 (CoCoA-enabled), using its default GB and split backends.
Z3 uses a Release build without GMP. Proof generation is disabled.
Eight single-process workers run on an Apple M2
Max (12 cores, 64 GiB; macOS). Every run has a 10 s wall-clock limit and a 4 GiB
RSS limit, sampled every 50 ms; sampling permits memory overshoots. Fresh-process
timings include parsing. Input order is seeded; solver order rotates. No CPU
affinity is imposed. Timing stability is checked separately with isolated repetitions.

\texttt{QF\_BVFF} is renamed to \texttt{ALL} for both solvers on 640 mixed-theory
inputs; assertions are unchanged. The 2,304 alternate BV/NIA encodings and 640
CirC intermediate-format completeness inputs are catalogued but outside this
finite-field SMT comparison. The nested CAV 2024 archive adds only duplicate inputs.

\begin{center}\small
\begin{tabular}{lrrrrr}\toprule
Artifact & Files & Unique & Z3 solved & GB solved & Split solved\\\midrule
\PaperRows
\bottomrule\end{tabular}
\end{center}
{\footnotesize Artifact rows overlap; ``main'' uses the paper experiment lists shipped
in each artifact. The FMCAD subset has 408 files but 390 distinct
inputs; all FMCAD inputs are already present in the CAV archives. ``Full'' refers
to input coverage, not reproduction of the original 300 s (CAV) or 1,200 s (FMCAD) budgets.}

\heading{Pooled results on distinct inputs}
\begin{center}\small
\begin{tabular}{lrrrrrrrr}\toprule
Solver & Solved & SAT & UNSAT & Time & Mem. & Other & Wrong & PAR-2 (s)\\\midrule
\AggregateRows
\bottomrule\end{tabular}
\end{center}
{\footnotesize Time/Mem. denote time/memory limits; Other denotes unknown/error.
Wrong denotes independently refuted answers, excluded from Solved, which includes
successful multi-query examples. PAR-2 uses measured wall time
for successful runs and 20 s for every failure; lower is better.}

\begin{center}\includegraphics[width=\linewidth]{overview.pdf}\end{center}
{\footnotesize Cactus curves contain successful runs only. Performance profiles
use all 4,212 inputs as denominator; failures have infinite ratios. Both figures
show the eight-worker coverage pass, not isolated microbenchmarks.}
\newpage
\heading{Where the difference comes from}
\begin{minipage}[t]{.50\linewidth}\vspace{0pt}\small
\begin{tabular}{lrrrr}\toprule
Family & Inputs & Z3 & GB & Split\\\midrule
\FamilyRows
\bottomrule\end{tabular}
\end{minipage}\hfill
\begin{minipage}[t]{.46\linewidth}\vspace{0pt}\small
TV: compiler translation validation. TV-pureFF: its alternate pure-field encoding.
CirC-D: operator determinism. CirC-S: mixed BV/field soundness. QED2: circomlib
determinism. Seq: bit-sum sequences. Small: small-field polynomial systems.
ASHR: extended arithmetic-shift instances. Families are disjoint after deduplication;
examples duplicated by experimental inputs inherit their experimental family.
\par\vspace{5pt}\LargeFieldSummary
\end{minipage}

\begin{center}\includegraphics[width=\linewidth]{scatter.pdf}\end{center}
{\footnotesize Each point is one distinct input. Above the diagonal favors Z3;
below favors cvc5. U is a failed run (timeout, memory limit, unknown, error or wrong answer),
placed beyond the 10 s boundary rather than assigned a fictitious runtime.
Overlapping points are translucent.}

\input{details.tex}

\heading{Interpretation and reproducibility}
These are local measurements with current binaries, not the papers' original
hardware, solver revisions, or timeout budgets. A single coverage repetition and
concurrent workers limit fine-grained timing claims; the isolated follow-up
addresses measurement stability on its stated sample only. SAT-model checking
and cross-solver agreement provide evidence, not an UNSAT certificate. No claim
of proof-production parity is made.

The accompanying manifest, per-run JSONL/CSV, binary hashes, commands, validation
results and scripts make the comparison auditable. Z3 is an experimental branch,
not an upstream release. No generated circuits or separately weighted benchmark
samples are added to the corpus.

{\footnotesize\textbf{Public sources.}
[1] Ozdemir et al., \emph{Satisfiability Modulo Finite Fields}, CAV 2023,
\href{https://zenodo.org/records/7865471}{doi:10.5281/zenodo.7865471}.
[2] Ozdemir et al., \emph{Split Groebner Bases for Satisfiability Modulo Finite Fields},
CAV 2024, \href{https://zenodo.org/records/10917330}{doi:10.5281/zenodo.10917330}.
[3] Saccomani et al., \emph{Proof Production for Satisfiability Modulo Finite Fields
with Proof Checking in Pacheck and Lean}, FMCAD 2026,
\href{https://zenodo.org/records/20133205}{doi:10.5281/zenodo.20133205}.
All retrieved 22 September 2026.}
\end{document}
'''
    (args.out/'comparison.tex').write_text(tex)
    (args.out/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print('LaTeX and vector figures written to', args.out)


if __name__ == '__main__': main()
