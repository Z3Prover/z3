# F* audit of PR #11372 @ ad556e7f7128735f3c436b26893afeed5aa9bb2a

Base 02f6a7e144ed5ce81ab07a1373fd667c60ead0c2. Sources read via contents API at head: src/opt/optsmt.cpp (sha256 6db97c07...9735; get_base_model L743-750, lex L752-, box call L961, get_model L991-995, reset L1040-1050), src/opt/opt_context.cpp (sha256 4a5e41fa...5ee6; get_labels L236, initial check L390-392, get_base_model L449, execute_min_max L554).

## Intended property
When optsmt reports its best model, the labels returned by optsmt::get_model are those of that same model, including when the search never improves on the base model.

## Obligations (all proved)
- O1: seeding (best:=context m_model, labels:=context m_labels), given the context invariant labels = labels_of(m_model) established at opt_context.cpp L391-392, yields a paired state.
- O2: an improvement step (m_best_model=m_model; get_labels) preserves pairing.
- O3: after seeding and any sequence of improvements, the result (what get_model returns) is paired.
- Witness (model-level): old seeding with empty optsmt labels and no improvement is unpaired; new seeding is paired. This reproduces the bug the PR fixes, not a defect in the PR.

## Mapping
st = (m_best_model, optsmt::m_labels); ctx = (context::m_model, context::m_labels); labels_of is an arbitrary function (universally quantified, no axioms). base_old/base_new = old/new seeding; improve = the labelled-update sites (L352, L637, L712, L90).

## Assumptions (manually reviewed, not mechanized)
- context::m_model and m_labels are set together at the initial check and not changed between that and optsmt::lex/box (read from source, other writers L562, L575, L651 not traced exhaustively).
- Every model-improving site updates m_labels together with m_best_model; improvement sites other than those listed were not exhaustively checked.
- Reachability of the old bug is established only by the PR description/test, which was not executed.
- Base modules: none imported; standard F* library only.

## Exclusions
src/test/opt_bounds.cpp new test (not audited); symba_opt/geometric paths that return before or bypass get_base_model; non-lex/box callers; later model fixing (fix_model) and its interaction with labels; header declaration (private method, plumbing); memory safety and C++ execution.

## Versions and reproduction
F* 2026.09.27; Z3 4.13.3 (pinned backend). Command:
timeout 120 /tmp/gh-aw/fstar/bin/fstar.exe --smt /tmp/gh-aw/fstar/lib/fstar/z3-4.13.3/bin/z3 --z3version 4.13.3 --include /home/runner/work/z3/z3/fstar --z3rlimit 10 --cache_dir cache --odir out OptLabelsAudit.fst

Exit code 0.