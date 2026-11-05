// Extract of optsmt::get_base_model (src/opt/optsmt.cpp at b238a89f, lines 742-750):
//   m_context.get_base_model(m_best_model);   // mdl = m_model
//   m_labels.reset();                          // size := 0
//   m_context.get_labels(m_labels);            // m_labels.append(ctx.m_labels)
// Abstractions: model_ref -> int; symbol -> int; svector growth abstracted by a
// capacity precondition; callees inlined.

/*@
  context_everywhere ctx_n >= 0 && cap >= ctx_n;
  context (pointer/redacted)(ctx_model, 1, 1\2) ** (pointer/redacted)(best_model, 1, write) ** (pointer/redacted)(labels_n, 1, write);
  context (pointer/redacted)(ctx_labels, ctx_n, 1\2);
  context (pointer/redacted)(labels, cap, write);
  ensures *best_model == *ctx_model;
  ensures *labels_n == ctx_n;
  ensures ((forall/redacted) int i; 0 <= i && i < ctx_n; labels[i] == ctx_labels[i]);
@*/
void get_base_model(int* ctx_model, int* ctx_labels, int ctx_n,
                    int* best_model, int* labels, int* labels_n, int cap)
{
    *best_model = *ctx_model;
    *labels_n = 0;
    int i = 0;
    /*@
      loop_invariant 0 <= i && i <= ctx_n;
      loop_invariant (pointer/redacted)(ctx_labels, ctx_n, 1\2) ** (pointer/redacted)(labels, cap, write);
      loop_invariant (pointer/redacted)(labels_n, 1, write);
      loop_invariant *labels_n == i;
      loop_invariant ((forall/redacted) int j; 0 <= j && j < i; labels[j] == ctx_labels[j]);
    @*/
    while (i < ctx_n) {
        labels[i] = ctx_labels[i];
        i = i + 1;
        *labels_n = i;
    }
}
