import { makeCCWrapper } from '../scripts/make-cc-wrapper';

describe('makeCCWrapper', () => {
  const wrapper = makeCCWrapper();

  it('rejects unknown exceptions with Error instances in every wrapper', () => {
    const handlers = [...wrapper.matchAll(/catch \(\.\.\.\) \{([\s\S]*?)\}, call_id\);/g)];

    expect(handlers.length).toBeGreaterThanOrEqual(3);
    for (const [, handler] of handlers) {
      expect(handler).toContain("reject_async($0, new Error('failed with unknown exception'));");
    }
    expect(wrapper).not.toContain("reject_async($0, 'failed with unknown exception');");
  });

  it('indents every call_id declaration by two spaces', () => {
    const declarations = wrapper.split('\n').filter(line => line.includes('unsigned int call_id ='));

    expect(declarations.length).toBeGreaterThanOrEqual(3);
    for (const declaration of declarations) {
      expect(declaration).toBe('  unsigned int call_id = EM_ASM_INT({ return current_async_call_id; });');
    }
  });
});
