import { functions, types } from '../scripts/parse-api';

describe('parse-api', () => {
  it('recognizes the proof-check callback and preserves its function-pointer metadata', () => {
    expect(types.Z3_proof_check_eh).toBe('Z3_proof_check_eh');

    const callback = functions.find(fn => fn.name === 'Z3_set_proof_check_callback');
    expect(callback).toMatchObject({
      ret: 'void',
      params: [
        { type: 'Z3_context', name: 'c', kind: 'in', isPtr: false },
        { type: 'void', name: 'user_context', kind: 'in', isPtr: true },
        { type: 'Z3_proof_check_eh', name: 'callback', kind: 'fnptr', isPtr: false },
      ],
    });
  });
});
