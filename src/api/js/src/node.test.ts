const mockInitModule = jest.fn();
const mockInitWrapper = jest.fn();
const mockCreateApi = jest.fn();

jest.mock('./z3-built', () => mockInitModule, { virtual: true });
jest.mock('./low-level', () => ({
  init: mockInitWrapper,
  Z3Core: undefined,
  Z3LowLevel: undefined,
}));
jest.mock('./high-level', () => ({
  createApi: mockCreateApi,
}));

import { init } from './node';

describe('node init', () => {
  beforeEach(() => {
    mockInitModule.mockReset();
    mockInitWrapper.mockReset();
    mockCreateApi.mockReset();
  });

  it('passes module overrides to the low-level initializer', async () => {
    const locateFile = jest.fn((file: string) => `npm:z3-solver/build/${file}`);
    const lowLevel = { Z3: { low: true }, em: { module: true } };
    const highLevel = { Context: jest.fn() };
    mockInitWrapper.mockResolvedValue(lowLevel);
    mockCreateApi.mockReturnValue(highLevel);

    const api = await init({ locateFile });

    expect(mockInitWrapper).toHaveBeenCalledWith(mockInitModule, { locateFile });
    expect(mockCreateApi).toHaveBeenCalledWith(lowLevel.Z3, lowLevel.em);
    expect(api).toEqual({ ...lowLevel, ...highLevel });
  });
});
