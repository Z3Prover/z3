const mockInitWrapper = jest.fn();
const mockCreateApi = jest.fn();

jest.mock('./low-level', () => ({
  init: mockInitWrapper,
  Z3Core: undefined,
  Z3LowLevel: undefined,
}));
jest.mock('./high-level', () => ({
  createApi: mockCreateApi,
}));

import { init } from './browser';

describe('browser init', () => {
  beforeEach(() => {
    delete (global as any).initZ3;
    mockInitWrapper.mockReset();
    mockCreateApi.mockReset();
  });

  it('passes module overrides to the browser initializer', async () => {
    const initZ3 = jest.fn();
    const locateFile = jest.fn((file: string) => `https://example.test/${file}`);
    const lowLevel = { Z3: { low: true }, em: { module: true } };
    const highLevel = { Context: jest.fn() };
    (global as any).initZ3 = initZ3;
    mockInitWrapper.mockResolvedValue(lowLevel);
    mockCreateApi.mockReturnValue(highLevel);

    const api = await init({ locateFile });

    expect(mockInitWrapper).toHaveBeenCalledWith(initZ3, { locateFile });
    expect(mockCreateApi).toHaveBeenCalledWith(lowLevel.Z3, lowLevel.em);
    expect(api).toEqual({ ...lowLevel, ...highLevel });
  });

  it('throws when initZ3 is unavailable', async () => {
    await expect(init()).rejects.toThrow(
      'initZ3 was not imported correctly. Please consult documentation on how to load Z3 in browser',
    );
  });
});
