import { Z3AssertionError } from './types';
import { allSatisfy, assert, assertExhaustive, autoBind } from './utils';

describe('allSatisfy', () => {
  it('returns null on empty array', () => {
    expect(allSatisfy([], () => true)).toBeNull();
  });

  it('returns true if all satisfy', () => {
    expect(allSatisfy([2, 4, 6, 8], arg => arg % 2 === 0)).toStrictEqual(true);
  });

  it('returns false if any element fails', () => {
    expect(allSatisfy([2, 4, 1, 8], arg => arg % 2 === 0)).toStrictEqual(false);
  });
});

describe('assertExhaustive', () => {
  enum MyEnum {
    A,
    B,
  }
  it('stops compilation', () => {
    const result: MyEnum = MyEnum.A as any;
    switch (result) {
      case MyEnum.A:
        break;
      default:
        // @ts-expect-error
        assertExhaustive(result);
    }
  });

  it('allows compilation', () => {
    const result: MyEnum = MyEnum.A as any;
    switch (result) {
      case MyEnum.A:
        break;
      case MyEnum.B:
        break;
      default:
        assertExhaustive(result);
    }
  });

  it('throws', () => {
    const result: MyEnum = undefined as any;
    switch (result) {
      case MyEnum.A:
        throw new Error();
      case MyEnum.B:
        throw new Error();
      default:
        expect(() => assertExhaustive(result)).toThrowError();
    }
  });
});

describe('autoBind', () => {
  class Binded {
    readonly name = 'Richard';
    constructor(shouldBind: boolean) {
      if (shouldBind === true) {
        autoBind(this);
      }
    }

    test(): string {
      return `Hello ${this.name}`;
    }
  }

  it('binds this', () => {
    const { test: withoutBind } = new Binded(false);
    const { test: withBind } = new Binded(true);
    expect(() => withoutBind()).toThrowError(TypeError);
    expect(withBind()).toStrictEqual('Hello Richard');
  });
});

describe('assert', () => {
  it('throws on failure', () => {
    expect(() => assert(false)).toThrowError(Z3AssertionError);
    expect(() => assert(false, 'foobar')).toThrowError(new Z3AssertionError('foobar'));
  });

  it('does nothing on sucess', () => {
    expect(() => assert(true, 'hello')).not.toThrow();
  });
});
