import { Z3AssertionError } from './types';

function getAllProperties(obj: Record<string, any>) {
  const properties = new Set<[any, string | symbol]>();
  do {
    for (const key of Reflect.ownKeys(obj)) {
      properties.add([obj, key]);
    }
  } while ((obj = Reflect.getPrototypeOf(obj)!) && obj !== Object.prototype);
  return properties;
}

/**
 * Use to ensure that switches are checked to be exhaustive at compile time
 *
 * @example Basic usage
 * ```typescript
 * enum Something {
 *  left,
 *  right,
 * };
 * const something = getSomething();
 * switch (something) {
 *  case Something.left:
 *    ...
 *  case Something.right:
 *    ...
 *  default:
 *    assertExhaustive(something);
 * }
 * ```
 *
 * @param x - The param on which the switch operates
 */
export function assertExhaustive(x: never): never {
  throw new Error('Unexpected code execution detected, should be caught at compile time');
}

export function assert(condition: boolean, reason?: string): asserts condition {
  if (!condition) {
    throw new Z3AssertionError(reason ?? 'Assertion failed');
  }
}

/**
 * Check the all elements of a `collection` satisfy the `premise`.
 * If any of the items fail the `premise`, returns false;
 * @returns null if the `collection` is empty, boolean otherwise
 */
export function allSatisfy<T>(collection: Iterable<T>, premise: (arg: T) => boolean): boolean | null {
  let hasItems = false;
  for (const arg of collection) {
    hasItems = true;
    if (!premise(arg)) {
      return false;
    }
  }
  return hasItems === true ? true : null;
}
