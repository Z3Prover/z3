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

// https://github.com/sindresorhus/auto-bind
// We modify it to use CommonJS instead of ESM
/*
MIT License

Copyright (c) Sindre Sorhus <sindresorhus@gmail.com> (https://sindresorhus.com)

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/
export function autoBind<Self extends Record<string | symbol, any>>(self: Self): Self {
  for (const [obj, key] of getAllProperties(self.constructor.prototype)) {
    if (key === 'constructor') {
      continue;
    }
    const descriptor = Reflect.getOwnPropertyDescriptor(obj, key);
    if (descriptor && typeof descriptor.value === 'function') {
      (self[key] as any) = self[key].bind(self);
    }
  }
  return self;
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
