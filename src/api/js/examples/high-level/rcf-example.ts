/**
 * Example demonstrating the RCF (Real Closed Field) API in TypeScript.
 *
 * This example shows how to use RCF numerals to work with:
 * - Transcendental numbers (pi, e)
 * - Algebraic numbers (roots of polynomials)
 * - Infinitesimals
 * - Exact real arithmetic
 *
 * Note: This example uses the high-level API for a cleaner interface.
 */

import { init } from 'z3-solver';

async function rcfBasicExample() {
  console.log('RCF Basic Example (High-Level API)');
  console.log('===================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  // Create pi and e
  const pi = RCFNum.pi();
  const e = RCFNum.e();

  console.log('pi =', pi.toString());
  console.log('e =', e.toString());

  // Arithmetic operations
  const sum = pi.add(e);
  const prod = pi.mul(e);

  console.log('pi + e =', sum.toString());
  console.log('pi * e =', prod.toString());

  // Decimal approximations
  console.log('pi (10 decimals) =', pi.toDecimal(10));
  console.log('e (10 decimals) =', e.toDecimal(10));

  // Comparisons
  console.log('pi < e?', pi.lt(e) ? 'yes' : 'no');
  console.log('pi > e?', pi.gt(e) ? 'yes' : 'no');
}

async function rcfRationalExample() {
  console.log('\nRCF Rational Example (High-Level API)');
  console.log('=====================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  // Create rational numbers
  const half = RCFNum('1/2');
  const third = RCFNum('1/3');

  console.log('1/2 =', half.toString());
  console.log('1/3 =', third.toString());

  // Arithmetic
  const sum = half.add(third);
  console.log('1/2 + 1/3 =', sum.toString());
  console.log('1/2 + 1/3 (decimal) =', sum.toDecimal(10));

  // Type queries
  console.log('Is 1/2 rational?', half.isRational() ? 'yes' : 'no');
  console.log('Is 1/2 algebraic?', half.isAlgebraic() ? 'yes' : 'no');
}

async function rcfRootsExample() {
  console.log('\nRCF Roots Example (High-Level API)');
  console.log('===================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  // Find roots of x^2 - 2 = 0
  // Polynomial: -2 + 0*x + 1*x^2
  const coeffs = [
    RCFNum(-2), // constant term
    RCFNum(0), // x coefficient
    RCFNum(1), // x^2 coefficient
  ];

  const roots = RCFNum.roots(coeffs);

  console.log('Roots of x^2 - 2 = 0:');
  for (let i = 0; i < roots.length; i++) {
    console.log(`  root[${i}] =`, roots[i].toString());
    console.log(`  decimal =`, roots[i].toDecimal(15));
    console.log(`  is_algebraic =`, roots[i].isAlgebraic() ? 'yes' : 'no');
  }
}

async function rcfInfinitesimalExample() {
  console.log('\nRCF Infinitesimal Example (High-Level API)');
  console.log('===========================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  // Create an infinitesimal
  const eps = RCFNum.infinitesimal();
  console.log('eps =', eps.toString());
  console.log('Is eps infinitesimal?', eps.isInfinitesimal() ? 'yes' : 'no');

  // Infinitesimals are smaller than any positive real number
  const tiny = RCFNum('1/1000000000');
  console.log('eps < 1/1000000000?', eps.lt(tiny) ? 'yes' : 'no');
}

async function rcfArithmeticExample() {
  console.log('\nRCF Arithmetic Operations Example');
  console.log('==================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  const a = RCFNum(5);
  const b = RCFNum(3);

  console.log('a =', a.toString());
  console.log('b =', b.toString());
  console.log('a + b =', a.add(b).toString());
  console.log('a - b =', a.sub(b).toString());
  console.log('a * b =', a.mul(b).toString());
  console.log('a / b =', a.div(b).toString(), '=', a.div(b).toDecimal(5));
  console.log('-a =', a.neg().toString());
  console.log('1/a =', a.inv().toString(), '=', a.inv().toDecimal(5));
  console.log('a^3 =', a.power(3).toString());

  // Comparisons
  console.log('\nComparisons:');
  console.log('a < b?', a.lt(b));
  console.log('a > b?', a.gt(b));
  console.log('a <= b?', a.le(b));
  console.log('a >= b?', a.ge(b));
  console.log('a == b?', a.eq(b));
  console.log('a != b?', a.neq(b));
}

async function rcfSymbolicMathExample() {
  console.log('\nRCF Symbolic Mathematics Example');
  console.log('=================================');

  const { Context } = await init();
  const { RCFNum } = Context('main');

  // Work with exact symbolic values
  const pi = RCFNum.pi();
  const e = RCFNum.e();
  const sqrt2Coeffs = [RCFNum(-2), RCFNum(0), RCFNum(1)];
  const sqrt2Roots = RCFNum.roots(sqrt2Coeffs);
  const sqrt2 = sqrt2Roots.find(r => r.gt(RCFNum(0)))!;

  console.log('π =', pi.toDecimal(15));
  console.log('e =', e.toDecimal(15));
  console.log('√2 =', sqrt2.toDecimal(15));

  // Combine them
  const expr1 = pi.add(e);
  const expr2 = pi.mul(sqrt2);
  const expr3 = e.power(2);

  console.log('\nExpressions:');
  console.log('π + e =', expr1.toDecimal(10));
  console.log('π × √2 =', expr2.toDecimal(10));
  console.log('e² =', expr3.toDecimal(10));

  // Check properties
  console.log('\nProperties:');
  console.log('π is transcendental:', pi.isTranscendental());
  console.log('e is transcendental:', e.isTranscendental());
  console.log('√2 is algebraic:', sqrt2.isAlgebraic());
  console.log('√2 is rational:', sqrt2.isRational());
}

async function main() {
  try {
    await rcfBasicExample();
    await rcfRationalExample();
    await rcfRootsExample();
    await rcfInfinitesimalExample();
    await rcfArithmeticExample();
    await rcfSymbolicMathExample();

    console.log('\n✓ All RCF examples completed successfully!');
    console.log('\nThe RCF API in TypeScript now provides:');
    console.log('  • 38 functions for exact real arithmetic');
    console.log('  • Support for π, e, algebraic numbers, and infinitesimals');
    console.log('  • Full arithmetic and comparison operations');
    console.log('  • Polynomial root finding');
    console.log('  • Type predicates and conversions');
  } catch (error) {
    console.error('Error:', error);
    throw error;
  }
}

main();
