/**
 * Example demonstrating the RCF (Real Closed Field) API in TypeScript.
 *
 * This example shows how to use RCF numerals to work with:
 * - Transcendental numbers (pi, e)
 * - Algebraic numbers (roots of polynomials)
 * - Infinitesimals
 * - Exact real arithmetic
 *
 * Note: The RCF API is exposed at the low-level API layer.
 * Import from 'z3-solver' for low-level access.
 */

import { init } from 'z3-solver';

async function rcfBasicExample() {
  console.log('RCF Basic Example');
  console.log('=================');

  const { Z3 } = await init();
  const ctx = Z3.mk_context_rc(Z3.mk_config());

  try {
    // Create pi and e
    const pi = Z3.rcf_mk_pi(ctx);
    const e = Z3.rcf_mk_e(ctx);

    console.log('pi =', Z3.rcf_num_to_string(ctx, pi, false, false));
    console.log('e =', Z3.rcf_num_to_string(ctx, e, false, false));

    // Arithmetic operations
    const sum = Z3.rcf_add(ctx, pi, e);
    const prod = Z3.rcf_mul(ctx, pi, e);

    console.log('pi + e =', Z3.rcf_num_to_string(ctx, sum, false, false));
    console.log('pi * e =', Z3.rcf_num_to_string(ctx, prod, false, false));

    // Decimal approximations
    console.log('pi (10 decimals) =', Z3.rcf_num_to_decimal_string(ctx, pi, 10));
    console.log('e (10 decimals) =', Z3.rcf_num_to_decimal_string(ctx, e, 10));

    // Comparisons
    console.log('pi < e?', Z3.rcf_lt(ctx, pi, e) ? 'yes' : 'no');
    console.log('pi > e?', Z3.rcf_gt(ctx, pi, e) ? 'yes' : 'no');

    // Cleanup
    Z3.rcf_del(ctx, pi);
    Z3.rcf_del(ctx, e);
    Z3.rcf_del(ctx, sum);
    Z3.rcf_del(ctx, prod);
  } finally {
    Z3.del_context(ctx);
  }
}

async function rcfRationalExample() {
  console.log('\nRCF Rational Example');
  console.log('====================');

  const { Z3 } = await init();
  const ctx = Z3.mk_context_rc(Z3.mk_config());

  try {
    // Create rational numbers
    const half = Z3.rcf_mk_rational(ctx, '1/2');
    const third = Z3.rcf_mk_rational(ctx, '1/3');

    console.log('1/2 =', Z3.rcf_num_to_string(ctx, half, false, false));
    console.log('1/3 =', Z3.rcf_num_to_string(ctx, third, false, false));

    // Arithmetic
    const sum = Z3.rcf_add(ctx, half, third);
    console.log('1/2 + 1/3 =', Z3.rcf_num_to_string(ctx, sum, false, false));

    // Type queries
    console.log('Is 1/2 rational?', Z3.rcf_is_rational(ctx, half) ? 'yes' : 'no');
    console.log('Is 1/2 algebraic?', Z3.rcf_is_algebraic(ctx, half) ? 'yes' : 'no');

    // Cleanup
    Z3.rcf_del(ctx, half);
    Z3.rcf_del(ctx, third);
    Z3.rcf_del(ctx, sum);
  } finally {
    Z3.del_context(ctx);
  }
}

async function rcfRootsExample() {
  console.log('\nRCF Roots Example');
  console.log('=================');

  const { Z3 } = await init();
  const ctx = Z3.mk_context_rc(Z3.mk_config());

  try {
    // Find roots of x^2 - 2 = 0
    // Polynomial: -2 + 0*x + 1*x^2
    const coeffs = [
      Z3.rcf_mk_small_int(ctx, -2), // constant term
      Z3.rcf_mk_small_int(ctx, 0), // x coefficient
      Z3.rcf_mk_small_int(ctx, 1), // x^2 coefficient
    ];

    const roots = new Array(coeffs.length);
    const numRoots = Z3.rcf_mk_roots(ctx, coeffs, roots);

    console.log('Roots of x^2 - 2 = 0:');
    for (let i = 0; i < numRoots; i++) {
      console.log(`  root[${i}] =`, Z3.rcf_num_to_string(ctx, roots[i], false, false));
      console.log(`  decimal =`, Z3.rcf_num_to_decimal_string(ctx, roots[i], 15));
      console.log(`  is_algebraic =`, Z3.rcf_is_algebraic(ctx, roots[i]) ? 'yes' : 'no');
    }

    // Cleanup
    for (const coeff of coeffs) {
      Z3.rcf_del(ctx, coeff);
    }
    for (let i = 0; i < numRoots; i++) {
      Z3.rcf_del(ctx, roots[i]);
    }
  } finally {
    Z3.del_context(ctx);
  }
}

async function rcfInfinitesimalExample() {
  console.log('\nRCF Infinitesimal Example');
  console.log('=========================');

  const { Z3 } = await init();
  const ctx = Z3.mk_context_rc(Z3.mk_config());

  try {
    // Create an infinitesimal
    const eps = Z3.rcf_mk_infinitesimal(ctx);
    console.log('eps =', Z3.rcf_num_to_string(ctx, eps, false, false));
    console.log('Is eps infinitesimal?', Z3.rcf_is_infinitesimal(ctx, eps) ? 'yes' : 'no');

    // Infinitesimals are smaller than any positive real number
    const tiny = Z3.rcf_mk_rational(ctx, '1/1000000000');
    console.log('eps < 1/1000000000?', Z3.rcf_lt(ctx, eps, tiny) ? 'yes' : 'no');

    // Cleanup
    Z3.rcf_del(ctx, eps);
    Z3.rcf_del(ctx, tiny);
  } finally {
    Z3.del_context(ctx);
  }
}

async function main() {
  try {
    await rcfBasicExample();
    await rcfRationalExample();
    await rcfRootsExample();
    await rcfInfinitesimalExample();

    console.log('\nAll RCF examples completed successfully!');
  } catch (error) {
    console.error('Error:', error);
    throw error;
  }
}

main();
