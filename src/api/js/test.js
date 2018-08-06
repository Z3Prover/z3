const z3 = require("./build/Release/z3");
const z3const = require("./z3consts.js");
const assert = require("assert");

class Z3Tests {
  constructor() {
    var cfg = z3.Z3_mk_config();
    this.ctx = z3.Z3_mk_context(cfg);
    this.bool_sort = this.mk_bool_sort();
    this.real_sort = this.mk_real_sort();
    this.int_sort = this.mk_int_sort();
  }

  mk_custom_context() {
    var cfg = z3.Z3_mk_config();
    z3.Z3_set_param_value(cfg, "model", "true");
    z3.Z3_set_param_value(cfg, "proof", "true");
    z3.Z3_del_config(cfg);
    this.ctx = z3.Z3_mk_context(cfg);
  }

  mk_solver() {
    var s = z3.Z3_mk_solver(this.ctx);
    z3.Z3_solver_inc_ref(this.ctx, s);
    return s;
  }

  mk_bool_sort() {
    return z3.Z3_mk_bool_sort(this.ctx);
  }

  mk_int_sort() {
    return z3.Z3_mk_int_sort(this.ctx);
  }

  mk_real_sort() {
    return z3.Z3_mk_real_sort(this.ctx);
  }

  mk_real_sort() {
    return z3.Z3_mk_real_sort(this.ctx);
  }

  mk_var(name, sort) {
    var s = z3.Z3_mk_string_symbol(this.ctx, name);
    return z3.Z3_mk_const(this.ctx, s, sort);
  }

  mk_real(name) {
    return this.mk_var(name, this.real_sort);
  }

  mk_assertion(name) {
    var x = this.mk_real("x");
    var y = this.mk_real("y");
    var L0 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
    var R0 = z3.Z3_mk_real(this.ctx, 5, this.real_sort);
    var c0 = z3.Z3_mk_eq(this.ctx, L0, R0);
  }

  test_linear_sat() {
    var x = this.mk_real("x");
    var y = this.mk_real("y");

    var L0 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
    var R0 = z3.Z3_mk_int(this.ctx, 5, this.int_sort);
    var c0 = z3.Z3_mk_eq(this.ctx, L0, R0);

    var s = this.mk_solver();
    z3.Z3_solver_assert(this.ctx, s, c0);

    var res = z3.Z3_solver_check(this.ctx, s);
    assert(res == z3const.Z3_L_TRUE);
  }

  test_linear_unsat() {
    var x = this.mk_real("x");
    var y = this.mk_real("y");

    var L0 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
    var R0 = z3.Z3_mk_int(this.ctx, 5, this.int_sort);
    var L1 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
    var R1 = z3.Z3_mk_int(this.ctx, 6, this.int_sort);

    var c0 = z3.Z3_mk_eq(this.ctx, L0, R0);
    var c1 = z3.Z3_mk_eq(this.ctx, L1, R1);

    var s = this.mk_solver();
    z3.Z3_solver_assert(this.ctx, s, c0);
    z3.Z3_solver_assert(this.ctx, s, c1);

    var res = z3.Z3_solver_check(this.ctx, s);
    assert(res == z3const.Z3_L_FALSE);
  }

  test_linear_solutions() {
    var x = this.mk_real("x");
    var y = this.mk_real("y");

    var L0 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
    var R0 = z3.Z3_mk_int(this.ctx, 8, this.int_sort);
    var c0 = z3.Z3_mk_eq(this.ctx, L0, R0);

    var L1 = z3.Z3_mk_sub(this.ctx, 2, [x, y]);
    var R1 = z3.Z3_mk_int(this.ctx, 2, this.int_sort);
    var c1 = z3.Z3_mk_eq(this.ctx, L1, R1);

    var s = this.mk_solver();
    z3.Z3_solver_assert(this.ctx, s, c0);
    z3.Z3_solver_assert(this.ctx, s, c1);

    var res = z3.Z3_solver_check(this.ctx, s);
    assert(res == z3const.Z3_L_TRUE);
    var m = z3.Z3_solver_get_model(this.ctx, s);
    var mstr = z3.Z3_model_to_string(this.ctx, m);
    var assignments = mstr.split("\n");
    assert(assignments.includes("y -> 3.0"));
    assert(assignments.includes("x -> 5.0"));
  }

  test_solver() {
    var x = this.mk_real("x");
    var y = this.mk_real("y");
    var z = this.mk_real("z");

    var s = this.mk_solver();

    var res = z3.Z3_solver_check(this.ctx, s);
    assert(res == z3const.Z3_L_TRUE);
  }

  test_array_value() {
    var x = this.mk_real("x");
    var y = this.mk_real("y");

    var c0 = z3.Z3_mk_add(this.ctx, 2, [x, y]);
  }
}

tester = new Z3Tests();

function getAllMethods(obj) {
  return Object.getOwnPropertyNames(obj).filter(function(prop) {
    return typeof obj[prop] == "function" && prop.startsWith("test");
  });
}

var funcs = getAllMethods(Z3Tests.prototype);

funcs.forEach(f => tester[f]());
