import assert from 'assert';
import fs from 'fs';
import path from 'path';

const files = [
  'z3_api.h',
  'z3_algebraic.h',
  'z3_ast_containers.h',
  'z3_fixedpoint.h',
  'z3_fpa.h',
  'z3_optimization.h',
  'z3_polynomial.h',
  'z3_rcf.h',
  'z3_spacer.h',
];

const aliases = {
  __proto__: null,
  Z3_string: 'string',
  bool: 'boolean',
  signed: 'int',
} as unknown as Record<string, string>;

const primitiveTypes = {
  __proto__: null,
  Z3_char_ptr: 'string',
  unsigned: 'number',
  int: 'number',
  uint64_t: 'bigint',
  int64_t: 'bigint',
  double: 'number',
  float: 'number',
} as unknown as Record<string, string>;

const optTypes = {
  __proto__: null,

  Z3_sort_opt: 'Z3_sort',
  Z3_ast_opt: 'Z3_ast',
  Z3_func_interp_opt: 'Z3_func_interp',
} as unknown as Record<string, string>;

// parse type declarations
const types = {
  __proto__: null,

  // these are function types I can't be bothered to parse
  // NSB: They can be extracted automatically from z3_api.h thanks to the use
  // of a macro.
  Z3_error_handler: 'Z3_error_handler',
  Z3_push_eh: 'Z3_push_eh',
  Z3_pop_eh: 'Z3_pop_eh',
  Z3_fresh_eh: 'Z3_fresh_eh',
  Z3_fixed_eh: 'Z3_fixed_eh',
  Z3_eq_eh: 'Z3_eq_eh',
  Z3_final_eh: 'Z3_final_eh',
  Z3_created_eh: 'Z3_created_eh',
  Z3_decide_eh: 'Z3_decide_eh',
  Z3_on_clause_eh: 'Z3_on_clause_eh',
} as unknown as Record<string, string>;

export type ApiParam = { kind: string; sizeIndex?: number; type: string };
export type Api = { params: ApiParam[]; ret: string; extra: boolean };
const defApis: Record<string, Api> = Object.create(null);
export type FuncParam = {
  type: string;
  cType: string;
  name: string;
  isConst: boolean;
  isPtr: boolean;
  isArray: boolean;
  nullable: boolean;
  kind?: string;
  sizeIndex?: number;
};
export type Func = { ret: string; cRet: string; name: string; params: FuncParam[]; nullableRet: boolean };
const functions: Func[] = [];
let enums: Record<string, Record<string, number>> = Object.create(null);
for (let file of files) {
  let contents = fs.readFileSync(path.join(__dirname, '..', '..', file), 'utf8');

  // we _could_ use an actual C++ parser, which accounted for macros and everything
  // but that's super painful
  // and the files are regular enough that we can get away without it

  // we could also do this by modifying the `update_api.py` script
  // which we should probably do eventually
  // but this is easier while this remains not upstreamed

  // we need to parse the `def_API` stuff so we know which things are out parameters
  // unfortunately we also need to parse the actual declarations so we know the parameter names also
  let pytypes = Object.create(null);

  let typeMatches = contents.matchAll(
    /def_Type\(\s*'(?<name>[A-Za-z0-9_]+)',\s*'(?<cname>[A-Za-z0-9_]+)',\s*'(?<pname>[A-Za-z0-9_]+)'\)/g,
  );
  for (let { groups } of typeMatches) {
    assert(groups !== undefined);
    pytypes[groups.name] = groups.cname;
  }

  // we don't have to pre-populate the types map with closure types
  // use the Z3_DECLARE_CLOSURE to identify closure types
  // for (let match of contents.matchAll(/Z3_DECLARE_CLOSURE\((?<type>[A-Za-z0-9_]+),/g)) {
  //   types[match.groups.type] = match.groups.type
  // }

  // we filter first to ensure our regex isn't too strict
  let apiLines = contents.split('\n').filter(l => /def_API|extra_API/.test(l));
  for (let line of apiLines) {
    let match = line.match(
      /^\s*(?<def>def_API|extra_API) *\(\s*'(?<name>[A-Za-z0-9_]+)'\s*,\s*(?<ret>[A-Za-z0-9_]+)\s*,\s*\((?<params>((_in|_out|_in_array|_out_array|_fnptr|_inout_array)\([^)]+\)\s*,?\s*)*)\)\s*\)\s*$/,
    );
    if (match === null) {
      throw new Error(`failed to match def_API call ${JSON.stringify(line)}`);
    }
    assert(match.groups !== undefined);
    let { name, ret, def } = match.groups;
    let params = match.groups.params.trim();
    let text = params;
    let parsedParams = [];
    while (true) {
      text = eatWs(text);
      ({ text, match } = eat(text, /^_(?<kind>in|out|in_array|out_array|inout_array|fnptr)\(/));
      if (match == null) {
        break;
      }
      assert(match.groups !== undefined);
      let kind = match.groups.kind;
      if (kind === 'inout_array') kind = 'in_array'; // https://github.com/Z3Prover/z3/discussions/5761
      if (kind === 'in' || kind === 'out' || kind == 'fnptr') {
        ({ text, match } = expect(text, /^[A-Za-z0-9_]+/));
        parsedParams.push({ kind, type: match[0] });
      } else {
        ({ text, match } = expect(text, /^(\d+),/));
        let sizeIndex = Number(match[1]);
        text = eatWs(text);
        ({ text, match } = expect(text, /^[A-Za-z0-9_]+/));
        parsedParams.push({ kind, sizeIndex, type: match[0] });
      }
      ({ text, match } = expect(text, /^\)/));
      text = eatWs(text);
      ({ text, match } = eat(text, /^,/));
    }
    if (text !== '') {
      throw new Error(`extra text in parameter list ${JSON.stringify(text)}`);
    }

    if (name in defApis) {
      throw new Error(`multiple defApi calls for ${name}`);
    }
    defApis[name] = { params: parsedParams, ret, extra: def === 'extra_API' };
  }

  for (let match of contents.matchAll(/DEFINE_TYPE\((?<type>[A-Za-z0-9_]+)\)/g)) {
    assert(match.groups !== undefined);
    types[match.groups.type] = match.groups.type;
  }

  // parse enum declarations
  for (let idx = 0; idx < contents.length; ) {
    let nextIdx = contents.indexOf('typedef enum', idx);
    if (nextIdx === -1) {
      break;
    }
    let lineStart = contents.lastIndexOf('\n', nextIdx);
    let lineEnd = contents.indexOf(';', nextIdx);
    if (lineStart === -1 || lineEnd === -1) {
      throw new Error(`could not parse enum at index ${nextIdx}`);
    }
    idx = lineEnd;
    let slice = contents.substring(lineStart, lineEnd);
    let { match, text } = eat(slice, /^\s*typedef enum\s*\{/);
    if (match === null) {
      throw new Error(`could not parse enum ${JSON.stringify(slice)}`);
    }
    let vals: Record<string, number> = Object.create(null);
    let next = 0;
    while (true) {
      let blank = true;
      while (blank) {
        ({ match, text } = eat(text, /^\s*(\/\/[^\n]*\n)?/));
        assert(match !== null);
        blank = match[0].length > 0;
      }
      ({ match, text } = eat(text, /^[A-Za-z0-9_]+/));
      if (match === null) {
        throw new Error(`could not parse enum value in ${slice}`);
      }
      let name = match[0];
      text = eatWs(text);

      ({ match, text } = eat(text, /^= *(?<val>[^\n,\s]+)/));
      if (match !== null) {
        assert(match.groups !== undefined);
        let parsedVal = Number(match.groups.val);
        if (Object.is(parsedVal, NaN)) {
          throw new Error('unknown value ' + match.groups.val);
        }
        vals[name] = parsedVal;
        next = parsedVal;
      } else {
        vals[name] = next;
      }
      text = eatWs(text);
      ({ match, text } = eat(text, /^,?\s*}/));
      if (match !== null) {
        break;
      }

      ({ match, text } = expect(text, /^,/));

      ++next;
    }
    text = eatWs(text);
    ({ match, text } = expect(text, /^[A-Za-z0-9_]+/));
    if (match[0] in enums) {
      throw new Error(`duplicate enum definition ${match[0]}`);
    }
    enums[match[0]] = vals;
    text = eatWs(text);
    if (text !== '') {
      throw new Error('expected end of definition, got ' + text);
    }
  }

  // parse function declarations
  for (let idx = 0; idx < contents.length; ) {
    let nextIdx = contents.indexOf(' Z3_API ', idx);
    if (nextIdx === -1) {
      break;
    }
    let lineStart = contents.lastIndexOf('\n', nextIdx);
    let lineEnd = contents.indexOf(';', nextIdx);
    if (lineStart === -1 || lineEnd === -1) {
      throw new Error(`could not parse definition at index ${nextIdx}`);
    }
    idx = lineEnd;

    let slice = contents.substring(lineStart, lineEnd);
    let match = slice.match(/^\s*(?<ret>[A-Za-z0-9_]+) +Z3_API +(?<name>[A-Za-z0-9_]+)\s*\((?<params>[^)]*)\)/);
    if (match == null) {
      throw new Error(`failed to match c definition: ${JSON.stringify(slice)}`);
    }
    assert(match.groups !== undefined);

    let { ret, name, params } = match.groups;
    let parsedParams = [];

    if (params.trim() !== 'void') {
      for (let param of params.split(',')) {
        let paramType: string, paramName: string, isConst: boolean, isPtr: boolean, isArray: boolean;

        let { match, text } = eat(param, /^\s*/);
        ({ match, text } = eat(text, /^[A-Za-z0-9_]+/));
        if (match === null) {
          throw new Error(`failed to parse param type in ${JSON.stringify(slice)} for param ${JSON.stringify(param)}`);
        }
        paramType = match[0];

        text = eatWs(text);

        ({ match, text } = eat(text, /^const(?![A-Za-z0-9_])/));
        isConst = match !== null;

        ({ match, text } = eat(text, /^\s*\*/));
        isPtr = match !== null;

        text = eatWs(text);

        if (text === '') {
          paramName = 'UNNAMED';
          isArray = false;
        } else {
          ({ match, text } = eat(text, /^[A-Za-z0-9_]+/));
          if (match === null) {
            throw new Error(
              `failed to parse param name in ${JSON.stringify(slice)} for param ${JSON.stringify(param)}`,
            );
          }
          paramName = match[0];
          text = eatWs(text);

          ({ match, text } = eat(text, /^\[\]/));
          isArray = match !== null;

          text = eatWs(text);

          if (text !== '') {
            throw new Error(`excess text in param in ${JSON.stringify(slice)} for param ${JSON.stringify(param)}`);
          }
        }

        if (paramType === 'Z3_string_ptr' && !isPtr) {
          paramType = 'Z3_string';
          isPtr = true;
        }

        let nullable = false;
        if (paramType in optTypes) {
          nullable = true;
          paramType = optTypes[paramType];
        }

        let cType = paramType;
        paramType = aliases[paramType] ?? paramType;

        parsedParams.push({ type: paramType, cType, name: paramName, isConst, isPtr, isArray, nullable });
      }
    }

    let nullableRet = false;
    if (ret in optTypes) {
      nullableRet = true;
      ret = optTypes[ret];
    }

    let cRet = ret;
    ret = aliases[ret] ?? ret;

    if (name in defApis) {
      functions.push({ ret, cRet, name, params: parsedParams, nullableRet });
    }
    // only a few things are missing `def_API`; we'll skip those
  }
}

function isKnownType(t: string) {
  return t in enums || t in types || t in primitiveTypes || ['string', 'boolean', 'void'].includes(t);
}

for (let fn of functions) {
  if (!isKnownType(fn.ret)) {
    throw new Error(`unknown type ${fn.ret}`);
  }
  let defParams = defApis[fn.name].params;
  if (fn.params.length !== defParams.length) {
    throw new Error(`parameter length mismatch for ${fn.name}`);
  }
  let idx = 0;
  for (let param of fn.params) {
    if (!isKnownType(param.type)) {
      throw new Error(`unknown type ${param.type}`);
    }
    param.kind = defParams[idx].kind;
    if (param.kind === 'in_array' || param.kind === 'out_array') {
      if (defParams[idx].sizeIndex == null) {
        throw new Error(`function ${fn.name} parameter ${idx} is marked as ${param.kind} but has no index`);
      }
      param.sizeIndex = defParams[idx].sizeIndex;
      if (!param.isArray && param.isPtr) {
        // not clear why some things are written as `int * x` and others `int x[]`
        // but we can just cast
        param.isArray = true;
        param.isPtr = false;
      }
      if (!param.isArray) {
        throw new Error(`function ${fn.name} parameter ${idx} is marked as ${param.kind} but not typed as array`);
      }
    }
    ++idx;
  }
}

function eat(str: string, regex: string | RegExp) {
  const match: RegExpMatchArray | null = str.match(regex);
  if (match === null) {
    return { match, text: str };
  }
  return { match, text: str.substring(match[0].length) };
}

function eatWs(text: string) {
  return eat(text, /^\s*/).text;
}

function expect(str: string, regex: string | RegExp) {
  let { text, match } = eat(str, regex);
  if (match === null) {
    throw new Error(`expected ${regex}, got ${JSON.stringify(text)}`);
  }
  return { text, match };
}

export { primitiveTypes, types, enums, functions };
