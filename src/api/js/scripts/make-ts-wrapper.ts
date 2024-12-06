import assert from 'assert';
import fs from 'fs';
import path from 'path';
import prettier from 'prettier';
import { asyncFuncs } from './async-fns';
import { enums, Func, FuncParam, functions, primitiveTypes, types } from './parse-api';

assert(process.argv.length === 4, `Usage: ${process.argv[0]} ${process.argv[1]} wrapperFilePath typesFilePath`);

const wrapperFilePath = process.argv[2];
const typesFilePath = process.argv[3];

async function makeTsWrapper() {
  const subtypes = {
    __proto__: null,
    Z3_sort: 'Z3_ast',
    Z3_func_decl: 'Z3_ast',
  } as unknown as Record<string, string>;

  const makePointerType = (t: string) =>
    `export type ${t} = ` + (t in subtypes ? `Subpointer<'${t}', '${subtypes[t]}'>;` : `Pointer<'${t}'>;`);

  // this supports a up to 6 out integers/pointers
  // or up to 3 out int64s
  const BYTES_TO_ALLOCATE_FOR_OUT_PARAMS = 24;

  const CUSTOM_IMPLEMENTATIONS = ['Z3_mk_context', 'Z3_mk_context_rc'];

  function toEmType(type: string) {
    if (type in primitiveTypes) {
      type = primitiveTypes[type];
    }
    if (['boolean', 'number', 'string', 'bigint', 'void'].includes(type)) {
      return type;
    }
    if (type.startsWith('Z3_')) {
      return 'number';
    }
    throw new Error(`unknown parameter type ${type}`);
  }

  function isZ3PointerType(type: string) {
    return type.startsWith('Z3_');
  }

  function toEm(p: string | FuncParam) {
    if (typeof p === 'string') {
      // we've already set this, e.g. by replacing it with an expression
      return p;
    }
    let { type } = p;
    if (p.kind === 'out') {
      throw new Error(`unknown out parameter type ${JSON.stringify(p)}`);
    }
    if (p.isArray) {
      if (isZ3PointerType(type) || type === 'unsigned' || type === 'int') {
        // this works for nullables also because null coerces to 0
        return `intArrayToByteArr(${p.name} as unknown as number[])`;
      } else if (type === 'boolean') {
        return `boolArrayToByteArr(${p.name})`;
      } else {
        throw new Error(`only know how to deal with arrays of int/bool (got ${type})`);
      }
    }
    if (type in primitiveTypes) {
      type = primitiveTypes[type];
    }

    if (['boolean', 'number', 'bigint', 'string'].includes(type)) {
      return p.name;
    }
    if (type.startsWith('Z3_')) {
      return p.name;
    }
    throw new Error(`unknown parameter type ${JSON.stringify(p)}`);
  }

  const isInParam = (p: FuncParam) => p.kind !== undefined && ['in', 'in_array'].includes(p.kind);

  function wrapFunction(fn: Func) {
    if (CUSTOM_IMPLEMENTATIONS.includes(fn.name)) {
      return null;
    }

    let inParams = fn.params.filter(isInParam);
    let outParams = fn.params.map((p, idx) => ({ ...p, idx })).filter(p => !isInParam(p));

    // we'll figure out how to deal with these cases later
    let unknownInParam = inParams.find(
      p =>
        p.isPtr ||
        p.type === 'Z3_char_ptr' ||
        (p.isArray && !(isZ3PointerType(p.type) || p.type === 'unsigned' || p.type === 'int' || p.type === 'boolean')),
    );
    if (unknownInParam) {
      console.error(`skipping ${fn.name} - unknown in parameter ${JSON.stringify(unknownInParam)}`);
      return null;
    }

    if (fn.ret === 'Z3_char_ptr') {
      console.error(`skipping ${fn.name} - returns a string or char pointer`);
      return null;
    }
    // console.error(fn.name);

    let isAsync = asyncFuncs.includes(fn.name);
    let trivial =
      !['string', 'boolean', 'unsigned'].includes(fn.ret) &&
      !fn.nullableRet &&
      outParams.length === 0 &&
      !inParams.some(p => p.type === 'string' || p.isArray || p.nullable);

    let name = fn.name.startsWith('Z3_') ? fn.name.substring(3) : fn.name;

    const params: (string | null)[] = inParams.map(p => {
      let type = p.type;
      if (p.isArray && p.nullable) {
        type = `(${type} | null)[]`;
      } else if (p.isArray) {
        type = `${type}[]`;
      } else if (p.nullable) {
        type = `${type} | null`;
      }
      return `${p.name}: ${type}`;
    });

    if (trivial && isAsync) {
      // i.e. and async
      return `${name}: function (${params.join(', ')}): Promise<${fn.ret}> {
      return Mod.async_call(Mod._async_${fn.name}, ${fn.params.map(toEm).join(', ')});
    }`;
    }

    if (trivial) {
      return `${name}: Mod._${fn.name} as ((${params.join(', ')}) => ${fn.ret})`;
    }

    // otherwise fall back to ccall

    const ctypes = fn.params.map(p =>
      p.kind === 'in_array' ? 'array' : p.kind === 'out_array' ? 'number' : p.isPtr ? 'number' : toEmType(p.type),
    );

    let prefix = '';
    let infix = '';
    let rv = 'ret';
    let suffix = '';

    const args: (string | FuncParam)[] = fn.params;

    let arrayLengthParams = new Map();
    for (let p of inParams) {
      if (p.nullable && !p.isArray) {
        // this would be easy to implement - just map null to 0 - but nothing actually uses nullable non-array input parameters, so we can't ensure we've done it right
        console.error(`skipping ${fn.name} - nullable input parameter`);
        return null;
      }
      if (!p.isArray) {
        continue;
      }
      let { sizeIndex } = p;
      assert(sizeIndex !== undefined);
      if (arrayLengthParams.has(sizeIndex)) {
        let otherParam = arrayLengthParams.get(sizeIndex);
        prefix += `
        if (${otherParam}.length !== ${p.name}.length) {
          throw new TypeError(\`${otherParam} and ${p.name} must be the same length (got \${${otherParam}.length} and \{${p.name}.length})\`);
        }
      `.trim();
        continue;
      }
      arrayLengthParams.set(sizeIndex, p.name);

      const sizeParam = fn.params[sizeIndex];
      if (!(sizeParam.kind === 'in' && sizeParam.type === 'unsigned' && !sizeParam.isPtr && !sizeParam.isArray)) {
        throw new Error(
          `size index is not unsigned int (for fn ${fn.name} parameter ${sizeIndex} got ${sizeParam.type})`,
        );
      }
      args[sizeIndex] = `${p.name}.length`;
      params[sizeIndex] = null;
    }

    let returnType = fn.ret;
    let cReturnType = toEmType(fn.ret);
    if (outParams.length > 0) {
      let mapped = [];
      let memIdx = 0; // offset from `outAddress` where the data should get written, in units of 4 bytes

      for (let outParam of outParams) {
        if (outParam.isArray) {
          if (isZ3PointerType(outParam.type) || outParam.type === 'unsigned') {
            let { sizeIndex } = outParam;
            assert(sizeIndex !== undefined);

            let count;
            if (arrayLengthParams.has(sizeIndex)) {
              // i.e. this is also the length of an input array
              count = args[sizeIndex];
            } else {
              let sizeParam = fn.params[sizeIndex];
              if (
                !(sizeParam.kind === 'in' && sizeParam.type === 'unsigned' && !sizeParam.isPtr && !sizeParam.isArray)
              ) {
                throw new Error(
                  `size index is not unsigned int (for fn ${fn.name} parameter ${sizeIndex} got ${sizeParam.type})`,
                );
              }
              count = sizeParam.name;
            }
            let outArrayAddress = `outArray_${outParam.name}`;
            prefix += `
            let ${outArrayAddress} = Mod._malloc(4 * ${count});
            try {
          `.trim();
            suffix =
              `
            } finally {
              Mod._free(${outArrayAddress});
            }
          `.trim() + suffix;
            args[outParam.idx] = outArrayAddress;
            mapped.push({
              name: outParam.name,
              read:
                `readUintArray(${outArrayAddress}, ${count})` +
                (outParam.type === 'unsigned' ? '' : `as unknown as ${outParam.type}[]`),
              type: `${outParam.type}[]`,
            });
          } else {
            console.error(`skipping ${fn.name} - out array of ${outParam.type}`);
            return null;
          }
        } else if (outParam.isPtr) {
          function setArg() {
            args[outParam.idx] = memIdx === 0 ? 'outAddress' : `outAddress + ${memIdx * 4}`;
          }

          let read, type;
          if (outParam.type === 'string') {
            read = `Mod.UTF8ToString(getOutUint(${memIdx}))`;
            setArg();
            ++memIdx;
          } else if (isZ3PointerType(outParam.type)) {
            read = `getOutUint(${memIdx}) as unknown as ${outParam.type}`;
            setArg();
            ++memIdx;
          } else if (outParam.type === 'unsigned') {
            read = `getOutUint(${memIdx})`;
            setArg();
            ++memIdx;
          } else if (outParam.type === 'int') {
            read = `getOutInt(${memIdx})`;
            setArg();
            ++memIdx;
          } else if (outParam.type === 'uint64_t') {
            if (memIdx % 2 === 1) {
              ++memIdx;
            }
            read = `getOutUint64(${memIdx / 2})`;
            setArg();
            memIdx += 2;
          } else if (outParam.type === 'int64_t') {
            if (memIdx % 2 === 1) {
              ++memIdx;
            }
            read = `getOutInt64(${memIdx / 2})`;
            setArg();
            memIdx += 2;
          } else {
            console.error(`skipping ${fn.name} - unknown out parameter type ${outParam.type}`);
            return null;
          }
          if (memIdx > Math.floor(BYTES_TO_ALLOCATE_FOR_OUT_PARAMS / 4)) {
            // prettier-ignore
            console.error(`skipping ${fn.name} - out parameter sizes sum to ${memIdx * 4}, which is > ${BYTES_TO_ALLOCATE_FOR_OUT_PARAMS}`);
            return null;
          }
          mapped.push({
            name: outParam.name,
            read,
            type: outParam.type,
          });
        } else {
          console.error(`skipping ${fn.name} - out param is neither pointer nor array`);
          return null;
        }
      }

      let ignoreReturn = fn.ret === 'boolean' || fn.ret === 'void';
      if (outParams.length === 1) {
        let outParam = mapped[0];
        if (ignoreReturn) {
          returnType = outParam.type;
          rv = outParam.read;
        } else {
          returnType = `{ rv: ${fn.ret}, ${outParam.name} : ${outParam.type} }`;
          rv = `{ rv: ret, ${outParam.name} : ${outParam.read} }`;
        }
      } else {
        if (ignoreReturn) {
          returnType = `{ ${mapped.map(p => `${p.name} : ${p.type}`).join(', ')} }`;
          rv = `{ ${mapped.map(p => `${p.name}: ${p.read}`).join(', ')} }`;
        } else {
          returnType = `{ rv: ${fn.ret}, ${mapped.map(p => `${p.name} : ${p.type}`).join(', ')} }`;
          rv = `{ rv: ret, ${mapped.map(p => `${p.name}: ${p.read}`).join(', ')} }`;
        }
      }

      if (fn.ret === 'boolean') {
        // assume the boolean indicates success
        infix += `
        if (!ret) {
          return null;
        }
      `.trim();
        cReturnType = 'boolean';
        returnType += ' | null';
      } else if (fn.ret === 'void') {
        cReturnType = 'void';
      } else if (isZ3PointerType(fn.ret) || fn.ret === 'unsigned') {
        cReturnType = 'number';
      } else {
        console.error(`skipping ${fn.name} - out parameter for function which returns non-boolean`);
        return null;
      }
    }

    if (fn.nullableRet) {
      returnType += ' | null';
      infix += `
      if (ret === 0) {
        return null;
      }
      `.trim();
    } else if (fn.ret === 'unsigned') {
      infix += `
      ret = (new Uint32Array([ret]))[0];
      `.trim();
    }

    // async functions are invocations of the wrapper from make-ts-wrapper.ts
    // the wrapper spawns a thread and returns void, so we need to use void as the return type here
    // prettier-ignore
    let invocation = `Mod.ccall('${isAsync ? "async_" : ""}${fn.name}', '${isAsync ? 'void' : cReturnType}', ${JSON.stringify(ctypes)}, [${args.map(toEm).join(", ")}])`;

    if (isAsync) {
      invocation = `await Mod.async_call(() => ${invocation})`;
      returnType = `Promise<${returnType}>`;
    }

    let out = `${name}: ${isAsync ? 'async' : ''} function(${params.filter(p => p != null).join(', ')}): ${returnType} {
    ${prefix}`;
    if (infix === '' && suffix === '' && rv === 'ret') {
      out += `return ${invocation};`;
    } else {
      out += `
      let ret = ${invocation};
      ${infix}return ${rv};${suffix}
    `.trim();
    }
    out += '}';
    return out;
  }

  function wrapEnum(name: string, values: Record<string, number>) {
    let enumEntries = Object.entries(values);
    return `export enum ${name} {
    ${enumEntries.map(([k, v], i) => k + (v === (enumEntries[i - 1]?.[1] ?? -1) + 1 ? '' : ` = ${v}`) + ',').join('\n')}
  };`;
  }

  function getValidOutArrayIndexes(size: number) {
    return Array.from({ length: Math.floor(BYTES_TO_ALLOCATE_FOR_OUT_PARAMS / size) }, (_, i) => i).join(' | ');
  }

  const typesDocument = `// THIS FILE IS AUTOMATICALLY GENERATED BY ${path.basename(__filename)}
// DO NOT EDIT IT BY HAND

interface Pointer<T extends string> extends Number {
  readonly __typeName: T;
}
interface Subpointer<T extends string, S extends string> extends Pointer<S> {
  readonly __typeName2: T;
}

${Object.keys(types)
  .filter(k => k.startsWith('Z3'))
  .map(makePointerType)
  .join('\n')}

${Object.entries(enums)
  .map(e => wrapEnum(e[0], e[1]))
  .join('\n\n')}
`;

  const relativePath: string = path.relative(path.dirname(wrapperFilePath), path.dirname(typesFilePath)) || './';
  const ext: string = path.extname(typesFilePath);
  const basename: string = path.basename(typesFilePath);
  const importPath = relativePath + basename.slice(0, -ext.length);

  const wrapperDocument = `// THIS FILE IS AUTOMATICALLY GENERATED BY ${path.basename(__filename)}
// DO NOT EDIT IT BY HAND

import {
  ${Object.keys(types)
    .filter(k => k.startsWith('Z3'))
    .join(',\n')},
  ${Object.keys(enums).join(',\n')},
} from '${importPath}';

${Object.entries(primitiveTypes)
  .filter(e => e[0] !== 'void')
  .map(e => `type ${e[0]} = ${e[1]};`)
  .join('\n')}

export async function init(initModule: any) {
  let Mod = await initModule();

  // this works for both signed and unsigned, because JS will wrap for you when constructing the Uint32Array
  function intArrayToByteArr(ints: number[]) {
    return new Uint8Array((new Uint32Array(ints)).buffer);
  }

  function boolArrayToByteArr(bools: boolean[]) {
    return bools.map(b => b ? 1 : 0);
  }

  function readUintArray(address: number, count: number) {
    return Array.from(new Uint32Array(Mod.HEAPU32.buffer, address, count));
  }

  let outAddress = Mod._malloc(${BYTES_TO_ALLOCATE_FOR_OUT_PARAMS});
  let outUintArray = (new Uint32Array(Mod.HEAPU32.buffer, outAddress, 4));
  let getOutUint = (i: ${getValidOutArrayIndexes(4)}) => outUintArray[i];
  let outIntArray = (new Int32Array(Mod.HEAPU32.buffer, outAddress, 4));
  let getOutInt = (i: ${getValidOutArrayIndexes(4)}) => outIntArray[i];
  let outUint64Array = (new BigUint64Array(Mod.HEAPU32.buffer, outAddress, 2));
  let getOutUint64 = (i: ${getValidOutArrayIndexes(8)}) => outUint64Array[i];
  let outInt64Array = (new BigInt64Array(Mod.HEAPU32.buffer, outAddress, 2));
  let getOutInt64 = (i: ${getValidOutArrayIndexes(8)}) => outInt64Array[i];

  return {
    em: Mod,
    Z3: {
      mk_context: function(c: Z3_config): Z3_context {
        let ctx = Mod._Z3_mk_context(c);
        Mod._set_noop_error_handler(ctx);
        return ctx;
      },
      mk_context_rc: function(c: Z3_config): Z3_context {
        let ctx = Mod._Z3_mk_context_rc(c);
        Mod._set_noop_error_handler(ctx);
        return ctx;
      },
      ${functions
        .map(wrapFunction)
        .filter(f => f != null)
        .join(',\n')}

    }
  };
}
`;

  return {
    wrapperDocument: await prettier.format(wrapperDocument, { singleQuote: true, parser: 'typescript' }),
    typesDocument: await prettier.format(typesDocument, { singleQuote: true, parser: 'typescript' }),
  };
}

(async () => {
  const { wrapperDocument, typesDocument } = await makeTsWrapper();
  fs.mkdirSync(path.dirname(wrapperFilePath), { recursive: true });
  fs.writeFileSync(wrapperFilePath, wrapperDocument);
  fs.mkdirSync(path.dirname(typesFilePath), { recursive: true });
  fs.writeFileSync(typesFilePath, typesDocument);
})().catch(e => {
  console.error(e);
  process.exit(1);
});
