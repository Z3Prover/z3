# Experimental n-api support

## How to build

- Install [opam](https://opam.ocaml.org/)
- `opam install ocaml core cil`
- `pip install -r pip-requirements.txt`
- `make`
- `node test.js`

These steps should produce two files that you can use via the require function of Node.js, as follows:

```javascript
const z3 = require('./build/Release/addon');
const z3const = require('./z3_consts.js')
```

See [test.js](./test.js) for examples.

## How it works

This tool parses the C API of Z3 (z3*.h) and converts it into two files, containing the API methods ([z3.cc](./z3.cc)) and constants ([z3_consts.js](./z3_consts.js)), respectively. Parsing happens in cdecl2napi.ml. Writing happens via a jinja template ([z3.cc.j2](./z3.cc.j2)).

## TODO

- This is the first working version of the API. It needs testing - please feel free to add tests and submit issues and pull requests if you find bugs
- Add a higher layer of abstraction to improve the API's usability
