# Experimental Javascript N-api support

This API binding is incomplete. See TODO list here: https://github.com/Z3Prover/z3/issues/1791

## How to build

- In the directory in which you checked out z3, run `python scripts/mk_make.py --js`
- In `src/api/js` run `pip install -r pip-requirements.txt`
- Run `npm install node-gyp` or `npm install -g node-gyp`
- `make`
- `node test.js`


```javascript
const z3 = require('./build/Release/addon');
const z3const = require('./z3_consts.js')
```
