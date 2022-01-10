'use strict';

// this is called by build.sh to generate the names of the bindings to export

let { functions } = require('./parse-api.js');
let asyncFns = require('./async-fns.js');

let extras = asyncFns.map(f => '_async_' + f);
let fns = functions.filter(f => !asyncFns.includes(f.name));

console.log(JSON.stringify([...extras, ...functions.map(f => '_' + f.name)]));
