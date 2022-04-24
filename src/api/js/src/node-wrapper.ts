// @ts-ignore no-implicit-any
import initModule = require('./z3-built.js');

// @ts-ignore no-implicit-any
import { init as initWrapper } from './wrapper';

export * from './wrapper';
export function init() {
  return initWrapper(initModule);
}
