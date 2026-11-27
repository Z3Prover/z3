module Z3IndependentNative

open FStar.All
module N = Z3Native
module Root = Z3SortedRootDocument

val check (assertions:list N.ast) (proof:N.ast) : ML Root.root_verdict
