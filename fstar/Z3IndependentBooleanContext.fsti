module Z3IndependentBooleanContext

module N = Z3BooleanNormalForm

val contextual_equivalent (s t:N.formula)
  : result:bool{result == N.contextual_equivalent s t}
