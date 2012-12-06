# remove 'z3_' and 'Z3_' prefixes on names

s/{\!Z3\./{\!/g
s/\([^_]\)[zZ]3_/\1/g

# remove cyclic definitions introduced by substituting type equations

s/^and \([a-z][a-zA-Z_ ]*\) = \1$//g
