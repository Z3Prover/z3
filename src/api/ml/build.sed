# attempt to clean up the mess with 'unsigned'
s/ unsigned/ unsigned int/g
s/unsigned int long/unsigned long/g
s/unsigned int __/unsigned __/g


# '@name ' -> 'Section: '
# '\sa ' -> 'See also: '
# '\brief '   -> 'Summary:  '
# '\remark ' -> 'Remark: '
# '\pre '     -> 'Precondition: '
# '\param '   -> '@param'
# '\warning ' -> 'Warning: '
# '\code' -> 'C Example:'
# '\endcode' -> ''
/\\pre/s/(/ /g;/\\pre/s/,//g;/\\pre/s/)//g;s/\\pre /- {b Precondition}: /g
/\\ccode/s/(/ /g;/\\ccode/s/\\,//g;/\\ccode/s/)//g;s/\\ccode{\(.*\)}/\[\1\]/g
s/\\defgroup .*//g
s/@name \(.*\)/{2 {L \1}}/g
s/\\sa \(.*\)/- {b See also}: {!Z3.\1}/g
s/\\see \(.*\)/- {b See}: {!Z3.\1}/g
s/<tt>/{e /g
s|</tt>| }|g
s/\\nicebox{/{e/g
s/\\brief /Summary: /g
s/\\remark /- {b Remarks}: /g
s/\\pre /- {b Precondition}: /g
s/\\param /@param /g
s/\\conly .*//g
s/\\warning /- {b Warning}: /g
s/\\code/{v /g
s/\\endcode/ v}/g
s/\\verbatim/{v /g
s/\\endverbatim/ v}/g
s/\\mlonly//g
s/\\endmlonly//g
s/\\mlh/\\\[ \[/g
s/\\endmlh/\] \\\]/g
s/\\deprecated/@deprecated/g
s/\\ / /g

# '\c code ' -> '[code]'
s/\\c \([^ .,:]*\)/[\1]/g

# '#Z3_' -> 'Z3.'
s/#Z3_\([^ \.,)	]*\)/{!Z3.\1}/g

# '/*@}*/' -> ''
s/\/\*@{\*\///g

# '/*@{*/' -> ''
s/\/\*@}\*\///g

# '/*...*/' -> ''
s/\/\*.*\*\///g

s|(\*\*/\*\*)|(\*\*%\*\*)|g

# '/**' -> 'quote(mli,"(**'
s|/\*\*|quote(mli,\"(**|g

# '...*/' -> '*)");'
s|[ 	  ]*\*/|*)\");|g

s|(\*\*%\*\*)|(\*\*/\*\*)|g

# 'extern "C"' -> 'extern ~~C~~'
# 'quote(foo,"bar")' -> quote(foo,~~bar~~)
# mltype("foo") -> mltype(~~foo~~)
s/extern \"C\"/extern ~~C~~/g
s/quote(\(.*\),\"\(.*\)\")/quote(\1,~~\2~~)/g
s/quote(\(.*\),\"/quote(\1,~~/g
s/\")\;/~~);/g
s/\;\"/;~~/g
s/mltype(\"\(.*\)\")/mltype(~~\1~~)/g

# '"' -> '\"'
s/\\\"/\"/g
s/\"/\\\"/g

# '~~' -> '"'
s/~~/\"/g
