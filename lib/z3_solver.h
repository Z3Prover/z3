/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    z3_solver.h

Abstract:

    Native ast parser.

Author:

    Nikolaj Bjorner (nbjorner) 2007-07-17

Revision History:

--*/

/**
  \defgroup z3native Z3 low level input format 

  This format is mainly used for generating logs. These logs
  capture the expressions created using the Z3 API, and 
  the main commands available there.
  It is very low-level and follows 
  some of the conventions found in the DIMACS format for SAT problems 
  and by the <a class="el" href="http://www.cs.ubc.ca/~babic/index_spear.htm">Spear</a>
  input format.

  The format is extensible, as the grammar allows for 
  selecting solvers and adding \emph{semantic attachments} 
  with constructors. The <a class="el" href="http://www.smtlib.org">SMT-LIB</a> and Simplify text formats are easier to
  write and read for a human consumer.

  Every line consists of a command that gets interpreted
  as a declaration of a node in anbstract syntax tree, or as
  a control instruction to Z3, such as to augment the current
  context with constraints or check for satisfiability.

  \nicebox{
    <i>command</i> := 
      | <i>ast</i>
      | <i>control </i>
      | <i> ; commented line </i>      
  }


  White spaces are implicit in the production rules.
  The legal white-spaces have the ASCII representations

  \nicebox{
     ' ' | \ t | \ r
  }

  Comment lines start with \c ;.
  All characters up to the newline \ n are ignored.

  We use <i>id</i> for identifiers in general. 
  Identifiers associated with certain semantic categories,
  such as \emph{ast} nodes, or \emph{type}s are 
  prefixed by the category and suffixed by \emph{id}.
  For example, we have:

  \nicebox{
   ast-id        - identifier for ast nodes 

   type-id       - identifier for type nodes 

   parameter-id  - identifier for ast 

   name-id       - identifier for a function/type name 

   decl-id       - identifier for declaration node 

   context-id    - identifier for Boolean context
  }   

  Identifiers can be any sequence of non-whitespace 
  and non-newline characters whose first character
  is not one of the decimal digits.
  Identifiers enclosed in quotes ''...''
  are treated specially: the quotes are stripped.
  Thus, the identifier consisting of zero characters
  is written ''''. The identifier ''null'' 
  is allowed for <em>skolem-id</em> and <em>quant-id</em>.
  
  \section nativecontrol Control commands

  To load a theory solver for integer linear arithmetic, 
  include a line of the form \ty{Solver LIA}. To load the
  mixed integer/real solver include instead a line of the
  form \ty{Solver LRA}

  Use \ty{Push} and \ty{Pop} to push/pop contexts 
  (constraints that are asserted 
  under a \ty{Push} are removed after a \ty{Pop}).
  To reset the state entirely, use \ty{Reset}.

  To assert a constraint use \ty{Assert} \emph{ast-id},
  where the \emph{ast-id} is an identifier declared
  for a boolean typed term.

  To check for satisfiability of all asserted constraints
  use \ty{Check}.

  \nicebox{
  <i>control</i> :=
     | Solver <i>solver</i>        - load specified theory solver 
     | Assert <i>ast-id</i>        - assert constraint 
     | Check                - check for satisfiability of asserts
     | Push                 - push a context
     | Pop                  - pop a context
     | Version <i>major minor build-number revision</i> - specify Z3 version

  <i>solver</i> :=
     | LRA                  - mixed integer/real arithmetic 
     | LIA                  - integer arithmetic}

  \section z3nativeast Abstract syntax trees

  Every node in the abstract syntax trees understood by Z3
  is declared by using a syntax category identifier, followed
  by a (unique) identifier that names the node. The
  node identifier is followed by a description of the node.

  In overview abstract syntax tree nodes are declared using the commands:

  \nicebox{
  <i>ast</i> :=
     | Type <i>id</i> <i>type</i> 
     | Dec <i>id</i> <i>declaration</i>
     | Const <i>id</i> <i>constant</i>             
     | Fun <i>id</i> <i>function</i>               
     | App <i>id</i> <i>built-in</i>               
     | Num <i>id</i> <i>numeral</i>                
     | Qua <i>id</i> <i>quantifier</i>                     
     | Var <i>id</i> <i>bound-variable</i>             
     | Ctx <i>id</i> <i>local-context</i>          
     | Lab <i>id</i> <i>label-term</i>         
     | Pat <i>id</i> <i>pattern</i> 
 }

 \subsection z3nativetypes Types

 Types are created from a name and optional parameters.
 A number of names are reserved for built-in theories.
 These names are:
 \nicebox{
    Int  Real  Bool  bv  array
 }
 When the name of a type is one of these, the type is automatically
 associated with the respective theory. 
 The \ty{bv} type takes one numeric parameter (the bit-width of the
 bit-vector), and \ty{array} takes <i>n+1</i> parameters (the <i>n</i> 
 types for the domain of the array and the last parameter for the
 range of the array.

 \nicebox{
 <i>type</i> := <i>name</i> '[' <i>parameter</i>* ']' 

 <i>parameter</i> := <i>number</i> | <i>ast-id</i> | <i>symbol</i>
 }
 A parameter can either be an integer, an identifier used for 
 another defined term or type, or a symbol. Symbols are given as
 strings. The parser first attempts to identify a parameter as
 a previously defined term or type, and if there is no 
 such previously defined term/type, then it treats the string
 as a symbol.

 \subsection nativez3Fuctions Function and constant declarations
 In Z3, functions are constants that take more than zero arguments,
 thus, everything is treated as a constant.

 Constant declarations comprise of a name, followed by
 a non-empty list of types, all but the first types
 are the domain of the function (there are no domain
 types for 0-ary constants), the last type is the range.
 A constant declaration is followed by optional 
 theory specific information.

 The codes used in the theory specific information is described under \ref theories 

 The theory specific information indicates
 whether the constant is associative/commutative/injective; 
 a list of parameters may also be used to indicate 
 auxiliary information for the constant declarations.

 \nicebox{
 <i>declaration</i> := <i>name-id</i> <i>type-id</i>* [<i>const-info</i>]

 <i>const-info</i> := BUILTIN <i>theory</i> <i>kind-num</i> (:assoc | :comm | :inj | <i>parameter</i>)*

 <i>theory</i> := 
    | basic -  built-in types and operations 
    | arith -  arithmetical 
    | bv    -  bit-vectors 
    | array -  arrays 
    | datatype - datatypes
 }


 \subsection z3nativeterms Terms


 Terms are built from constants, function applications,
 labeling, context formation, quantification
 and bound variables.

 A constant consists of a declarations, functions consist of
 a declaration followed by a non-empty list of term identifiers.
 All constants and function applications can be constructed using
 the \ty{Fun} construct. However, two shortcuts are available.

 <ul>
 <li> \ty{Const}:
 Constants may be defined directly by supplying the name and the type of the constant.
 </li>
 <li> \ty{App}:
 Built-in arithmetic, array, bit-vector, and Boolean operations may be applied directly
 to their arguments without first providing function declarations.
 </li>
 </ul>

  \nicebox{
  <i>constant</i>  := <i>name-id</i> <i>type-id</i>

  <i>function</i>  := <i>decl-id</i> <i>ast-id</i>* 

  <i>built-in</i>  := <i>name-id</i> [<i> [</i> <i>parameter</i>* ]</i> </i>] <i>ast-id</i>*
  }

 Labeled terms consist of a polarity (\ty{LBLPOS} for positive 
 context, \ty{LBLNEG} for negative contexts), a name, and a 
 term identifier.

 
  \nicebox{
  <i>label-term</i>  :=  (LBLPOS | LBLNEG) <i>label-name</i> <i>ast-id</i> 
  }

 Local contexts consist of an identifier for the underlying
 term, followed by a predicate summarizing the context in
 which the term is interpreted. 

  \nicebox{
  <i>local-context</i> :=  <i>ast-id</i> <i>context-id</i>
  }

 A quantifier consists of 
<ul>
<li> 
A number indiciating the
weight of the quantifier (for matching precedence),
<li> 
A skolem identifier, used for Boogie quantifier instantiation,
<li>
A quantifier identifier, used for profiling instantiations, 
<li>
A number indicating how many variables are bound by the quantifier, followed
by the bound variables, which are
<ul>
<li> A name for the bound variable.
<li> An identifier for the type of the bound variable.
</ul>
<li>
A number indicating how many patterns are associated with the quantifier,
followed by the patterns, which are
<ul>
<li> An identifier for the pattern.
</ul>
<li> An identifier for the body of the quantifier.
</ul>

  \nicebox{
  <i>quantifier</i>  :=  
      (FORALL | EXISTS) 
      <i>weight-num</i>  
      <i>skolem-id</i>
      <i>quant-id</i> 
      <i>decls-num</i>
      (<i>name-id</i> <i>type-id</i>)*
      <i>pattern-num</i>
      <i>pattern-id</i>*
      <i>ast-id</i>
  }

A bound variable consists of a de-Brujin index for the bound
variable together with the type of the bound variable.
While the type can be computed by matching the index of
the de-Brujin index with the associated quantifier, 

Patterns comprise of a list of terms.


  \nicebox{
  <i>bound-variable</i>  :=  <i>index-num</i> <i>type-id</i>

  <i>numeral</i>   :=  <i>rational</i> <i>type-id</i> 

  <i>rational</i>  :=  <i>number</i> [/<i>number</i>] 

  <i>number</i>    :=  [0-9]+

  <i>pattern</i>   :=  <i>id</i> <i>ast-id</i>*
  }


\section z3nativeexamples Examples

\subsection z3nativearithmetic Integer Arithmetic

Suppose we wish to check whether 
\nicebox{
       z0 >= 0 && z1 >= 0 && z2 >= 1 && z1 >= z2 && z2 >= z0
}
is satisfiable for <pre>z0, z1, z2</pre> integers. 
With the low-level input format, we may specify this by:

\nicebox{
   Type INT  Int
   Type BOOL Bool
   Const z0  z0 INT
   Const z1  z1 INT
   Const z2  z2 INT
   Num   0   0 INT
   Num   1   1 INT
   App c0 >= z0 0
   Assert c0
   App c1 >= z1 0
   Assert c1
   App c2 >= z2 1
   Assert c2
   App c3 >= z1 z2
   Assert c3
   App c4 >= z2 z0
   Assert c4
   Check
}


Notice that the identifiers may be arbitrary strings, including numerals.
So for instance, we used 1 to represent integer 1. 

\subsection z3nativebv Bit-vectors

We can check whether 32-bit addition is commutative. Z3 reports \ty{unsat}
in for the first check. The second satisfiable check illustrates the use of parameters
(\ty{extract} takes two integer parameters for the range of bits extracted
from the bit-vectors). 

\nicebox{
   Type bool Bool 
   Type bv32 bv [ 32 ]
   Type bv64 bv [ 64 ]
   Num 0 0 bv32
   Num 1 1 bv32
   Const x0 x0 bv32
   Const x1 x1 bv32
   Const x2 x2 bv64
   App a bvadd x0 x1
   App b bvadd x1 x0
   App eq = a b
   App constraint1 not eq
   Push
   Assert constraint1
   Check
   Pop
   App c extract [ 31 0 ] x2
   App eq2 = a c
   App constraint2 not eq2
   Push
   Assert constraint2
   Check
   Pop
}

We added the declarations of bit-vector constants 0 and 1. Like integers, 
these are also numerals, but with bit-vector type.


\subsection z3nativeexarray Arrays

The low-level version of:
\nicebox{
   store(f1,i1,v1) = store(f2,i2,v2) && i1 != i3 && i2 != i3 && select(f1,i3) != select(f2,i3)
}
is:

\nicebox{
  Type Index Index
  Type Elem Elem
  Type Array array [ Index Elem ]
  Type bool Bool
  Const i1 i1 Index
  Const i2 i2 Index
  Const i3 i3 Index
  Const v1 v1 Elem
  Const v2 v2 Elem
  Const f1 f1 Array
  Const f2 f2 Array
  App n1 store f1 i1 v1
  App n2 store f2 i2 v2
  App n3 = n1 n2
  App n4 = i1 i3
  App n5 not n4
  App n6 = i2 i3
  App n7 not n6 
  App n8 select f1 i3
  App n9 select f2 i3
  App n10 = n8 n9
  App n11 not n10
  Assert n3
  Assert n5
  Assert n7
  Assert n11
  Check
}

\subsection z3nativeexdatatype Data-types

To check projection over tuples
\nicebox{
  (= x (first (mk_tuple x y)))
}

we write:
\nicebox{
  Type int Int
  Type pair tuple [ mk_tuple first int second int ]
  Const x x int
  Const y y int
  Const p p pair
  App n1 mk_tuple x y
  App n2 first n1
  App n3 = n2 x
  App n4 not n3
  Assert n4
  Check
}


*/

 /**

  \defgroup theories Z3 theories


  \section theorisbasics Basics

There is a single basic sort, \ty{bool}, which has op-code 0.
The basic operators are, listed with their codes in the table below.

<table border cellspacing=5 cellpadding=10>
<tr>
 <th>Op-code</th>
 <th>Mnmonics</th>
 <th>Description</th>
</tr>
<tr><td>0</td><td> \ty{true} </td><td> the constant \emph{true} </td></tr>
<tr><td>1</td><td> \ty{false} </td><td> the constant \emph{false} </td></tr>
<tr><td>2</td><td> \ty{=} </td><td> equality</td></tr>
<tr><td>3</td><td> \ty{distinct} </td><td> distincinctness </td></tr>
<tr><td>4</td><td> \ty{ite} </td><td> if-then-else </td></tr>
<tr><td>5</td><td> \ty{and} </td><td> n-ary conjunction </td></tr>
<tr><td>6</td><td> \ty{or} </td><td> n-ary disjunction </td></tr>
<tr><td>7</td><td> \ty{iff} </td><td> bi-impliciation </td></tr>
<tr><td>8</td><td> \ty{xor} </td><td> exclusive or </td></tr>
<tr><td>9</td><td> \ty{not} </td><td> negation </td></tr>
<tr><td>10</td><td> \ty{implies} </td><td> implication </td></tr>
</table> 

  \section theoriesarithmetic Arithmetic

  \subsection tharithbuiltin Built-in operators

  Arithmetical expression can be built from reals or integers.
  The arithmetical sorts are listed below
  and the supported operations are listed in the table thereafter.

<table border cellspacing=5 cellpadding=10>
<tr>
 <th>Op-code</th>
 <th>Mnmonics</th>
 <th>Description</th>
</tr>
<tr><td>0</td> <td>\ty{real}</td> <td> sort of reals</td></tr>
<tr><td>1</td> <td>\ty{int}</td> <td> sort of integers</td></tr>
</table>

<table border cellspacing=5 cellpadding=10>
<tr>
 <th>Op-code</th>
 <th>Mnmonics</th>
 <th>Description</th>
</tr>
<tr><td>0</td> <td> \ty{<=} </td><td> less-than or equal </td></tr>
<tr><td>1</td> <td> \ty{>=} </td><td> greater-than or equal </td></tr>
<tr><td>2</td> <td> \ty{<} </td><td> less-than </td></tr>
<tr><td>3</td> <td> \ty{>} </td><td>  greater-than </td></tr>
<tr><td>4</td> <td> \ty{+} </td><td>  n-ary addition </td></tr>
<tr><td>5</td> <td> \ty{-} </td><td>  binary minus </td></tr>
<tr><td>6</td> <td> \ty{~} </td><td> unary minus </td></tr>
<tr><td>7</td> <td> \ty{*} </td><td>  n-ary multiplication </td></tr>
<tr><td>8</td> <td> \ty{/} </td><td>  rational division </td></tr>
<tr><td>9</td> <td> \ty{div} </td><td>  integer division </td></tr>
<tr><td>10</td> <td> \ty{rem} </td><td>  integer remainder </td></tr>
<tr><td>11</td> <td> \ty{mod} </td><td>  integer modulus </td></tr>
</table>

  \section theoriesbv Bit-vectors
To indicate the bit-vector length one adds a numeral parameter
with the number of bits the bit-vector holds.
For instance, a declaration of the form:

\nicebox{
  Type $1 bv [ 32 ] 
}

declares a 32-bit bit-vector type.

  
<table border cellspacing=5 cellpadding=10>
<tr>
 <th>Op-code</th>
 <th>Mnmonics</th>
 <th>Parameters</th>
 <th>Description</th>
</tr>
<tr><td>0</td> <td> \ty{bit1} </td> <td></td> <td>constant comprising of a single bit set to 1</td></tr>
<tr><td>1 </td><td> \ty{bit0} </td><td> </td><td>  constant comprising of a single bit set to 0. </td></tr>
<tr><td>2 </td><td> \ty{bvneg} </td><td> </td><td> Unary subtraction. </td></tr>
<tr><td>3 </td><td> \ty{bvadd} </td><td> </td><td>  addition. </td></tr>
<tr><td>4 </td><td> \ty{bvsub} </td><td> </td><td>  subtraction. </td></tr>
<tr><td>5 </td><td> \ty{bvmul} </td><td> </td><td>  multiplication. </td></tr>
<tr><td>6 </td><td> \ty{bvsdiv} </td><td> </td><td>  signed division. </td></tr>
<tr><td>7 </td><td> \ty{bvudiv} </td><td> </td><td>  unsigned division. 
The operands are treated as unsigned numbers. </td></tr> 
<tr><td>8 </td><td> \ty{bvsrem} </td><td> </td><td>   signed remainder. </td></tr>
<tr><td>9 </td><td> \ty{bvurem} </td><td> </td><td>   unsigned remainder. </td></tr>
<tr><td>10 </td><td> \ty{bvsmod} </td><td> </td><td>   signed modulus. </td></tr>
<tr><td>11 </td><td> \ty{bvule} </td><td> </td><td>   unsigned \ty{<=}. </td></tr>
<tr><td>12 </td><td> \ty{bvsle} </td><td> </td><td>   signed \ty{<=}. </td></tr>
<tr><td>13</td><td> \ty{bvuge} </td><td> </td><td>   unsigned \ty{>=}. </td></tr>
<tr><td>14 </td><td> \ty{bvsge} </td><td> </td><td>  signed \ty{>=}. </td></tr>
<tr><td>15 </td><td> \ty{bvult} </td><td> </td><td>  unsigned \ty{<}. </td></tr>
<tr><td>16 </td><td> \ty{bvslt} </td><td> </td><td>  signed \ty{<}. </td></tr>
<tr><td>17 </td><td> \ty{bvugt} </td><td> </td><td>  unsigned \ty{>}. </td></tr>
<tr><td>18 </td><td> \ty{bvsgt} </td><td> </td><td>  signed \ty{>}. </td></tr>
<tr><td>19 </td><td> \ty{bvand} </td><td> </td><td>  n-ary (associative/commutative) bit-wise and. </td></tr> 
<tr><td>20 </td><td> \ty{bvor} </td><td> </td><td>  n-ary (associative/commutative) bit-wise or. </td></tr>
<tr><td>21 </td><td> \ty{bvnot} </td><td> </td><td>  bit-wise not. </td></tr>
<tr><td>22 </td><td> \ty{bvxor} </td><td> </td><td>  n-ary bit-wise xor. </td></tr>
<tr><td>23 </td><td> \ty{bvnand} </td><td> </td><td>  bit-wise nand. </td></tr>
<tr><td>24 </td><td> \ty{bvnor} </td><td> </td><td>  bit-wise nor. </td></tr>
<tr><td>25 </td><td> \ty{bvxnor} </td><td> </td><td>  bit-wise exclusive nor. </td></tr>
<tr><td>26 </td><td> \ty{concat} </td><td> </td><td>  bit-vector concatentaion. </td></tr>
<tr><td>27 </td><td> \ty{sign\_extend} </td><td> \emph{n}</td><td>  \emph{n}-bit sign extension. </td></tr>
<tr><td>28</td><td> \ty{zero\_extend} </td><td> \emph{n}</td><td>  \emph{n}-bit  zero extension. </td></tr>
<tr><td>29 </td><td> \ty{extract} </td><td> \emph{hi:low} </td><td>  \emph{hi}-\emph{low} bit-extraction. </td></tr>
<tr><td>30 </td><td> \ty{repeat} </td><td> \emph{n} </td><td>  repeat $n$ times. </td></tr>
<tr><td>31 </td><td> \ty{bvredor} </td><td> </td><td>  or-reduction. </td></tr>
<tr><td>32 </td><td> \ty{bvredand} </td><td> </td><td>  and-reducdtion. </td></tr>
<tr><td>33 </td><td> \ty{bvcomp} </td><td> </td><td>  bit-vector comparison. </td></tr>
<tr><td>34 </td><td> \ty{bvshl} </td><td> </td><td>  shift-left. </td></tr>
<tr><td>35 </td><td> \ty{bvlshr} </td><td> </td><td>  logical shift-right. </td></tr>
<tr><td>36 </td><td> \ty{bvrshr} </td><td> </td><td>  arithmetical shift-right. </td></tr>
<tr><td>37 </td><td> \ty{bvrotate\_left} </td><td> \emph{n} </td><td>  \emph{n}-bit left rotation. </td></tr>
<tr><td>38 </td><td> \ty{bvrotate\_right} </td><td>\emph{n} </td><td>  \emph{n}-bit right rotation.  </td></tr>
</table>

\section theoriesarrays Arrays

\subsection tharraybuiltinops Built-in operators

  There is a single built-in sort constructor for arrays with code 0.
  It is followed by a sequence of parameters indicating the domain
  sorts and the range of the array.

<table border cellspacing=5 cellpadding=10>
<tr>
 <th>Op-code</th>
 <th>Mnmonics</th>
 <th>Description</th>
</tr>
<tr><td>0</td><td> \ty{store} </td><td>  array store </td></tr>
<tr><td>1</td><td> \ty{select} </td><td>  array select </td></tr>
<!---
<tr><td></td><td> \ty{const} </td><td> array returning constant value </td></tr>
%\begin{internal}
<tr><td></td><td> \ty{store\_ite} </td><td> ternary non-pointwise store</td></tr>
<tr><td></td><td> \ty{set\_union} </td><td> set union A u B </td></tr>
<tr><td></td><td> \ty{set\_intersect} </td><td> set intersection A n B </td></tr>
<tr><td></td><td> \ty{set\_difference} </td><td> set difference A \ B </td></tr>
<tr><td></td><td> \ty{set\_complement} </td><td> set complement C(A) </td></tr>
<tr><td></td><td> \ty{is\_subset} </td><td> non-strict subset: A <= B </td></tr>
--->
</table>

  In the low-level input format, array types
  are accompanied by a sequence of identifiers corresponding
  to the domain and range of the array the operations operate
  upon.
  In more detail, the contract is that the supplied parameters
  to the type declaration of an array are of the form:

  <ul>
  <li> parameter_0 - 1'st dimension 
  <li> parameter_{n-1} - n'th dimension
  <li> parameter_n - range
  </ul>

 The constant array function symbol \ty{const} needs a parameter
 in order to infer the types of the indices of the constant array.
 We pass the array type as the parameter to \ty{const}. 
 The other array operations do not need parameters.

 We summarize the arities and semantics of the operators:

 <ul>
 <li> \ty{store} - 
      
Updates an array at a given index with a value:
 \ty{store}(A, i0, ... i_{n-1}, v) has the same contents as A, except on
index i0, ... , i_{n-1}, where the value is v.

 <li> \ty{select} - 
  
  Selects the value from an array: 
  \ty{select}(A, i0, ... , i_{n-}) selects the value stored at
  index i0, ... , i_{n-1}.
 </ul>

<!---
 
\\
{\tt const} \\
\> 
\begin{minipage}[t]{5in}
Creates a constant array: ${\tt const}(v)$ maps every index in the domain of the array to $v$.
\end{minipage}
\internalonly{
\\
{\tt store\_ite} \\
\> 
\begin{minipage}[t]{5in}
Creates an array using a test and two other arrays: 
\[
\begin{array}{lll}
        {\tt select}(A,\overline{i}) = {\tt select}(B, \overline{i}) & \rightarrow & 
        {\tt select}({\tt store\_ite}(A,B,C), \overline{i}) = {\tt select}(C,\overline{i}) \ \
        {\tt select}(A,\overline{i}) \neq {\tt select}(B, \overline{i}) & \rightarrow & 
        {\tt select}({\tt store\_ite}(A,B,C), \overline{i}) = {\tt select}(B,\overline{i})
\end{array}		
\]
\end{minipage}
\\
{\tt set\_union}, {\tt set\_intersect} \\
\>
\begin{minipage}[t]{5in}
Creates the union, intersection of the list of arguments. Each argument must be declared as an array of the same type, 
and the range type must be {\tt bool}.
\end{minipage}
\\
{\tt set\_difference} \\
\>
\begin{minipage}[t]{5in}
Creates the set difference of two arrays. The arguments must be declared as arrays of the same type with range type {\tt bool}
\end{minipage}
\\
{\tt set\_complement}\\
\>
\begin{minipage}[t]{5in}
Set complement of one Boolean valued array.
\end{minipage}
\\
{\tt is\_subset} \\
\>
\begin{minipage}[t]{5in}
Subset test of two Boolean valued arrays of the same type.
\end{minipage}
} % internalonly
\end{tabbing}
--->


 */
#ifndef _Z3_SOLVER_H_
#define _Z3_SOLVER_H_

#include "ast.h"
#include "symbol_table.h"
#include "stream_buffer.h"
#include "warning.h"
#include "front_end_params.h"
#include "arith_decl_plugin.h"
#include "bv_decl_plugin.h"
#include "z3.h"


class z3_solver {
    
    enum kind {
        T_NUM,
        T_VAR,
        T_DEC,
        T_FUNCTION_CONST,
        T_GET_IMPLIED_EQUALITIES,
        T_NULLARY_CONST,
        T_BUILTIN_CONST,
        T_TY,
        T_TYPE,
        T_QUA,
        T_LAB,
        T_CTX,
        T_PAT,

        T_SOLVER,
        T_SIMPLIFY,

        T_ASSERT,
        T_CHECK,
        T_CHECK_ASSUMPTIONS,
        T_DBG_SAT,
        T_DBG_UNSAT,
        T_PUSH,
        T_POP,
        T_RESET,
        T_ECHO,
        T_VERSION,
       
        T_COMMENT,

        T_EOF,
        T_ERR
    };

    struct builtin_info {
        family_id m_fid;
        decl_kind m_kind;
        builtin_info(family_id fid, decl_kind k) : m_fid(fid), m_kind(k) {}
        builtin_info(): m_fid(null_family_id), m_kind(null_decl_kind) {}
    };

    Z3_context         m_context;
    bool               m_owns_context;
    ast_manager&       m_manager;
    front_end_params&  m_params;
    symbol_table<ast*> m_table;
    stream_buffer      m_in;
    std::ostream&      m_out;
    bool               m_is_active;
    expr_ref_vector    m_assumptions;
    unsigned_vector    m_assumptions_lim;
    unsigned           m_num_checks;
    std::string        m_string;
    bool               m_eof;
    unsigned           m_line;
    symbol_table<builtin_info> m_builtin_ops;
    symbol_table<builtin_info> m_builtin_types;
    arith_util         m_arith;
    bv_util            m_bv;
    ast_ref_vector     m_pinned;
    unsigned_vector    m_pinned_lim;
    Z3_lbool           m_last_check_result;
    
public:        

    z3_solver(
        Z3_context    c,
        std::istream& is,
        std::ostream& os,
        front_end_params & params,
        bool is_active = true
        );

    z3_solver(
        ast_manager&  m,
        std::istream& is,
        std::ostream& os,
        front_end_params & params
        );

    ~z3_solver();

    bool parse();

    void get_assumptions(expr_ref_vector& v) { v.append(m_assumptions); }

    void display_statistics(std::ostream& out, bool istats);

    void set_error_handler(Z3_error_handler h) {
        Z3_set_error_handler(m_context, h);
    }
    
private:

    template<typename T>
    struct coerce {
        virtual ~coerce() {}
        virtual T* operator()(ast* a) const = 0; 
    };

    struct sort_coerce : public coerce<sort> {
        virtual sort* operator()(ast* a) const { 
            if (!a || a->get_kind() != AST_SORT) {
                return 0;
            }
            return to_sort(a); 
        }
    };

    struct func_decl_coerce : public coerce<func_decl> {
        virtual func_decl* operator()(ast* a) const { 
            if (!a || a->get_kind() != AST_FUNC_DECL) {
                return 0;
            }
            return to_func_decl(a); 
        }
    };

    struct pattern_coerce : public coerce<app> {
        ast_manager& m_manager;
        pattern_coerce(ast_manager& m): m_manager(m) {}
        virtual app* operator()(ast* a) const { 
            if (!a || a->get_kind() != AST_APP) {
                return 0;
            }
            if (!m_manager.is_pattern(to_app(a))) {
                return 0;
            }
            return to_app(a);
        }
    };

    struct expr_coerce : public coerce<expr> {
        virtual expr* operator()(ast* a) const { 
            if (!a) {
                return 0;
            }
            ast_kind k = a->get_kind();
            switch(k) {
            case AST_APP:
            case AST_QUANTIFIER:
            case AST_VAR:
                return reinterpret_cast<expr*>(a);
            default:
                return 0;
            }
        }
    };

    struct app_coerce : public coerce<app> {
        virtual app* operator()(ast* a) const { 
            if (!a) {
                return 0;
            }
            if (a->get_kind() == AST_APP) {
                return to_app(a);
            }
            return 0;
        }
    };
  

    template<typename T>
    bool parse_ast(symbol id, T*& n, const coerce<T>& coerce)
    {
        ast* a;                                                         
        if (!m_table.find(id, a)) {
            warning_msg("line %d. Could not find id '%s'\n", 
                        m_line, id.str().c_str());    
            return false;                                               
        }                              
        n = coerce(a);
        if (n == 0) {
            warning_msg("line %d. Wrong kind %d for %s\n", 
                        m_line, a->get_kind(), id.str().c_str());             
            return false;                                               
        }                                                               
        return true;                                                       
    }

   
    template<typename T>
    bool parse_ast(T*& n, const coerce<T>& coerce)
    {
        symbol id;                                                      
        if (parse_id(id)) { 
            return parse_ast(id, n, coerce);
        }                                                                   
        return false;                                                       
    }


    template<typename T>
    bool parse_asts(ref_vector<T, ast_manager>& asts, const coerce<T>& c)
    {
        symbol id;
        T*   n;
        while (m_string[0] != '\n') {
            if (strcmp(m_string.c_str(), "BUILTIN") == 0) {
                return true;
            }
            if (!parse_ast(n,c)) {
                return false;
            }
            asts.push_back(n);
        }
        return true;
    }

    kind parse_kind();

    bool next_token();

    bool parse_id(symbol& id);

    bool parse_rational(rational& r);

    void skip_blank();

    bool parse_eol();

    bool parse_numeral();

    bool parse_var();

    bool parse_info(scoped_ptr<func_decl_info>& info);

    bool parse_info(scoped_ptr<sort_info>& info);

    bool parse_func_decl();

    bool parse_func_decl(symbol& id, func_decl*& d);

    bool parse_nullary_const();

    bool parse_const();

    bool parse_builtin_const();

    bool parse_type();

    bool parse_type_new();

    bool parse_label();

    bool parse_quantifier();

    bool parse_pattern();

    bool parse_int(int& i);

    bool check_int(int& i);

    bool parse_unsigned(unsigned& i);

    bool check_unsigned(unsigned& i);

    bool try_parse(char const* token);

    bool parse_assert();

    bool parse_simplify();

    bool parse_check();

    bool parse_check_assumptions();

    bool parse_get_implied_equalities();

    bool parse_dbg(bool expected_sat);
    
    bool parse_push();

    bool parse_comment();
    
    bool parse_pop();

    bool parse_reset();

    bool parse_echo();

    bool parse_version();

    bool parse_solver();

    bool parse_parameter(vector<parameter>& params);

    bool parse_params(vector<parameter>& params);
    
    bool find_builtin_op(symbol name, family_id & fid, decl_kind& kind);

    bool find_builtin_type(symbol name, family_id & fid, decl_kind& kind);

    void add_builtins(family_id fid);

    void add_id(symbol const& id, ast* a);

    family_id get_family_id(char const* s);

    void dump_smtlib_benchmark(unsigned num_assumptions, expr* const* assumptions, Z3_lbool result);
};

#endif
