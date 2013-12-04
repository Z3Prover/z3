/* A Bison parser, made by GNU Bison 2.4.2.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2006, 2009-2010 Free Software
   Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.4.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 0



/* Copy the first part of user declarations.  */

/* Line 189 of yacc.c  */
#line 2 "tptp5.y"

//-----------------------------------------------------------------------------
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
//-----------------------------------------------------------------------------
//----Compile with -DP_VERBOSE=1 for verbose output.
#ifndef P_VERBOSE
#  define P_VERBOSE 0
#endif
int verbose = P_VERBOSE;

//----Compile with -DP_USERPROC=1 to #include p_user_proc.c. p_user_proc.c 
//----should #define P_ACT, P_BUILD, P_TOKEN, P_PRINT to different procedures 
//----from those below, and supply code.
#ifdef P_USERPROC

#else
#  define P_ACT(ss) if(verbose)printf("%7d %s\n",yylineno,ss);
#  define P_BUILD(sym,A,B,C,D,E,F,G,H,I,J) pBuildTree(sym,A,B,C,D,E,F,G,H,I,J)
#  define P_TOKEN(tok,symbolIndex) pToken(tok,symbolIndex)
#  define P_PRINT(ss) if(verbose){printf("\n\n");pPrintTree(ss,0);}
#endif

extern int yylineno;
extern int yychar;
extern char yytext[];

extern int tptp_store_size;
extern char* tptp_lval[];

#define MAX_CHILDREN 12
typedef struct pTreeNode * pTree;
struct pTreeNode {
    char* symbol; 
    int symbolIndex; 
    pTree children[MAX_CHILDREN+1];
};
//-----------------------------------------------------------------------------
int yyerror( char const *s ) { 

    fprintf( stderr, "%s in line %d at item \"%s\".\n", s, yylineno, yytext); 
	return 0;
}
//-----------------------------------------------------------------------------
pTree pBuildTree(char* symbol,pTree A,pTree B,pTree C,pTree D,pTree E,pTree F, 
pTree G, pTree H, pTree I, pTree J) { 

    pTree ss = (pTree)calloc(1,sizeof(struct pTreeNode));

    ss->symbol = symbol;
    ss->symbolIndex = -1;
    ss->children[0] = A; 
    ss->children[1] = B; 
    ss->children[2] = C;
    ss->children[3] = D;
    ss->children[4] = E;
    ss->children[5] = F;
    ss->children[6] = G;
    ss->children[7] = H;
    ss->children[8] = I;
    ss->children[9] = J;
    ss->children[10] = NULL;

    return ss; 
}
//-----------------------------------------------------------------------------
pTree pToken(char* token, int symbolIndex) { 

    //char pTokenBuf[8240];
    pTree ss;
    char* symbol = tptp_lval[symbolIndex];
    char* safeSym = 0;

    //strncpy(pTokenBuf, token, 39);
    //strncat(pTokenBuf, symbol, 8193);
    //safeSym = strdup(pTokenBuf);
    ss = pBuildTree(safeSym,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);
    ss->symbolIndex = symbolIndex;

    return ss; 
}
//-----------------------------------------------------------------------------
void pPrintComments(int start, int depth) { 

    int d, j;
    char c1[4] = "%", c2[4] = "/*";

    j = start;
    while (tptp_lval[j] != NULL && (tptp_lval[j][0]==c1[0] || 
(tptp_lval[j][0]==c2[0] && tptp_lval[j][1]==c2[1]))) { 
        for (d=0; d<depth-1; d++) {
            printf("| ");
        }
        printf("%1d ",depth % 10);
        printf("%s\n",tptp_lval[j]);
        j = (j+1)%tptp_store_size; 
    }
    return; 
}
//-----------------------------------------------------------------------------
void pPrintTree(pTree ss, int depth) { 

//----pPrintIdx is where to find top-level comments to print before a sentence. 
//----yywrap() gets those after last sentence.
    static int pPrintIdx = 0;
    int i, d;

    if (pPrintIdx >= 0) { 
        pPrintComments(pPrintIdx, 0); 
        pPrintIdx = -1;
    }
    if (ss == NULL) {
        return;
    }
    for (d = 0; d < depth-1; d++) {
        printf("| ");
    }
    printf("%1d ",depth % 10);
    if (ss->children[0] == NULL) {
        printf("%s\n", ss->symbol);
    } else {
        printf("<%s>\n", ss->symbol);
    }
    if (strcmp(ss->symbol, "PERIOD .") == 0) {
        pPrintIdx = (ss->symbolIndex+1) % tptp_store_size;
    }
    if (ss->symbolIndex >= 0) {
        pPrintComments((ss->symbolIndex+1) % tptp_store_size, depth);
    }
    i = 0;
    while(ss->children[i] != NULL) {
        pPrintTree(ss->children[i],depth+1); 
        i++;
    }
    return; 
}
//-----------------------------------------------------------------------------
int yywrap(void) { 

    P_PRINT(NULL); 
    return 1; 
}
//-----------------------------------------------------------------------------


/* Line 189 of yacc.c  */
#line 219 "tptp5.tab.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     AMPERSAND = 258,
     AT_SIGN = 259,
     AT_SIGN_MINUS = 260,
     AT_SIGN_PLUS = 261,
     CARET = 262,
     COLON = 263,
     COLON_EQUALS = 264,
     COMMA = 265,
     EQUALS = 266,
     EQUALS_GREATER = 267,
     EXCLAMATION = 268,
     EXCLAMATION_EQUALS = 269,
     EXCLAMATION_EXCLAMATION = 270,
     EXCLAMATION_GREATER = 271,
     LBRKT = 272,
     LESS_EQUALS = 273,
     LESS_EQUALS_GREATER = 274,
     LESS_TILDE_GREATER = 275,
     LPAREN = 276,
     MINUS = 277,
     MINUS_MINUS_GREATER = 278,
     PERIOD = 279,
     QUESTION = 280,
     QUESTION_QUESTION = 281,
     QUESTION_STAR = 282,
     RBRKT = 283,
     RPAREN = 284,
     STAR = 285,
     TILDE = 286,
     TILDE_AMPERSAND = 287,
     TILDE_VLINE = 288,
     VLINE = 289,
     _DLR_cnf = 290,
     _DLR_fof = 291,
     _DLR_fot = 292,
     _DLR_itef = 293,
     _DLR_itetf = 294,
     _DLR_itett = 295,
     _DLR_tff = 296,
     _DLR_thf = 297,
     _LIT_cnf = 298,
     _LIT_fof = 299,
     _LIT_include = 300,
     _LIT_tff = 301,
     _LIT_thf = 302,
     arrow = 303,
     comment = 304,
     comment_line = 305,
     decimal = 306,
     decimal_exponent = 307,
     decimal_fraction = 308,
     distinct_object = 309,
     dollar_dollar_word = 310,
     dollar_word = 311,
     dot_decimal = 312,
     integer = 313,
     less_sign = 314,
     lower_word = 315,
     plus = 316,
     positive_decimal = 317,
     rational = 318,
     real = 319,
     signed_integer = 320,
     signed_rational = 321,
     signed_real = 322,
     single_quoted = 323,
     star = 324,
     unrecognized = 325,
     unsigned_integer = 326,
     unsigned_rational = 327,
     unsigned_real = 328,
     upper_word = 329,
     vline = 330
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 214 of yacc.c  */
#line 148 "tptp5.y"
int ival; double dval; char* sval; TreeNode* pval;


/* Line 214 of yacc.c  */
#line 334 "tptp5.tab.c"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


/* Copy the second part of user declarations.  */


/* Line 264 of yacc.c  */
#line 346 "tptp5.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1612

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  76
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  141
/* YYNRULES -- Number of rules.  */
#define YYNRULES  281
/* YYNRULES -- Number of states.  */
#define YYNSTATES  523

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   330

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     8,    10,    12,    14,    16,    18,
      20,    31,    42,    53,    64,    68,    70,    72,    74,    76,
      78,    80,    82,    84,    86,    88,    90,    94,    96,    98,
     100,   104,   108,   112,   116,   120,   124,   126,   128,   130,
     132,   134,   136,   140,   147,   149,   153,   155,   157,   161,
     166,   170,   172,   174,   178,   182,   184,   186,   188,   190,
     192,   196,   200,   204,   208,   212,   216,   218,   220,   223,
     227,   229,   233,   240,   242,   246,   250,   254,   263,   267,
     271,   273,   275,   277,   279,   281,   283,   285,   289,   291,
     293,   297,   301,   305,   309,   311,   313,   315,   317,   319,
     321,   325,   332,   334,   338,   340,   342,   346,   349,   351,
     355,   359,   361,   363,   365,   367,   369,   373,   375,   377,
     381,   385,   389,   393,   397,   404,   406,   410,   414,   419,
     423,   432,   436,   440,   442,   444,   446,   448,   450,   452,
     456,   458,   460,   464,   468,   472,   476,   478,   480,   482,
     484,   486,   488,   492,   499,   501,   505,   508,   510,   517,
     519,   523,   527,   532,   536,   545,   549,   553,   557,   559,
     561,   565,   567,   570,   572,   574,   576,   578,   582,   584,
     586,   588,   590,   592,   594,   596,   598,   600,   602,   604,
     606,   609,   611,   613,   615,   617,   619,   621,   623,   625,
     627,   629,   631,   633,   635,   637,   639,   641,   643,   645,
     647,   649,   653,   655,   657,   659,   661,   663,   665,   667,
     669,   671,   673,   675,   680,   682,   684,   686,   688,   690,
     692,   694,   696,   701,   703,   705,   707,   712,   714,   716,
     718,   720,   724,   733,   742,   744,   747,   749,   751,   758,
     763,   765,   767,   771,   773,   777,   779,   781,   786,   788,
     790,   792,   794,   799,   804,   809,   814,   819,   822,   826,
     828,   832,   834,   836,   838,   840,   842,   844,   846,   848,
     850,   852
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
      77,     0,    -1,   216,    -1,    77,    78,    -1,    79,    -1,
     202,    -1,    80,    -1,    81,    -1,    82,    -1,    83,    -1,
      47,    21,   210,    10,    85,    10,    86,    84,    29,    24,
      -1,    46,    21,   210,    10,    85,    10,   117,    84,    29,
      24,    -1,    44,    21,   210,    10,    85,    10,   142,    84,
      29,    24,    -1,    43,    21,   210,    10,    85,    10,   158,
      84,    29,    24,    -1,    10,   199,   200,    -1,   216,    -1,
      60,    -1,    87,    -1,   116,    -1,    88,    -1,    94,    -1,
     100,    -1,   102,    -1,    89,    -1,    90,    -1,   105,    -1,
      94,   164,    94,    -1,    91,    -1,    92,    -1,    93,    -1,
      94,    34,    94,    -1,    91,    34,    94,    -1,    94,     3,
      94,    -1,    92,     3,    94,    -1,    94,     4,    94,    -1,
      93,     4,    94,    -1,    95,    -1,    99,    -1,   109,    -1,
     110,    -1,   112,    -1,   115,    -1,    21,    87,    29,    -1,
     163,    17,    96,    28,     8,    94,    -1,    97,    -1,    97,
      10,    96,    -1,    98,    -1,   196,    -1,   196,     8,   103,
      -1,   165,    21,    87,    29,    -1,   101,     8,   103,    -1,
     109,    -1,   110,    -1,    21,    87,    29,    -1,   185,   166,
     185,    -1,    87,    -1,    94,    -1,   106,    -1,   107,    -1,
     108,    -1,   104,    48,   104,    -1,   104,    48,   106,    -1,
     104,    30,   104,    -1,   107,    30,   104,    -1,   104,    61,
     104,    -1,   108,    61,   104,    -1,   182,    -1,   161,    -1,
      17,    28,    -1,    17,   111,    28,    -1,    94,    -1,    94,
      10,   111,    -1,     9,    17,   113,    28,     8,    94,    -1,
     114,    -1,   114,    10,   113,    -1,    97,     9,    87,    -1,
      21,   114,    29,    -1,    38,    21,    87,    10,    87,    10,
      87,    29,    -1,   110,   171,   110,    -1,    21,   116,    29,
      -1,   118,    -1,   130,    -1,   141,    -1,   119,    -1,   124,
      -1,   120,    -1,   121,    -1,   124,   168,   124,    -1,   122,
      -1,   123,    -1,   124,    34,   124,    -1,   122,    34,   124,
      -1,   124,     3,   124,    -1,   123,     3,   124,    -1,   125,
      -1,   129,    -1,   173,    -1,   137,    -1,   196,    -1,   140,
      -1,    21,   118,    29,    -1,   167,    17,   126,    28,     8,
     124,    -1,   127,    -1,   127,    10,   126,    -1,   128,    -1,
     196,    -1,   196,     8,   134,    -1,   170,   124,    -1,   162,
      -1,   131,     8,   132,    -1,    21,   130,    29,    -1,   186,
      -1,   195,    -1,   134,    -1,   135,    -1,   134,    -1,    21,
     136,    29,    -1,   211,    -1,   172,    -1,   133,    48,   134,
      -1,    21,   135,    29,    -1,   134,    30,   134,    -1,   136,
      30,   134,    -1,    21,   136,    29,    -1,     9,    17,   138,
      28,     8,   124,    -1,   139,    -1,   139,    10,   138,    -1,
     196,     9,   118,    -1,   196,     8,    22,   182,    -1,    21,
     139,    29,    -1,    38,    21,   118,    10,   118,    10,   118,
      29,    -1,   118,   171,   118,    -1,    21,   141,    29,    -1,
     143,    -1,   157,    -1,   144,    -1,   149,    -1,   145,    -1,
     146,    -1,   149,   168,   149,    -1,   147,    -1,   148,    -1,
     149,    34,   149,    -1,   147,    34,   149,    -1,   149,     3,
     149,    -1,   148,     3,   149,    -1,   150,    -1,   152,    -1,
     173,    -1,   153,    -1,   196,    -1,   156,    -1,    21,   143,
      29,    -1,   167,    17,   151,    28,     8,   149,    -1,   196,
      -1,   196,    10,   151,    -1,   170,   149,    -1,   162,    -1,
       9,    17,   154,    28,     8,   149,    -1,   155,    -1,   155,
      10,   154,    -1,   196,     9,   143,    -1,   196,     8,    22,
     182,    -1,    21,   155,    29,    -1,    38,    21,   143,    10,
     143,    10,   143,    29,    -1,   143,   171,   143,    -1,    21,
     157,    29,    -1,    21,   159,    29,    -1,   159,    -1,   160,
      -1,   159,    34,   160,    -1,   173,    -1,    31,   173,    -1,
     162,    -1,   164,    -1,   169,    -1,   165,    -1,   182,   180,
     182,    -1,   167,    -1,     7,    -1,    16,    -1,    27,    -1,
       6,    -1,     5,    -1,   179,    -1,   180,    -1,   168,    -1,
     170,    -1,    15,    -1,    26,    -1,    59,    59,    -1,    13,
      -1,    25,    -1,    19,    -1,    12,    -1,    18,    -1,    20,
      -1,    33,    -1,    32,    -1,    34,    -1,     3,    -1,    31,
      -1,    23,    -1,   212,    -1,   174,    -1,   175,    -1,   181,
      -1,   184,    -1,   176,    -1,   177,    -1,   190,    -1,   182,
     178,   182,    -1,   179,    -1,    11,    -1,    14,    -1,   193,
      -1,   183,    -1,   196,    -1,   198,    -1,   184,    -1,   187,
      -1,   193,    -1,   185,    -1,   186,    21,   197,    29,    -1,
     186,    -1,   211,    -1,   188,    -1,   189,    -1,   214,    -1,
      54,    -1,   190,    -1,   191,    -1,   192,    21,   197,    29,
      -1,   192,    -1,   212,    -1,   194,    -1,   195,    21,   197,
      29,    -1,   195,    -1,   213,    -1,    74,    -1,   182,    -1,
     182,    10,   197,    -1,    40,    21,   118,    10,   182,    10,
     182,    29,    -1,    39,    21,   143,    10,   182,    10,   182,
      29,    -1,   205,    -1,    10,   201,    -1,   216,    -1,   208,
      -1,    45,    21,   215,   203,    29,    24,    -1,    10,    17,
     204,    28,    -1,   216,    -1,   210,    -1,   210,    10,   204,
      -1,   206,    -1,   206,     8,   205,    -1,   208,    -1,   211,
      -1,   211,    21,   209,    29,    -1,   196,    -1,   214,    -1,
      54,    -1,   207,    -1,    42,    21,    86,    29,    -1,    41,
      21,   117,    29,    -1,    36,    21,   142,    29,    -1,    35,
      21,   158,    29,    -1,    37,    21,   182,    29,    -1,    17,
      28,    -1,    17,   209,    28,    -1,   205,    -1,   205,    10,
     209,    -1,   211,    -1,    58,    -1,    60,    -1,    68,    -1,
      56,    -1,    55,    -1,    58,    -1,    63,    -1,    64,    -1,
      68,    -1,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   225,   225,   226,   229,   230,   233,   234,   235,   236,
     239,   242,   245,   248,   251,   252,   255,   258,   259,   262,
     263,   264,   265,   268,   269,   270,   273,   276,   277,   278,
     281,   282,   285,   286,   289,   290,   293,   294,   295,   296,
     297,   298,   299,   302,   305,   306,   309,   310,   313,   316,
     319,   322,   323,   324,   327,   330,   333,   336,   337,   338,
     341,   342,   345,   346,   349,   350,   353,   354,   357,   358,
     361,   362,   365,   368,   369,   372,   373,   376,   379,   380,
     383,   384,   385,   388,   389,   392,   393,   396,   399,   400,
     403,   404,   407,   408,   411,   412,   413,   414,   415,   416,
     417,   420,   423,   424,   427,   428,   431,   434,   435,   438,
     439,   442,   443,   446,   447,   450,   451,   454,   455,   458,
     459,   462,   463,   464,   467,   470,   471,   474,   475,   476,
     479,   482,   483,   486,   487,   490,   491,   494,   495,   498,
     501,   502,   505,   506,   509,   510,   513,   514,   515,   516,
     517,   518,   519,   522,   525,   526,   529,   530,   533,   536,
     537,   540,   541,   542,   545,   548,   549,   552,   553,   556,
     557,   560,   561,   562,   565,   566,   567,   570,   573,   574,
     575,   576,   577,   578,   581,   582,   583,   586,   587,   588,
     591,   594,   595,   598,   599,   600,   601,   602,   603,   606,
     607,   610,   613,   616,   619,   620,   621,   624,   627,   628,
     631,   634,   637,   640,   643,   646,   649,   650,   651,   654,
     655,   656,   659,   660,   663,   666,   669,   670,   673,   674,
     677,   680,   681,   684,   687,   690,   691,   694,   697,   700,
     703,   704,   707,   708,   711,   714,   715,   718,   721,   724,
     725,   728,   729,   732,   733,   734,   737,   738,   739,   740,
     741,   742,   745,   746,   747,   748,   749,   752,   753,   756,
     757,   760,   761,   764,   765,   768,   771,   774,   775,   776,
     779,   782
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "AMPERSAND", "AT_SIGN", "AT_SIGN_MINUS",
  "AT_SIGN_PLUS", "CARET", "COLON", "COLON_EQUALS", "COMMA", "EQUALS",
  "EQUALS_GREATER", "EXCLAMATION", "EXCLAMATION_EQUALS",
  "EXCLAMATION_EXCLAMATION", "EXCLAMATION_GREATER", "LBRKT", "LESS_EQUALS",
  "LESS_EQUALS_GREATER", "LESS_TILDE_GREATER", "LPAREN", "MINUS",
  "MINUS_MINUS_GREATER", "PERIOD", "QUESTION", "QUESTION_QUESTION",
  "QUESTION_STAR", "RBRKT", "RPAREN", "STAR", "TILDE", "TILDE_AMPERSAND",
  "TILDE_VLINE", "VLINE", "_DLR_cnf", "_DLR_fof", "_DLR_fot", "_DLR_itef",
  "_DLR_itetf", "_DLR_itett", "_DLR_tff", "_DLR_thf", "_LIT_cnf",
  "_LIT_fof", "_LIT_include", "_LIT_tff", "_LIT_thf", "arrow", "comment",
  "comment_line", "decimal", "decimal_exponent", "decimal_fraction",
  "distinct_object", "dollar_dollar_word", "dollar_word", "dot_decimal",
  "integer", "less_sign", "lower_word", "plus", "positive_decimal",
  "rational", "real", "signed_integer", "signed_rational", "signed_real",
  "single_quoted", "star", "unrecognized", "unsigned_integer",
  "unsigned_rational", "unsigned_real", "upper_word", "vline", "$accept",
  "TPTP_file", "TPTP_input", "annotated_formula", "thf_annotated",
  "tff_annotated", "fof_annotated", "cnf_annotated", "annotations",
  "formula_role", "thf_formula", "thf_logic_formula", "thf_binary_formula",
  "thf_binary_pair", "thf_binary_tuple", "thf_or_formula",
  "thf_and_formula", "thf_apply_formula", "thf_unitary_formula",
  "thf_quantified_formula", "thf_variable_list", "thf_variable",
  "thf_typed_variable", "thf_unary_formula", "thf_type_formula",
  "thf_typeable_formula", "thf_subtype", "thf_top_level_type",
  "thf_unitary_type", "thf_binary_type", "thf_mapping_type",
  "thf_xprod_type", "thf_union_type", "thf_atom", "thf_tuple",
  "thf_tuple_list", "thf_let", "thf_let_list", "thf_defined_var",
  "thf_conditional", "thf_sequent", "tff_formula", "tff_logic_formula",
  "tff_binary_formula", "tff_binary_nonassoc", "tff_binary_assoc",
  "tff_or_formula", "tff_and_formula", "tff_unitary_formula",
  "tff_quantified_formula", "tff_variable_list", "tff_variable",
  "tff_typed_variable", "tff_unary_formula", "tff_typed_atom",
  "tff_untyped_atom", "tff_top_level_type", "tff_unitary_type",
  "tff_atomic_type", "tff_mapping_type", "tff_xprod_type", "tff_let",
  "tff_let_list", "tff_defined_var", "tff_conditional", "tff_sequent",
  "fof_formula", "fof_logic_formula", "fof_binary_formula",
  "fof_binary_nonassoc", "fof_binary_assoc", "fof_or_formula",
  "fof_and_formula", "fof_unitary_formula", "fof_quantified_formula",
  "fof_variable_list", "fof_unary_formula", "fof_let", "fof_let_list",
  "fof_defined_var", "fof_conditional", "fof_sequent", "cnf_formula",
  "disjunction", "literal", "thf_conn_term", "fol_infix_unary",
  "thf_quantifier", "thf_pair_connective", "thf_unary_connective",
  "subtype_sign", "fol_quantifier", "binary_connective",
  "assoc_connective", "unary_connective", "gentzen_arrow", "defined_type",
  "atomic_formula", "plain_atomic_formula", "defined_atomic_formula",
  "defined_plain_formula", "defined_infix_formula", "defined_infix_pred",
  "infix_equality", "infix_inequality", "system_atomic_formula", "term",
  "function_term", "plain_term", "constant", "functor", "defined_term",
  "defined_atom", "defined_atomic_term", "defined_plain_term",
  "defined_constant", "defined_functor", "system_term", "system_constant",
  "system_functor", "variable", "arguments", "conditional_term", "source",
  "optional_info", "useful_info", "include", "formula_selection",
  "name_list", "general_term", "general_data", "formula_data",
  "general_list", "general_terms", "name", "atomic_word",
  "atomic_defined_word", "atomic_system_word", "number", "file_name",
  "null", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    76,    77,    77,    78,    78,    79,    79,    79,    79,
      80,    81,    82,    83,    84,    84,    85,    86,    86,    87,
      87,    87,    87,    88,    88,    88,    89,    90,    90,    90,
      91,    91,    92,    92,    93,    93,    94,    94,    94,    94,
      94,    94,    94,    95,    96,    96,    97,    97,    98,    99,
     100,   101,   101,   101,   102,   103,   104,   105,   105,   105,
     106,   106,   107,   107,   108,   108,   109,   109,   110,   110,
     111,   111,   112,   113,   113,   114,   114,   115,   116,   116,
     117,   117,   117,   118,   118,   119,   119,   120,   121,   121,
     122,   122,   123,   123,   124,   124,   124,   124,   124,   124,
     124,   125,   126,   126,   127,   127,   128,   129,   129,   130,
     130,   131,   131,   132,   132,   133,   133,   134,   134,   135,
     135,   136,   136,   136,   137,   138,   138,   139,   139,   139,
     140,   141,   141,   142,   142,   143,   143,   144,   144,   145,
     146,   146,   147,   147,   148,   148,   149,   149,   149,   149,
     149,   149,   149,   150,   151,   151,   152,   152,   153,   154,
     154,   155,   155,   155,   156,   157,   157,   158,   158,   159,
     159,   160,   160,   160,   161,   161,   161,   162,   163,   163,
     163,   163,   163,   163,   164,   164,   164,   165,   165,   165,
     166,   167,   167,   168,   168,   168,   168,   168,   168,   169,
     169,   170,   171,   172,   173,   173,   173,   174,   175,   175,
     176,   177,   178,   179,   180,   181,   182,   182,   182,   183,
     183,   183,   184,   184,   185,   186,   187,   187,   188,   188,
     189,   190,   190,   191,   192,   193,   193,   194,   195,   196,
     197,   197,   198,   198,   199,   200,   200,   201,   202,   203,
     203,   204,   204,   205,   205,   205,   206,   206,   206,   206,
     206,   206,   207,   207,   207,   207,   207,   208,   208,   209,
     209,   210,   210,   211,   211,   212,   213,   214,   214,   214,
     215,   216
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     1,     1,     1,     1,     1,     1,
      10,    10,    10,    10,     3,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     3,     1,     1,     1,
       3,     3,     3,     3,     3,     3,     1,     1,     1,     1,
       1,     1,     3,     6,     1,     3,     1,     1,     3,     4,
       3,     1,     1,     3,     3,     1,     1,     1,     1,     1,
       3,     3,     3,     3,     3,     3,     1,     1,     2,     3,
       1,     3,     6,     1,     3,     3,     3,     8,     3,     3,
       1,     1,     1,     1,     1,     1,     1,     3,     1,     1,
       3,     3,     3,     3,     1,     1,     1,     1,     1,     1,
       3,     6,     1,     3,     1,     1,     3,     2,     1,     3,
       3,     1,     1,     1,     1,     1,     3,     1,     1,     3,
       3,     3,     3,     3,     6,     1,     3,     3,     4,     3,
       8,     3,     3,     1,     1,     1,     1,     1,     1,     3,
       1,     1,     3,     3,     3,     3,     1,     1,     1,     1,
       1,     1,     3,     6,     1,     3,     2,     1,     6,     1,
       3,     3,     4,     3,     8,     3,     3,     3,     1,     1,
       3,     1,     2,     1,     1,     1,     1,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     3,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     4,     1,     1,     1,     1,     1,     1,
       1,     1,     4,     1,     1,     1,     4,     1,     1,     1,
       1,     3,     8,     8,     1,     2,     1,     1,     6,     4,
       1,     1,     3,     1,     3,     1,     1,     4,     1,     1,
       1,     1,     4,     4,     4,     4,     4,     2,     3,     1,
       3,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     0
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
     281,     0,     2,     1,     0,     0,     0,     0,     0,     3,
       4,     6,     7,     8,     9,     5,     0,     0,     0,     0,
       0,   272,   273,   274,     0,   271,     0,   280,   281,     0,
       0,     0,     0,     0,     0,   250,     0,     0,    16,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   251,   248,
       0,     0,     0,     0,     0,     0,   229,   276,   275,   277,
     278,   279,   239,   281,   168,   169,   173,   171,   204,   205,
     208,   209,   206,     0,   216,   207,   222,   224,   220,   226,
     227,   210,   231,   233,   215,   235,   237,   217,   218,   225,
     234,   238,   228,     0,   191,     0,   192,   201,     0,   281,
     133,   135,   137,   138,   140,   141,   136,   146,   147,   149,
     151,   134,   157,     0,     0,   148,   150,   249,     0,     0,
       0,     0,   281,    80,    83,    85,    86,    88,    89,    84,
      94,    95,    81,     0,    97,    99,    82,   108,     0,     0,
      96,   224,   237,    98,   200,   183,   182,   179,     0,   213,
     194,   214,   188,   180,     0,   195,   193,   196,     0,   189,
     181,   198,   197,   199,     0,   281,    17,    19,    23,    24,
      27,    28,    29,    20,    36,    37,    21,     0,    22,     0,
      25,    57,    58,    59,    38,    39,    40,    41,    18,    67,
       0,   174,   176,   178,   186,   175,   187,   184,   185,    66,
     219,   222,   230,   221,     0,   172,     0,     0,     0,     0,
       0,    15,     0,     0,   212,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   202,     0,     0,     0,     0,     0,
       0,     0,     0,   156,   252,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     107,     0,     0,    68,    70,    38,    39,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     167,     0,     0,     0,     0,     0,     0,     0,     0,   260,
     258,   281,   244,   253,   261,   255,   256,   259,     0,   170,
     211,   177,   240,     0,     0,     0,     0,     0,   159,     0,
     152,   166,     0,     0,   165,   143,   145,   144,   142,   139,
       0,   154,     0,     0,     0,   125,     0,   100,   110,   132,
       0,     0,   131,    91,    93,    92,    90,    87,     0,   109,
       0,   113,   114,   118,   117,   203,     0,   102,   104,   105,
       0,     0,     0,    46,     0,    73,    47,     0,     0,    39,
       0,    69,    42,    79,     0,     0,    31,    33,    35,    32,
      34,    30,    26,    55,    50,    56,    62,    60,    61,    64,
      63,    65,    78,     0,    44,     0,   190,    54,   224,     0,
       0,   267,   269,     0,     0,     0,     0,     0,     0,     0,
      14,   246,     0,     0,    13,     0,   223,   232,   236,     0,
       0,     0,     0,     0,     0,    12,     0,     0,     0,     0,
       0,     0,     0,     0,    11,     0,   115,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    42,    71,
       0,    10,     0,     0,    49,     0,     0,     0,   268,     0,
       0,     0,     0,     0,   245,   247,   254,     0,   241,   163,
       0,   160,     0,   161,     0,     0,   155,   129,     0,   126,
       0,   127,     0,     0,     0,   120,   116,     0,   119,     0,
     103,   106,    76,    75,     0,    74,    48,     0,     0,    45,
       0,     0,   270,   265,   264,   266,   263,   262,   257,   158,
     162,     0,   153,   124,   128,     0,   123,   121,   122,   101,
      72,     0,    43,     0,     0,     0,     0,     0,   243,   242,
     164,   130,    77
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     9,    10,    11,    12,    13,    14,   210,    39,
     165,   166,   167,   168,   169,   170,   171,   172,   173,   174,
     383,   352,   353,   175,   176,   177,   178,   374,   179,   180,
     181,   182,   183,   255,   256,   257,   186,   354,   355,   187,
     188,   122,   123,   124,   125,   126,   127,   128,   129,   130,
     346,   347,   348,   131,   132,   133,   339,   340,   426,   427,
     428,   134,   324,   325,   135,   136,    99,   100,   101,   102,
     103,   104,   105,   106,   107,   320,   108,   109,   307,   308,
     110,   111,    63,    64,    65,   189,   112,   190,   191,   192,
     279,   193,   194,   195,   196,   225,   343,   115,    68,    69,
      70,    71,   213,   197,   198,    72,    73,    74,    75,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      87,   303,    88,   291,   400,   454,    15,    34,    47,   392,
     293,   294,   295,   393,    48,    89,    90,    91,    92,    28,
     211
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -388
static const yytype_int16 yypact[] =
{
    -388,   110,  -388,  -388,    12,    14,    26,    41,    46,  -388,
    -388,  -388,  -388,  -388,  -388,  -388,   -12,   -12,    10,   -12,
     -12,  -388,  -388,  -388,    72,  -388,    74,  -388,    84,    89,
      91,    52,    52,   104,   101,  -388,    52,    52,  -388,   132,
     141,   -12,   145,   155,   164,   750,    32,   148,   174,  -388,
     790,  1403,   594,   471,   177,   179,  -388,  -388,  -388,  -388,
    -388,  -388,  -388,   201,   178,  -388,  -388,  -388,  -388,  -388,
    -388,  -388,  -388,    50,  -388,   111,  -388,   192,  -388,  -388,
    -388,   127,  -388,   193,   152,  -388,   195,  -388,  -388,  -388,
    -388,  -388,  -388,   216,  -388,    32,  -388,  -388,   214,   201,
     217,  -388,  -388,  -388,   205,   238,   298,  -388,  -388,  -388,
    -388,  -388,  -388,   227,  1158,  -388,   153,  -388,   -12,   228,
     790,   226,   201,   217,  -388,  -388,  -388,   231,   259,   316,
    -388,  -388,  -388,   258,  -388,  -388,  -388,  -388,   251,  1241,
    -388,    19,    22,   153,  -388,  -388,  -388,  -388,   254,  -388,
    -388,  -388,  -388,  -388,  1339,  -388,  -388,  -388,  1403,  -388,
    -388,  -388,  -388,  -388,   252,   201,  -388,  -388,  -388,  -388,
     240,   269,   272,   566,  -388,  -388,  -388,   270,  -388,    -6,
    -388,  -388,   250,   220,   275,    21,  -388,  -388,  -388,  -388,
     267,  -388,   268,  -388,  -388,  -388,  -388,  -388,  -388,  -388,
    -388,   234,  -388,  -388,     2,  -388,   279,  1158,  1241,  1058,
     266,  -388,   594,   471,  -388,   471,   471,   471,   471,    -1,
       3,   271,  1158,   274,  -388,  1158,  1158,  1158,  1158,  1158,
    1158,   222,  1158,  -388,  -388,     0,    36,   276,   282,  1241,
     284,  1241,  1241,  1241,  1241,  1241,  1241,    29,   222,  1241,
    -388,     1,  1467,  -388,   287,  -388,  -388,   295,   285,   296,
    1467,   297,  1531,  1531,  1531,  1531,  1531,  1531,  1531,  1467,
    1531,  1531,  1531,  1531,  1531,   281,   222,  1467,   245,    23,
    -388,   289,   314,  1538,   306,   308,   312,   317,   318,  -388,
    -388,   330,  -388,   334,  -388,  -388,   326,  -388,   331,  -388,
    -388,  -388,   346,   329,   332,   335,    -1,   337,   349,   183,
    -388,  -388,   353,   342,  -388,  -388,  -388,  -388,  -388,  -388,
     339,   358,   340,     0,   343,   360,   186,  -388,  -388,  -388,
     362,   354,  -388,  -388,  -388,  -388,  -388,  -388,    77,  -388,
     333,   345,  -388,  -388,  -388,  -388,   355,   369,  -388,   380,
     365,     1,   387,  -388,   370,   390,   389,  1467,   372,   396,
    1531,  -388,   397,  -388,   400,   382,  -388,  -388,  -388,  -388,
    -388,  -388,  -388,  -388,  -388,  -388,  -388,   359,  -388,  -388,
    -388,  -388,  -388,   383,   402,   385,  -388,  -388,  -388,   471,
     471,  -388,   408,   391,   750,    32,   471,   790,  1403,   404,
    -388,  -388,  1058,  1058,  -388,   471,  -388,  -388,  -388,   393,
     416,    -1,   405,  1158,  1158,  -388,   420,   222,   401,   421,
       0,   411,  1241,  1241,  -388,    77,   412,   409,   167,    -2,
     433,   222,    -2,   418,  1467,   441,     1,  1467,  -388,  -388,
    1467,  -388,   442,   222,  -388,   443,   445,  1058,  -388,   423,
     430,   431,   434,   435,  -388,  -388,  -388,   436,  -388,  -388,
    1158,  -388,   471,  -388,   452,  1158,  -388,  -388,  1241,  -388,
     471,  -388,   457,   180,    -2,  -388,  -388,    -2,  -388,  1241,
    -388,  -388,  -388,  -388,  1531,  -388,  -388,   458,  1531,  -388,
     471,   471,  -388,  -388,  -388,  -388,  -388,  -388,  -388,  -388,
    -388,  1158,  -388,  -388,  -388,  1241,   424,  -388,  -388,  -388,
    -388,  1467,  -388,   440,   444,   446,   449,   451,  -388,  -388,
    -388,  -388,  -388
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -388,  -388,  -388,  -388,  -388,  -388,  -388,  -388,   -84,    99,
      96,  -149,  -388,  -388,  -388,  -388,  -388,  -388,   -85,  -388,
      55,  -253,  -388,  -388,  -388,  -388,  -388,    58,  -112,  -388,
     235,  -388,  -388,   465,    17,   154,  -388,    76,   162,  -388,
     357,   120,  -115,  -388,  -388,  -388,  -388,  -388,  -127,  -388,
      87,  -388,  -388,  -388,   399,  -388,  -388,  -388,  -168,   273,
      97,  -388,   103,   198,  -388,   410,   129,   -93,  -388,  -388,
    -388,  -388,  -388,   -80,  -388,   115,  -388,  -388,   122,   230,
    -388,   447,   143,   488,   350,  -388,   516,  -388,   368,  -388,
    -388,   781,   -78,  -388,   842,  -109,  -388,   455,  -388,  -388,
    -388,  -388,  -388,   -54,   470,  -388,   -45,  -388,   -14,   351,
     -43,  -388,  -388,  -388,   219,  -388,  -388,   286,  -388,   -40,
     722,  -200,  -388,  -388,  -388,  -388,  -388,  -388,   426,  -196,
    -388,  -388,   165,  -387,    88,   -16,  -195,  -388,  -160,  -388,
      11
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -231
static const yytype_int16 yytable[] =
{
      25,    25,   220,    25,    25,   236,   199,   141,   206,   258,
     142,     2,   250,   292,   241,   223,   457,   304,   305,   214,
     306,   323,   351,   384,   270,    25,   224,  -111,   230,   -52,
    -112,   280,   310,    16,   233,    17,   212,   200,   240,    35,
     216,    93,   271,   218,   224,    94,    21,    18,    22,   297,
     338,   246,   345,    95,    58,   272,    23,    96,    22,   224,
     492,   149,    19,    97,   151,   327,    23,    20,   185,   254,
      98,    54,    55,    62,    62,    62,   275,   141,    27,   341,
     142,   261,    31,    22,    32,    58,    56,    57,    58,    22,
      59,    23,    22,   282,    33,    60,    61,    23,   425,    36,
      23,    37,    25,   358,    24,    26,    62,    29,    30,   199,
       3,   364,    38,   199,   281,   333,   334,   335,   336,   337,
     373,    41,  -219,   297,   330,  -219,   332,   241,   385,   312,
      42,    40,   314,    58,   350,    43,    44,    22,  -230,   322,
     200,  -230,    45,   345,   200,    23,   315,   316,   317,   318,
     319,    46,   214,     4,     5,     6,     7,     8,   376,   377,
     379,   380,   381,  -221,  -217,    50,  -221,  -217,   300,    49,
     301,   302,   302,   302,    51,   185,   117,   366,   367,   368,
     369,   370,   371,   372,   118,   375,   375,   375,   375,   375,
     384,   412,   413,   296,   421,   422,   476,   477,   207,   200,
     208,   200,   200,   200,   200,   458,   456,   199,   258,   506,
     477,   209,   212,   216,   217,   199,   218,   199,   199,   199,
     199,   199,   199,   199,   199,   199,   199,   199,   199,   199,
     345,   344,   199,   219,   345,   222,   388,   345,   200,   226,
     224,   227,   297,   297,   231,   235,   200,   239,   200,   200,
     200,   200,   200,   200,   200,   200,   200,   200,   200,   200,
     200,   478,   243,   200,   481,   242,   247,   296,   248,   359,
     202,   251,   263,   260,   262,   254,   264,   359,   269,   345,
     273,   274,   345,   -51,   276,   483,   359,   297,   373,   277,
     149,   487,   382,   278,   359,   298,    62,   360,   154,   389,
     311,   228,   401,   313,   386,   328,   507,   471,   472,   508,
     150,   329,   199,   331,   362,   199,   155,   156,   157,   244,
     463,   464,   344,   361,   390,   363,   365,   394,   150,   395,
     161,   162,   229,   396,   155,   156,   157,   203,   397,   398,
     399,   503,   402,   200,   445,   446,   200,   403,   161,   162,
     245,   451,   509,   199,   141,   404,   405,   142,   406,   411,
     302,   407,   517,   414,   408,   410,   415,   416,   417,   310,
     420,   419,   423,   202,   359,   200,   200,   202,   424,   431,
     499,   429,   200,   430,   200,   502,   296,   296,   432,   199,
     516,   200,   199,  -115,   327,   199,   434,   437,   435,   510,
     436,   438,   201,   512,   -52,   -53,   441,   271,   515,   344,
     440,   442,   443,   344,   444,   185,   344,   500,   447,   448,
     200,   283,   459,   200,   460,   504,   200,   462,   465,   468,
     467,   296,   202,   470,   202,   202,   202,   202,   475,   199,
     203,   479,   474,   199,   203,   513,   514,   482,   200,   484,
     488,   359,   493,   490,   359,   491,   200,   359,   344,   494,
     495,   344,   501,   496,   497,   498,   199,   505,   511,   518,
     200,   202,  -116,   519,   200,   520,   200,   200,   521,   202,
     522,   202,   202,   202,   202,   202,   202,   202,   202,   202,
     202,   202,   202,   202,   453,   486,   202,   200,   489,   203,
      67,   203,   203,   203,   203,   140,   378,    67,   205,   201,
      54,    55,   485,   433,   439,   259,   184,   452,   480,   237,
     342,   418,   473,   469,   450,    56,    57,    58,   359,    59,
     238,    22,   466,   461,    60,    61,   409,   449,   203,    23,
     204,   268,   221,   215,   234,    62,   203,     0,   203,   203,
     203,   203,   203,   203,   203,   203,   203,   203,   203,   203,
     203,    66,   299,   203,   455,     0,   137,     0,    66,   265,
     266,     0,     0,     0,     0,   140,   202,   149,   150,   202,
     151,     0,     0,     0,   155,   156,   157,     0,     0,     0,
       0,     0,     0,     0,   140,     0,   -56,     0,   161,   162,
     267,     0,     0,   201,     0,     0,     0,     0,   202,   202,
       0,   201,     0,     0,   -56,   202,     0,   202,     0,     0,
     201,     0,     0,   184,   202,    53,     0,   -56,   201,     0,
     387,     0,     0,    54,    55,     0,   137,     0,     0,     0,
       0,     0,     0,   203,     0,     0,   203,     0,    56,    57,
      58,     0,    59,   202,    22,   137,   202,    60,    61,   202,
       0,     0,    23,   140,     0,     0,     0,    67,    62,     0,
       0,     0,     0,     0,     0,   203,   203,     0,     0,     0,
       0,   202,   203,     0,   203,     0,     0,     0,     0,   202,
       0,   203,     0,     0,   140,     0,   140,   140,   140,   140,
     140,   140,     0,   202,   140,     0,     0,   202,   201,   202,
     202,     0,     0,     0,     0,     0,     0,   184,     0,     0,
     203,     0,     0,   203,   137,   184,   203,     0,    66,     0,
     202,     0,     0,     0,   184,     0,     0,     0,     0,     0,
       0,     0,   184,     0,     0,     0,     0,     0,   203,   201,
       0,     0,     0,     0,     0,   137,   203,   137,   137,   137,
     137,   137,   137,     0,     0,   137,     0,     0,   116,     0,
     203,    52,   143,     0,   203,     0,   203,   203,     0,     0,
       0,    53,     0,     0,     0,   201,     0,     0,   201,    54,
      55,   201,     0,     0,     0,     0,     0,   203,     0,   119,
       0,     0,     0,    94,    56,    57,    58,     0,    59,     0,
      22,   120,     0,    60,    61,    96,     0,   116,    23,     0,
       0,    97,   184,     0,    62,     0,     0,   113,   121,    54,
      55,   138,     0,     0,     0,     0,   116,     0,     0,     0,
       0,     0,   143,     0,    56,    57,    58,     0,    59,    67,
      22,     0,   140,    60,    61,     0,     0,     0,    23,     0,
       0,   143,   201,   184,    62,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   113,   140,   140,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   114,     0,
       0,     0,   139,     0,     0,   113,     0,     0,     0,   184,
       0,   138,   184,     0,     0,   184,     0,     0,     0,     0,
      66,     0,     0,   137,     0,     0,     0,     0,     0,     0,
     138,     0,     0,   140,     0,     0,     0,     0,     0,   116,
     143,   290,     0,     0,   140,     0,     0,   114,   137,   137,
       0,   309,     0,     0,   116,     0,     0,   116,   116,   116,
     116,   116,   116,   321,   116,     0,   114,   326,     0,     0,
     140,   143,   139,   143,   143,   143,   143,   143,   143,     0,
     349,   143,     0,   356,     0,     0,   184,     0,     0,     0,
       0,   139,     0,     0,   137,     0,     0,     0,   113,   138,
       0,     0,     0,     0,     0,   137,     0,     0,   356,     0,
       0,     0,     0,   113,     0,   290,   113,   113,   113,   113,
     113,   113,     0,   113,     0,     0,     0,     0,     0,     0,
     138,   137,   138,   138,   138,   138,   138,   138,   309,     0,
     138,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   326,     0,     0,     0,   114,
     139,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   114,     0,     0,   114,   114,   114,
     114,   114,   114,   356,   114,   283,     0,     0,     0,     0,
       0,   139,     0,   139,   139,   139,   139,   139,   139,     0,
       0,   139,     0,   284,   285,   286,     0,     0,     0,   287,
     288,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   289,     0,     0,     0,    59,   116,    22,   143,
       0,    60,    61,     0,   290,   290,    23,     0,     0,     0,
       0,     0,    62,   309,     0,   116,   116,     0,     0,   321,
       0,     0,   326,     0,   143,   143,     0,     0,     0,     0,
       0,     0,     0,   349,     0,     0,     0,     0,   356,     0,
       0,     0,     0,     0,     0,   356,     0,    93,     0,   290,
       0,    94,     0,     0,     0,     0,   113,     0,   138,   232,
       0,     0,   116,    96,     0,     0,     0,   116,     0,    97,
     143,     0,     0,     0,   113,   113,    98,    54,    55,     0,
       0,   143,     0,   138,   138,     0,     0,     0,     0,     0,
       0,     0,    56,    57,    58,     0,    59,     0,    22,     0,
       0,    60,    61,   116,     0,     0,    23,   143,     0,     0,
       0,     0,    62,     0,     0,     0,     0,   114,     0,   139,
       0,   113,     0,     0,     0,     0,   113,     0,     0,   138,
     119,     0,     0,     0,    94,   114,   114,     0,     0,     0,
     138,     0,   249,     0,   139,   139,    96,     0,     0,     0,
       0,     0,    97,     0,     0,     0,     0,     0,     0,   121,
      54,    55,   113,     0,     0,     0,   138,     0,     0,     0,
       0,     0,     0,     0,     0,    56,    57,    58,     0,    59,
       0,    22,   114,     0,    60,    61,     0,   114,     0,    23,
     139,     0,     0,     0,     0,    62,     0,     0,     0,     0,
       0,   139,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   144,   114,   145,   146,   147,   139,   148,     0,
     149,   150,    94,   151,   152,   153,   154,   155,   156,   157,
     252,     0,     0,     0,    96,   159,   160,   253,     0,     0,
      97,   161,   162,   163,     0,     0,     0,   164,    54,    55,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    56,    57,    58,     0,    59,     0,    22,
       0,     0,    60,    61,     0,     0,   144,    23,   145,   146,
     147,     0,   148,    62,   149,   150,    94,   151,   152,   153,
     154,   155,   156,   157,   158,     0,     0,     0,    96,   159,
     160,     0,     0,     0,    97,   161,   162,   163,     0,     0,
       0,   164,    54,    55,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    56,    57,    58,
       0,    59,     0,    22,     0,     0,    60,    61,     0,     0,
     144,    23,   145,   146,   147,     0,   148,    62,   149,   150,
      94,   151,   152,   153,   154,   155,   156,   157,   357,     0,
       0,     0,    96,   159,   160,     0,     0,     0,    97,   161,
     162,   163,     0,     0,     0,   164,    54,    55,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    56,    57,    58,     0,    59,     0,    22,     0,     0,
      60,    61,     0,     0,   144,    23,   145,   146,   147,     0,
     148,    62,   149,   150,    94,   151,   152,   153,   154,   155,
     156,   157,   252,     0,     0,   283,    96,   159,   160,     0,
       0,     0,    97,   161,   162,   163,   391,     0,     0,   164,
      54,    55,     0,   284,   285,   286,     0,     0,     0,   287,
     288,     0,     0,     0,     0,    56,    57,    58,     0,    59,
       0,    22,   289,     0,    60,    61,    59,     0,    22,    23,
       0,    60,    61,     0,     0,    62,    23,     0,     0,     0,
       0,     0,    62
};

static const yytype_int16 yycheck[] =
{
      16,    17,    95,    19,    20,   120,    51,    50,    53,   158,
      50,     0,   139,   209,   123,    99,   403,   217,   218,    73,
      21,    21,    21,   276,    30,    41,    23,     8,   106,     8,
       8,    29,    29,    21,   114,    21,    34,    51,   122,    28,
      21,     9,    48,    21,    23,    13,    58,    21,    60,   209,
      21,   129,   247,    21,    56,    61,    68,    25,    60,    23,
     447,    11,    21,    31,    14,    29,    68,    21,    51,   154,
      38,    39,    40,    74,    74,    74,   185,   120,    68,   247,
     120,   165,    10,    60,    10,    56,    54,    55,    56,    60,
      58,    68,    60,   208,    10,    63,    64,    68,    21,    10,
      68,    10,   118,   252,    16,    17,    74,    19,    20,   154,
       0,   260,    60,   158,   207,   242,   243,   244,   245,   246,
     269,    17,    11,   283,   239,    14,   241,   236,   277,   222,
      29,    32,   225,    56,   249,    36,    37,    60,    11,   232,
     154,    14,    10,   338,   158,    68,   226,   227,   228,   229,
     230,    10,   206,    43,    44,    45,    46,    47,   270,   271,
     272,   273,   274,    11,    11,    10,    14,    14,   213,    24,
     215,   216,   217,   218,    10,   158,    28,   262,   263,   264,
     265,   266,   267,   268,    10,   270,   271,   272,   273,   274,
     443,     8,     9,   209,     8,     9,    29,    30,    21,   213,
      21,   215,   216,   217,   218,   405,   402,   252,   357,    29,
      30,    10,    34,    21,    21,   260,    21,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     425,   247,   277,    17,   429,    21,   279,   432,   252,    34,
      23,     3,   402,   403,    17,    17,   260,    21,   262,   263,
     264,   265,   266,   267,   268,   269,   270,   271,   272,   273,
     274,   429,     3,   277,   432,    34,     8,   283,    17,   252,
      51,    17,     3,    21,    34,   360,     4,   260,     8,   474,
      30,    61,   477,     8,    17,   434,   269,   447,   437,    21,
      11,   440,   275,    59,   277,    29,    74,    10,    17,    10,
      29,     3,   291,    29,    59,    29,   474,   422,   423,   477,
      12,    29,   357,    29,    29,   360,    18,    19,    20,     3,
     413,   414,   338,    28,    10,    29,    29,    21,    12,    21,
      32,    33,    34,    21,    18,    19,    20,    51,    21,    21,
      10,   468,     8,   357,   389,   390,   360,    21,    32,    33,
      34,   396,   479,   398,   397,    24,    10,   397,    29,    10,
     405,    29,   511,    10,    29,    28,    24,    28,    10,    29,
      10,    28,    10,   154,   357,   389,   390,   158,    24,    10,
     460,    48,   396,    28,   398,   465,   402,   403,     8,   434,
     505,   405,   437,    48,    29,   440,     9,     8,    28,   484,
      10,    29,    51,   488,     8,     8,    24,    48,   501,   425,
      10,    28,    10,   429,    29,   398,   432,   462,    10,    28,
     434,    17,    29,   437,     8,   470,   440,    22,     8,     8,
      29,   447,   213,    22,   215,   216,   217,   218,    29,   484,
     154,     8,    30,   488,   158,   490,   491,    29,   462,     8,
       8,   434,    29,    10,   437,    10,   470,   440,   474,    29,
      29,   477,    10,    29,    29,    29,   511,    10,    10,    29,
     484,   252,    48,    29,   488,    29,   490,   491,    29,   260,
      29,   262,   263,   264,   265,   266,   267,   268,   269,   270,
     271,   272,   273,   274,   398,   437,   277,   511,   443,   213,
      45,   215,   216,   217,   218,    50,   271,    52,    53,   158,
      39,    40,   436,   351,   360,   158,    51,   397,   431,   120,
     247,   323,   425,   420,   395,    54,    55,    56,   511,    58,
     120,    60,   417,   411,    63,    64,   306,   394,   252,    68,
      52,   173,    95,    73,   118,    74,   260,    -1,   262,   263,
     264,   265,   266,   267,   268,   269,   270,   271,   272,   273,
     274,    45,   212,   277,   399,    -1,    50,    -1,    52,     3,
       4,    -1,    -1,    -1,    -1,   120,   357,    11,    12,   360,
      14,    -1,    -1,    -1,    18,    19,    20,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   139,    -1,    30,    -1,    32,    33,
      34,    -1,    -1,   252,    -1,    -1,    -1,    -1,   389,   390,
      -1,   260,    -1,    -1,    48,   396,    -1,   398,    -1,    -1,
     269,    -1,    -1,   158,   405,    31,    -1,    61,   277,    -1,
     279,    -1,    -1,    39,    40,    -1,   120,    -1,    -1,    -1,
      -1,    -1,    -1,   357,    -1,    -1,   360,    -1,    54,    55,
      56,    -1,    58,   434,    60,   139,   437,    63,    64,   440,
      -1,    -1,    68,   208,    -1,    -1,    -1,   212,    74,    -1,
      -1,    -1,    -1,    -1,    -1,   389,   390,    -1,    -1,    -1,
      -1,   462,   396,    -1,   398,    -1,    -1,    -1,    -1,   470,
      -1,   405,    -1,    -1,   239,    -1,   241,   242,   243,   244,
     245,   246,    -1,   484,   249,    -1,    -1,   488,   357,   490,
     491,    -1,    -1,    -1,    -1,    -1,    -1,   252,    -1,    -1,
     434,    -1,    -1,   437,   208,   260,   440,    -1,   212,    -1,
     511,    -1,    -1,    -1,   269,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   277,    -1,    -1,    -1,    -1,    -1,   462,   398,
      -1,    -1,    -1,    -1,    -1,   239,   470,   241,   242,   243,
     244,   245,   246,    -1,    -1,   249,    -1,    -1,    46,    -1,
     484,    21,    50,    -1,   488,    -1,   490,   491,    -1,    -1,
      -1,    31,    -1,    -1,    -1,   434,    -1,    -1,   437,    39,
      40,   440,    -1,    -1,    -1,    -1,    -1,   511,    -1,     9,
      -1,    -1,    -1,    13,    54,    55,    56,    -1,    58,    -1,
      60,    21,    -1,    63,    64,    25,    -1,    95,    68,    -1,
      -1,    31,   357,    -1,    74,    -1,    -1,    46,    38,    39,
      40,    50,    -1,    -1,    -1,    -1,   114,    -1,    -1,    -1,
      -1,    -1,   120,    -1,    54,    55,    56,    -1,    58,   394,
      60,    -1,   397,    63,    64,    -1,    -1,    -1,    68,    -1,
      -1,   139,   511,   398,    74,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    95,   422,   423,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    46,    -1,
      -1,    -1,    50,    -1,    -1,   114,    -1,    -1,    -1,   434,
      -1,   120,   437,    -1,    -1,   440,    -1,    -1,    -1,    -1,
     394,    -1,    -1,   397,    -1,    -1,    -1,    -1,    -1,    -1,
     139,    -1,    -1,   468,    -1,    -1,    -1,    -1,    -1,   207,
     208,   209,    -1,    -1,   479,    -1,    -1,    95,   422,   423,
      -1,   219,    -1,    -1,   222,    -1,    -1,   225,   226,   227,
     228,   229,   230,   231,   232,    -1,   114,   235,    -1,    -1,
     505,   239,   120,   241,   242,   243,   244,   245,   246,    -1,
     248,   249,    -1,   251,    -1,    -1,   511,    -1,    -1,    -1,
      -1,   139,    -1,    -1,   468,    -1,    -1,    -1,   207,   208,
      -1,    -1,    -1,    -1,    -1,   479,    -1,    -1,   276,    -1,
      -1,    -1,    -1,   222,    -1,   283,   225,   226,   227,   228,
     229,   230,    -1,   232,    -1,    -1,    -1,    -1,    -1,    -1,
     239,   505,   241,   242,   243,   244,   245,   246,   306,    -1,
     249,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   323,    -1,    -1,    -1,   207,
     208,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   222,    -1,    -1,   225,   226,   227,
     228,   229,   230,   351,   232,    17,    -1,    -1,    -1,    -1,
      -1,   239,    -1,   241,   242,   243,   244,   245,   246,    -1,
      -1,   249,    -1,    35,    36,    37,    -1,    -1,    -1,    41,
      42,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    54,    -1,    -1,    -1,    58,   395,    60,   397,
      -1,    63,    64,    -1,   402,   403,    68,    -1,    -1,    -1,
      -1,    -1,    74,   411,    -1,   413,   414,    -1,    -1,   417,
      -1,    -1,   420,    -1,   422,   423,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   431,    -1,    -1,    -1,    -1,   436,    -1,
      -1,    -1,    -1,    -1,    -1,   443,    -1,     9,    -1,   447,
      -1,    13,    -1,    -1,    -1,    -1,   395,    -1,   397,    21,
      -1,    -1,   460,    25,    -1,    -1,    -1,   465,    -1,    31,
     468,    -1,    -1,    -1,   413,   414,    38,    39,    40,    -1,
      -1,   479,    -1,   422,   423,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    54,    55,    56,    -1,    58,    -1,    60,    -1,
      -1,    63,    64,   501,    -1,    -1,    68,   505,    -1,    -1,
      -1,    -1,    74,    -1,    -1,    -1,    -1,   395,    -1,   397,
      -1,   460,    -1,    -1,    -1,    -1,   465,    -1,    -1,   468,
       9,    -1,    -1,    -1,    13,   413,   414,    -1,    -1,    -1,
     479,    -1,    21,    -1,   422,   423,    25,    -1,    -1,    -1,
      -1,    -1,    31,    -1,    -1,    -1,    -1,    -1,    -1,    38,
      39,    40,   501,    -1,    -1,    -1,   505,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    54,    55,    56,    -1,    58,
      -1,    60,   460,    -1,    63,    64,    -1,   465,    -1,    68,
     468,    -1,    -1,    -1,    -1,    74,    -1,    -1,    -1,    -1,
      -1,   479,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     3,   501,     5,     6,     7,   505,     9,    -1,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    -1,    -1,    -1,    25,    26,    27,    28,    -1,    -1,
      31,    32,    33,    34,    -1,    -1,    -1,    38,    39,    40,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    54,    55,    56,    -1,    58,    -1,    60,
      -1,    -1,    63,    64,    -1,    -1,     3,    68,     5,     6,
       7,    -1,     9,    74,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    -1,    -1,    -1,    25,    26,
      27,    -1,    -1,    -1,    31,    32,    33,    34,    -1,    -1,
      -1,    38,    39,    40,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    54,    55,    56,
      -1,    58,    -1,    60,    -1,    -1,    63,    64,    -1,    -1,
       3,    68,     5,     6,     7,    -1,     9,    74,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    25,    26,    27,    -1,    -1,    -1,    31,    32,
      33,    34,    -1,    -1,    -1,    38,    39,    40,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    54,    55,    56,    -1,    58,    -1,    60,    -1,    -1,
      63,    64,    -1,    -1,     3,    68,     5,     6,     7,    -1,
       9,    74,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    -1,    -1,    17,    25,    26,    27,    -1,
      -1,    -1,    31,    32,    33,    34,    28,    -1,    -1,    38,
      39,    40,    -1,    35,    36,    37,    -1,    -1,    -1,    41,
      42,    -1,    -1,    -1,    -1,    54,    55,    56,    -1,    58,
      -1,    60,    54,    -1,    63,    64,    58,    -1,    60,    68,
      -1,    63,    64,    -1,    -1,    74,    68,    -1,    -1,    -1,
      -1,    -1,    74
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    77,   216,     0,    43,    44,    45,    46,    47,    78,
      79,    80,    81,    82,    83,   202,    21,    21,    21,    21,
      21,    58,    60,    68,   210,   211,   210,    68,   215,   210,
     210,    10,    10,    10,   203,   216,    10,    10,    60,    85,
      85,    17,    29,    85,    85,    10,    10,   204,   210,    24,
      10,    10,    21,    31,    39,    40,    54,    55,    56,    58,
      63,    64,    74,   158,   159,   160,   162,   173,   174,   175,
     176,   177,   181,   182,   183,   184,   185,   186,   187,   188,
     189,   190,   191,   192,   193,   194,   195,   196,   198,   211,
     212,   213,   214,     9,    13,    21,    25,    31,    38,   142,
     143,   144,   145,   146,   147,   148,   149,   150,   152,   153,
     156,   157,   162,   167,   170,   173,   196,    28,    10,     9,
      21,    38,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   129,   130,   131,   137,   140,   141,   162,   167,   170,
     173,   186,   195,   196,     3,     5,     6,     7,     9,    11,
      12,    14,    15,    16,    17,    18,    19,    20,    21,    26,
      27,    32,    33,    34,    38,    86,    87,    88,    89,    90,
      91,    92,    93,    94,    95,    99,   100,   101,   102,   104,
     105,   106,   107,   108,   109,   110,   112,   115,   116,   161,
     163,   164,   165,   167,   168,   169,   170,   179,   180,   182,
     184,   185,   190,   193,   159,   173,   182,    21,    21,    10,
      84,   216,    34,   178,   179,   180,    21,    21,    21,    17,
     143,   157,    21,    84,    23,   171,    34,     3,     3,    34,
     168,    17,    21,   149,   204,    17,   118,   130,   141,    21,
      84,   171,    34,     3,     3,    34,   168,     8,    17,    21,
     124,    17,    21,    28,    94,   109,   110,   111,    87,   116,
      21,    84,    34,     3,     4,     3,     4,    34,   164,     8,
      30,    48,    61,    30,    61,   171,    17,    21,    59,   166,
      29,   143,   118,    17,    35,    36,    37,    41,    42,    54,
     196,   199,   205,   206,   207,   208,   211,   214,    29,   160,
     182,   182,   182,   197,   197,   197,    21,   154,   155,   196,
      29,    29,   143,    29,   143,   149,   149,   149,   149,   149,
     151,   196,   143,    21,   138,   139,   196,    29,    29,    29,
     118,    29,   118,   124,   124,   124,   124,   124,    21,   132,
     133,   134,   135,   172,   211,   212,   126,   127,   128,   196,
     118,    21,    97,    98,   113,   114,   196,    21,    87,   110,
      10,    28,    29,    29,    87,    29,    94,    94,    94,    94,
      94,    94,    94,    87,   103,    94,   104,   104,   106,   104,
     104,   104,   110,    96,    97,    87,    59,   185,   186,    10,
      10,    28,   205,   209,    21,    21,    21,    21,    21,    10,
     200,   216,     8,    21,    24,    10,    29,    29,    29,   155,
      28,    10,     8,     9,    10,    24,    28,    10,   139,    28,
      10,     8,     9,    10,    24,    21,   134,   135,   136,    48,
      28,    10,     8,   114,     9,    28,    10,     8,    29,   111,
      10,    24,    28,    10,    29,   182,   182,    10,    28,   158,
     142,   182,   117,    86,   201,   208,   205,   209,   197,    29,
       8,   154,    22,   143,   143,     8,   151,    29,     8,   138,
      22,   118,   118,   136,    30,    29,    29,    30,   134,     8,
     126,   134,    29,    87,     8,   113,   103,    87,     8,    96,
      10,    10,   209,    29,    29,    29,    29,    29,    29,   149,
     182,    10,   149,   124,   182,    10,    29,   134,   134,   124,
      94,    10,    94,   182,   182,   143,   118,    87,    29,    29,
      29,    29,    29
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  However,
   YYFAIL appears to be in use.  Nevertheless, it is formally deprecated
   in Bison 2.4.2's NEWS entry, where a plan to phase it out is
   discussed.  */

#define YYFAIL		goto yyerrlab
#if defined YYFAIL
  /* This is here to suppress warnings from the GCC cpp's
     -Wunused-macros.  Normally we don't worry about that warning, but
     some users do, and we want to make it easy for users to remove
     YYFAIL uses, which will produce warnings from Bison 2.5.  */
#endif

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

#if 0
  switch (yytype)
    {

      default:
	break;
    }
#endif
}

/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*-------------------------.
| yyparse or yypush_parse.  |
`-------------------------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{


    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:

/* Line 1464 of yacc.c  */
#line 225 "tptp5.y"
    {;}
    break;

  case 3:

/* Line 1464 of yacc.c  */
#line 226 "tptp5.y"
    {;}
    break;

  case 4:

/* Line 1464 of yacc.c  */
#line 229 "tptp5.y"
    {P_PRINT((yyval.pval));;}
    break;

  case 5:

/* Line 1464 of yacc.c  */
#line 230 "tptp5.y"
    {P_PRINT((yyval.pval));;}
    break;

  case 6:

/* Line 1464 of yacc.c  */
#line 233 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotated_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 7:

/* Line 1464 of yacc.c  */
#line 234 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotated_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 8:

/* Line 1464 of yacc.c  */
#line 235 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotated_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 9:

/* Line 1464 of yacc.c  */
#line 236 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotated_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 10:

/* Line 1464 of yacc.c  */
#line 239 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_annotated", P_TOKEN("_LIT_thf ", (yyvsp[(1) - (10)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (10)].ival)), (yyvsp[(3) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (10)].ival)), (yyvsp[(5) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (10)].ival)), (yyvsp[(7) - (10)].pval), (yyvsp[(8) - (10)].pval), P_TOKEN("RPAREN ", (yyvsp[(9) - (10)].ival)), P_TOKEN("PERIOD ", (yyvsp[(10) - (10)].ival)));;}
    break;

  case 11:

/* Line 1464 of yacc.c  */
#line 242 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_annotated", P_TOKEN("_LIT_tff ", (yyvsp[(1) - (10)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (10)].ival)), (yyvsp[(3) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (10)].ival)), (yyvsp[(5) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (10)].ival)), (yyvsp[(7) - (10)].pval), (yyvsp[(8) - (10)].pval), P_TOKEN("RPAREN ", (yyvsp[(9) - (10)].ival)), P_TOKEN("PERIOD ", (yyvsp[(10) - (10)].ival)));;}
    break;

  case 12:

/* Line 1464 of yacc.c  */
#line 245 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_annotated", P_TOKEN("_LIT_fof ", (yyvsp[(1) - (10)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (10)].ival)), (yyvsp[(3) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (10)].ival)), (yyvsp[(5) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (10)].ival)), (yyvsp[(7) - (10)].pval), (yyvsp[(8) - (10)].pval), P_TOKEN("RPAREN ", (yyvsp[(9) - (10)].ival)), P_TOKEN("PERIOD ", (yyvsp[(10) - (10)].ival)));;}
    break;

  case 13:

/* Line 1464 of yacc.c  */
#line 248 "tptp5.y"
    {(yyval.pval) = P_BUILD("cnf_annotated", P_TOKEN("_LIT_cnf ", (yyvsp[(1) - (10)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (10)].ival)), (yyvsp[(3) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (10)].ival)), (yyvsp[(5) - (10)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (10)].ival)), (yyvsp[(7) - (10)].pval), (yyvsp[(8) - (10)].pval), P_TOKEN("RPAREN ", (yyvsp[(9) - (10)].ival)), P_TOKEN("PERIOD ", (yyvsp[(10) - (10)].ival)));;}
    break;

  case 14:

/* Line 1464 of yacc.c  */
#line 251 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotations", P_TOKEN("COMMA ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 15:

/* Line 1464 of yacc.c  */
#line 252 "tptp5.y"
    {(yyval.pval) = P_BUILD("annotations", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 16:

/* Line 1464 of yacc.c  */
#line 255 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_role", P_TOKEN("lower_word ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 17:

/* Line 1464 of yacc.c  */
#line 258 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 18:

/* Line 1464 of yacc.c  */
#line 259 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 19:

/* Line 1464 of yacc.c  */
#line 262 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 20:

/* Line 1464 of yacc.c  */
#line 263 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 21:

/* Line 1464 of yacc.c  */
#line 264 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 22:

/* Line 1464 of yacc.c  */
#line 265 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 23:

/* Line 1464 of yacc.c  */
#line 268 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 24:

/* Line 1464 of yacc.c  */
#line 269 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 25:

/* Line 1464 of yacc.c  */
#line 270 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 26:

/* Line 1464 of yacc.c  */
#line 273 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_pair", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 27:

/* Line 1464 of yacc.c  */
#line 276 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_tuple", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 28:

/* Line 1464 of yacc.c  */
#line 277 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_tuple", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 29:

/* Line 1464 of yacc.c  */
#line 278 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_tuple", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 30:

/* Line 1464 of yacc.c  */
#line 281 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 31:

/* Line 1464 of yacc.c  */
#line 282 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 32:

/* Line 1464 of yacc.c  */
#line 285 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 33:

/* Line 1464 of yacc.c  */
#line 286 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 34:

/* Line 1464 of yacc.c  */
#line 289 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_apply_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AT_SIGN ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 35:

/* Line 1464 of yacc.c  */
#line 290 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_apply_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AT_SIGN ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 36:

/* Line 1464 of yacc.c  */
#line 293 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 37:

/* Line 1464 of yacc.c  */
#line 294 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 38:

/* Line 1464 of yacc.c  */
#line 295 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 39:

/* Line 1464 of yacc.c  */
#line 296 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 40:

/* Line 1464 of yacc.c  */
#line 297 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 41:

/* Line 1464 of yacc.c  */
#line 298 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 42:

/* Line 1464 of yacc.c  */
#line 299 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_formula", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 43:

/* Line 1464 of yacc.c  */
#line 302 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantified_formula", (yyvsp[(1) - (6)].pval), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 44:

/* Line 1464 of yacc.c  */
#line 305 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_variable_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 45:

/* Line 1464 of yacc.c  */
#line 306 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_variable_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 46:

/* Line 1464 of yacc.c  */
#line 309 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_variable", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 47:

/* Line 1464 of yacc.c  */
#line 310 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_variable", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 48:

/* Line 1464 of yacc.c  */
#line 313 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_typed_variable", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 49:

/* Line 1464 of yacc.c  */
#line 316 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unary_formula", (yyvsp[(1) - (4)].pval), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 50:

/* Line 1464 of yacc.c  */
#line 319 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_type_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 51:

/* Line 1464 of yacc.c  */
#line 322 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_typeable_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 52:

/* Line 1464 of yacc.c  */
#line 323 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_typeable_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 53:

/* Line 1464 of yacc.c  */
#line 324 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_typeable_formula", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 54:

/* Line 1464 of yacc.c  */
#line 327 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_subtype", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 55:

/* Line 1464 of yacc.c  */
#line 330 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_top_level_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 56:

/* Line 1464 of yacc.c  */
#line 333 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unitary_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 57:

/* Line 1464 of yacc.c  */
#line 336 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 58:

/* Line 1464 of yacc.c  */
#line 337 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 59:

/* Line 1464 of yacc.c  */
#line 338 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_binary_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 60:

/* Line 1464 of yacc.c  */
#line 341 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_mapping_type", (yyvsp[(1) - (3)].pval), P_TOKEN("arrow ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 61:

/* Line 1464 of yacc.c  */
#line 342 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_mapping_type", (yyvsp[(1) - (3)].pval), P_TOKEN("arrow ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 62:

/* Line 1464 of yacc.c  */
#line 345 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_xprod_type", (yyvsp[(1) - (3)].pval), P_TOKEN("STAR ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 63:

/* Line 1464 of yacc.c  */
#line 346 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_xprod_type", (yyvsp[(1) - (3)].pval), P_TOKEN("STAR ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 64:

/* Line 1464 of yacc.c  */
#line 349 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_union_type", (yyvsp[(1) - (3)].pval), P_TOKEN("plus ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 65:

/* Line 1464 of yacc.c  */
#line 350 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_union_type", (yyvsp[(1) - (3)].pval), P_TOKEN("plus ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 66:

/* Line 1464 of yacc.c  */
#line 353 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_atom", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 67:

/* Line 1464 of yacc.c  */
#line 354 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_atom", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 68:

/* Line 1464 of yacc.c  */
#line 357 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_tuple", P_TOKEN("LBRKT ", (yyvsp[(1) - (2)].ival)), P_TOKEN("RBRKT ", (yyvsp[(2) - (2)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 69:

/* Line 1464 of yacc.c  */
#line 358 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_tuple", P_TOKEN("LBRKT ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RBRKT ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 70:

/* Line 1464 of yacc.c  */
#line 361 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_tuple_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 71:

/* Line 1464 of yacc.c  */
#line 362 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_tuple_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 72:

/* Line 1464 of yacc.c  */
#line 365 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_let", P_TOKEN("COLON_EQUALS ", (yyvsp[(1) - (6)].ival)), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 73:

/* Line 1464 of yacc.c  */
#line 368 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_let_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 74:

/* Line 1464 of yacc.c  */
#line 369 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_let_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 75:

/* Line 1464 of yacc.c  */
#line 372 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_defined_var", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON_EQUALS ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 76:

/* Line 1464 of yacc.c  */
#line 373 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_defined_var", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 77:

/* Line 1464 of yacc.c  */
#line 376 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_conditional", P_TOKEN("_DLR_itef ", (yyvsp[(1) - (8)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (8)].ival)), (yyvsp[(3) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (8)].ival)), (yyvsp[(5) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (8)].ival)), (yyvsp[(7) - (8)].pval), P_TOKEN("RPAREN ", (yyvsp[(8) - (8)].ival)),NULL,NULL);;}
    break;

  case 78:

/* Line 1464 of yacc.c  */
#line 379 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_sequent", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 79:

/* Line 1464 of yacc.c  */
#line 380 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_sequent", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 80:

/* Line 1464 of yacc.c  */
#line 383 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 81:

/* Line 1464 of yacc.c  */
#line 384 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 82:

/* Line 1464 of yacc.c  */
#line 385 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 83:

/* Line 1464 of yacc.c  */
#line 388 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 84:

/* Line 1464 of yacc.c  */
#line 389 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 85:

/* Line 1464 of yacc.c  */
#line 392 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 86:

/* Line 1464 of yacc.c  */
#line 393 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 87:

/* Line 1464 of yacc.c  */
#line 396 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_binary_nonassoc", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 88:

/* Line 1464 of yacc.c  */
#line 399 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_binary_assoc", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 89:

/* Line 1464 of yacc.c  */
#line 400 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_binary_assoc", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 90:

/* Line 1464 of yacc.c  */
#line 403 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 91:

/* Line 1464 of yacc.c  */
#line 404 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 92:

/* Line 1464 of yacc.c  */
#line 407 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 93:

/* Line 1464 of yacc.c  */
#line 408 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 94:

/* Line 1464 of yacc.c  */
#line 411 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 95:

/* Line 1464 of yacc.c  */
#line 412 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 96:

/* Line 1464 of yacc.c  */
#line 413 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 97:

/* Line 1464 of yacc.c  */
#line 414 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 98:

/* Line 1464 of yacc.c  */
#line 415 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 99:

/* Line 1464 of yacc.c  */
#line 416 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 100:

/* Line 1464 of yacc.c  */
#line 417 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_formula", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 101:

/* Line 1464 of yacc.c  */
#line 420 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_quantified_formula", (yyvsp[(1) - (6)].pval), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 102:

/* Line 1464 of yacc.c  */
#line 423 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_variable_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 103:

/* Line 1464 of yacc.c  */
#line 424 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_variable_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 104:

/* Line 1464 of yacc.c  */
#line 427 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_variable", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 105:

/* Line 1464 of yacc.c  */
#line 428 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_variable", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 106:

/* Line 1464 of yacc.c  */
#line 431 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_typed_variable", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 107:

/* Line 1464 of yacc.c  */
#line 434 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unary_formula", (yyvsp[(1) - (2)].pval), (yyvsp[(2) - (2)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 108:

/* Line 1464 of yacc.c  */
#line 435 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 109:

/* Line 1464 of yacc.c  */
#line 438 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_typed_atom", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 110:

/* Line 1464 of yacc.c  */
#line 439 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_typed_atom", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 111:

/* Line 1464 of yacc.c  */
#line 442 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_untyped_atom", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 112:

/* Line 1464 of yacc.c  */
#line 443 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_untyped_atom", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 113:

/* Line 1464 of yacc.c  */
#line 446 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_top_level_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 114:

/* Line 1464 of yacc.c  */
#line 447 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_top_level_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 115:

/* Line 1464 of yacc.c  */
#line 450 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 116:

/* Line 1464 of yacc.c  */
#line 451 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_unitary_type", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 117:

/* Line 1464 of yacc.c  */
#line 454 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_atomic_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 118:

/* Line 1464 of yacc.c  */
#line 455 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_atomic_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 119:

/* Line 1464 of yacc.c  */
#line 458 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_mapping_type", (yyvsp[(1) - (3)].pval), P_TOKEN("arrow ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 120:

/* Line 1464 of yacc.c  */
#line 459 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_mapping_type", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 121:

/* Line 1464 of yacc.c  */
#line 462 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_xprod_type", (yyvsp[(1) - (3)].pval), P_TOKEN("STAR ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 122:

/* Line 1464 of yacc.c  */
#line 463 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_xprod_type", (yyvsp[(1) - (3)].pval), P_TOKEN("STAR ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 123:

/* Line 1464 of yacc.c  */
#line 464 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_xprod_type", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 124:

/* Line 1464 of yacc.c  */
#line 467 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_let", P_TOKEN("COLON_EQUALS ", (yyvsp[(1) - (6)].ival)), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 125:

/* Line 1464 of yacc.c  */
#line 470 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_let_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 126:

/* Line 1464 of yacc.c  */
#line 471 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_let_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 127:

/* Line 1464 of yacc.c  */
#line 474 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_defined_var", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON_EQUALS ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 128:

/* Line 1464 of yacc.c  */
#line 475 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_defined_var", (yyvsp[(1) - (4)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (4)].ival)), P_TOKEN("MINUS ", (yyvsp[(3) - (4)].ival)), (yyvsp[(4) - (4)].pval),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 129:

/* Line 1464 of yacc.c  */
#line 476 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_defined_var", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 130:

/* Line 1464 of yacc.c  */
#line 479 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_conditional", P_TOKEN("_DLR_itef ", (yyvsp[(1) - (8)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (8)].ival)), (yyvsp[(3) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (8)].ival)), (yyvsp[(5) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (8)].ival)), (yyvsp[(7) - (8)].pval), P_TOKEN("RPAREN ", (yyvsp[(8) - (8)].ival)),NULL,NULL);;}
    break;

  case 131:

/* Line 1464 of yacc.c  */
#line 482 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_sequent", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 132:

/* Line 1464 of yacc.c  */
#line 483 "tptp5.y"
    {(yyval.pval) = P_BUILD("tff_sequent", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 133:

/* Line 1464 of yacc.c  */
#line 486 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 134:

/* Line 1464 of yacc.c  */
#line 487 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 135:

/* Line 1464 of yacc.c  */
#line 490 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 136:

/* Line 1464 of yacc.c  */
#line 491 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_logic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 137:

/* Line 1464 of yacc.c  */
#line 494 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 138:

/* Line 1464 of yacc.c  */
#line 495 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_binary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 139:

/* Line 1464 of yacc.c  */
#line 498 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_binary_nonassoc", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 140:

/* Line 1464 of yacc.c  */
#line 501 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_binary_assoc", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 141:

/* Line 1464 of yacc.c  */
#line 502 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_binary_assoc", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 142:

/* Line 1464 of yacc.c  */
#line 505 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 143:

/* Line 1464 of yacc.c  */
#line 506 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_or_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 144:

/* Line 1464 of yacc.c  */
#line 509 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 145:

/* Line 1464 of yacc.c  */
#line 510 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_and_formula", (yyvsp[(1) - (3)].pval), P_TOKEN("AMPERSAND ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 146:

/* Line 1464 of yacc.c  */
#line 513 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 147:

/* Line 1464 of yacc.c  */
#line 514 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 148:

/* Line 1464 of yacc.c  */
#line 515 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 149:

/* Line 1464 of yacc.c  */
#line 516 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 150:

/* Line 1464 of yacc.c  */
#line 517 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 151:

/* Line 1464 of yacc.c  */
#line 518 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 152:

/* Line 1464 of yacc.c  */
#line 519 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unitary_formula", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 153:

/* Line 1464 of yacc.c  */
#line 522 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_quantified_formula", (yyvsp[(1) - (6)].pval), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 154:

/* Line 1464 of yacc.c  */
#line 525 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_variable_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 155:

/* Line 1464 of yacc.c  */
#line 526 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_variable_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 156:

/* Line 1464 of yacc.c  */
#line 529 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unary_formula", (yyvsp[(1) - (2)].pval), (yyvsp[(2) - (2)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 157:

/* Line 1464 of yacc.c  */
#line 530 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_unary_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 158:

/* Line 1464 of yacc.c  */
#line 533 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_let", P_TOKEN("COLON_EQUALS ", (yyvsp[(1) - (6)].ival)), P_TOKEN("LBRKT ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (6)].ival)), P_TOKEN("COLON ", (yyvsp[(5) - (6)].ival)), (yyvsp[(6) - (6)].pval),NULL,NULL,NULL,NULL);;}
    break;

  case 159:

/* Line 1464 of yacc.c  */
#line 536 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_let_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 160:

/* Line 1464 of yacc.c  */
#line 537 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_let_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 161:

/* Line 1464 of yacc.c  */
#line 540 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_defined_var", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON_EQUALS ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 162:

/* Line 1464 of yacc.c  */
#line 541 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_defined_var", (yyvsp[(1) - (4)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (4)].ival)), P_TOKEN("MINUS ", (yyvsp[(3) - (4)].ival)), (yyvsp[(4) - (4)].pval),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 163:

/* Line 1464 of yacc.c  */
#line 542 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_defined_var", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 164:

/* Line 1464 of yacc.c  */
#line 545 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_conditional", P_TOKEN("_DLR_itef ", (yyvsp[(1) - (8)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (8)].ival)), (yyvsp[(3) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (8)].ival)), (yyvsp[(5) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (8)].ival)), (yyvsp[(7) - (8)].pval), P_TOKEN("RPAREN ", (yyvsp[(8) - (8)].ival)),NULL,NULL);;}
    break;

  case 165:

/* Line 1464 of yacc.c  */
#line 548 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_sequent", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 166:

/* Line 1464 of yacc.c  */
#line 549 "tptp5.y"
    {(yyval.pval) = P_BUILD("fof_sequent", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 167:

/* Line 1464 of yacc.c  */
#line 552 "tptp5.y"
    {(yyval.pval) = P_BUILD("cnf_formula", P_TOKEN("LPAREN ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RPAREN ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 168:

/* Line 1464 of yacc.c  */
#line 553 "tptp5.y"
    {(yyval.pval) = P_BUILD("cnf_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 169:

/* Line 1464 of yacc.c  */
#line 556 "tptp5.y"
    {(yyval.pval) = P_BUILD("disjunction", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 170:

/* Line 1464 of yacc.c  */
#line 557 "tptp5.y"
    {(yyval.pval) = P_BUILD("disjunction", (yyvsp[(1) - (3)].pval), P_TOKEN("VLINE ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 171:

/* Line 1464 of yacc.c  */
#line 560 "tptp5.y"
    {(yyval.pval) = P_BUILD("literal", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 172:

/* Line 1464 of yacc.c  */
#line 561 "tptp5.y"
    {(yyval.pval) = P_BUILD("literal", P_TOKEN("TILDE ", (yyvsp[(1) - (2)].ival)), (yyvsp[(2) - (2)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 173:

/* Line 1464 of yacc.c  */
#line 562 "tptp5.y"
    {(yyval.pval) = P_BUILD("literal", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 174:

/* Line 1464 of yacc.c  */
#line 565 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_conn_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 175:

/* Line 1464 of yacc.c  */
#line 566 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_conn_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 176:

/* Line 1464 of yacc.c  */
#line 567 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_conn_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 177:

/* Line 1464 of yacc.c  */
#line 570 "tptp5.y"
    {(yyval.pval) = P_BUILD("fol_infix_unary", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 178:

/* Line 1464 of yacc.c  */
#line 573 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 179:

/* Line 1464 of yacc.c  */
#line 574 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", P_TOKEN("CARET ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 180:

/* Line 1464 of yacc.c  */
#line 575 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", P_TOKEN("EXCLAMATION_GREATER ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 181:

/* Line 1464 of yacc.c  */
#line 576 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", P_TOKEN("QUESTION_STAR ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 182:

/* Line 1464 of yacc.c  */
#line 577 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", P_TOKEN("AT_SIGN_PLUS ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 183:

/* Line 1464 of yacc.c  */
#line 578 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_quantifier", P_TOKEN("AT_SIGN_MINUS ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 184:

/* Line 1464 of yacc.c  */
#line 581 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_pair_connective", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 185:

/* Line 1464 of yacc.c  */
#line 582 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_pair_connective", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 186:

/* Line 1464 of yacc.c  */
#line 583 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_pair_connective", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 187:

/* Line 1464 of yacc.c  */
#line 586 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unary_connective", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 188:

/* Line 1464 of yacc.c  */
#line 587 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unary_connective", P_TOKEN("EXCLAMATION_EXCLAMATION ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 189:

/* Line 1464 of yacc.c  */
#line 588 "tptp5.y"
    {(yyval.pval) = P_BUILD("thf_unary_connective", P_TOKEN("QUESTION_QUESTION ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 190:

/* Line 1464 of yacc.c  */
#line 591 "tptp5.y"
    {(yyval.pval) = P_BUILD("subtype_sign", P_TOKEN("less_sign ", (yyvsp[(1) - (2)].ival)), P_TOKEN("less_sign ", (yyvsp[(2) - (2)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 191:

/* Line 1464 of yacc.c  */
#line 594 "tptp5.y"
    {(yyval.pval) = P_BUILD("fol_quantifier", P_TOKEN("EXCLAMATION ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 192:

/* Line 1464 of yacc.c  */
#line 595 "tptp5.y"
    {(yyval.pval) = P_BUILD("fol_quantifier", P_TOKEN("QUESTION ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 193:

/* Line 1464 of yacc.c  */
#line 598 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("LESS_EQUALS_GREATER ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 194:

/* Line 1464 of yacc.c  */
#line 599 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("EQUALS_GREATER ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 195:

/* Line 1464 of yacc.c  */
#line 600 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("LESS_EQUALS ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 196:

/* Line 1464 of yacc.c  */
#line 601 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("LESS_TILDE_GREATER ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 197:

/* Line 1464 of yacc.c  */
#line 602 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("TILDE_VLINE ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 198:

/* Line 1464 of yacc.c  */
#line 603 "tptp5.y"
    {(yyval.pval) = P_BUILD("binary_connective", P_TOKEN("TILDE_AMPERSAND ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 199:

/* Line 1464 of yacc.c  */
#line 606 "tptp5.y"
    {(yyval.pval) = P_BUILD("assoc_connective", P_TOKEN("VLINE ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 200:

/* Line 1464 of yacc.c  */
#line 607 "tptp5.y"
    {(yyval.pval) = P_BUILD("assoc_connective", P_TOKEN("AMPERSAND ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 201:

/* Line 1464 of yacc.c  */
#line 610 "tptp5.y"
    {(yyval.pval) = P_BUILD("unary_connective", P_TOKEN("TILDE ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 202:

/* Line 1464 of yacc.c  */
#line 613 "tptp5.y"
    {(yyval.pval) = P_BUILD("gentzen_arrow", P_TOKEN("MINUS_MINUS_GREATER ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 203:

/* Line 1464 of yacc.c  */
#line 616 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_type", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 204:

/* Line 1464 of yacc.c  */
#line 619 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 205:

/* Line 1464 of yacc.c  */
#line 620 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 206:

/* Line 1464 of yacc.c  */
#line 621 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 207:

/* Line 1464 of yacc.c  */
#line 624 "tptp5.y"
    {(yyval.pval) = P_BUILD("plain_atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 208:

/* Line 1464 of yacc.c  */
#line 627 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 209:

/* Line 1464 of yacc.c  */
#line 628 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 210:

/* Line 1464 of yacc.c  */
#line 631 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_plain_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 211:

/* Line 1464 of yacc.c  */
#line 634 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_infix_formula", (yyvsp[(1) - (3)].pval), (yyvsp[(2) - (3)].pval), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 212:

/* Line 1464 of yacc.c  */
#line 637 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_infix_pred", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 213:

/* Line 1464 of yacc.c  */
#line 640 "tptp5.y"
    {(yyval.pval) = P_BUILD("infix_equality", P_TOKEN("EQUALS ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 214:

/* Line 1464 of yacc.c  */
#line 643 "tptp5.y"
    {(yyval.pval) = P_BUILD("infix_inequality", P_TOKEN("EXCLAMATION_EQUALS ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 215:

/* Line 1464 of yacc.c  */
#line 646 "tptp5.y"
    {(yyval.pval) = P_BUILD("system_atomic_formula", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 216:

/* Line 1464 of yacc.c  */
#line 649 "tptp5.y"
    {(yyval.pval) = P_BUILD("term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 217:

/* Line 1464 of yacc.c  */
#line 650 "tptp5.y"
    {(yyval.pval) = P_BUILD("term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 218:

/* Line 1464 of yacc.c  */
#line 651 "tptp5.y"
    {(yyval.pval) = P_BUILD("term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 219:

/* Line 1464 of yacc.c  */
#line 654 "tptp5.y"
    {(yyval.pval) = P_BUILD("function_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 220:

/* Line 1464 of yacc.c  */
#line 655 "tptp5.y"
    {(yyval.pval) = P_BUILD("function_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 221:

/* Line 1464 of yacc.c  */
#line 656 "tptp5.y"
    {(yyval.pval) = P_BUILD("function_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 222:

/* Line 1464 of yacc.c  */
#line 659 "tptp5.y"
    {(yyval.pval) = P_BUILD("plain_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 223:

/* Line 1464 of yacc.c  */
#line 660 "tptp5.y"
    {(yyval.pval) = P_BUILD("plain_term", (yyvsp[(1) - (4)].pval), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 224:

/* Line 1464 of yacc.c  */
#line 663 "tptp5.y"
    {(yyval.pval) = P_BUILD("constant", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 225:

/* Line 1464 of yacc.c  */
#line 666 "tptp5.y"
    {(yyval.pval) = P_BUILD("functor", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 226:

/* Line 1464 of yacc.c  */
#line 669 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 227:

/* Line 1464 of yacc.c  */
#line 670 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 228:

/* Line 1464 of yacc.c  */
#line 673 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_atom", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 229:

/* Line 1464 of yacc.c  */
#line 674 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_atom", P_TOKEN("distinct_object ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 230:

/* Line 1464 of yacc.c  */
#line 677 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_atomic_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 231:

/* Line 1464 of yacc.c  */
#line 680 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_plain_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 232:

/* Line 1464 of yacc.c  */
#line 681 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_plain_term", (yyvsp[(1) - (4)].pval), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 233:

/* Line 1464 of yacc.c  */
#line 684 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_constant", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 234:

/* Line 1464 of yacc.c  */
#line 687 "tptp5.y"
    {(yyval.pval) = P_BUILD("defined_functor", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 235:

/* Line 1464 of yacc.c  */
#line 690 "tptp5.y"
    {(yyval.pval) = P_BUILD("system_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 236:

/* Line 1464 of yacc.c  */
#line 691 "tptp5.y"
    {(yyval.pval) = P_BUILD("system_term", (yyvsp[(1) - (4)].pval), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 237:

/* Line 1464 of yacc.c  */
#line 694 "tptp5.y"
    {(yyval.pval) = P_BUILD("system_constant", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 238:

/* Line 1464 of yacc.c  */
#line 697 "tptp5.y"
    {(yyval.pval) = P_BUILD("system_functor", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 239:

/* Line 1464 of yacc.c  */
#line 700 "tptp5.y"
    {(yyval.pval) = P_BUILD("variable", P_TOKEN("upper_word ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 240:

/* Line 1464 of yacc.c  */
#line 703 "tptp5.y"
    {(yyval.pval) = P_BUILD("arguments", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 241:

/* Line 1464 of yacc.c  */
#line 704 "tptp5.y"
    {(yyval.pval) = P_BUILD("arguments", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 242:

/* Line 1464 of yacc.c  */
#line 707 "tptp5.y"
    {(yyval.pval) = P_BUILD("conditional_term", P_TOKEN("_DLR_itett ", (yyvsp[(1) - (8)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (8)].ival)), (yyvsp[(3) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (8)].ival)), (yyvsp[(5) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (8)].ival)), (yyvsp[(7) - (8)].pval), P_TOKEN("RPAREN ", (yyvsp[(8) - (8)].ival)),NULL,NULL);;}
    break;

  case 243:

/* Line 1464 of yacc.c  */
#line 708 "tptp5.y"
    {(yyval.pval) = P_BUILD("conditional_term", P_TOKEN("_DLR_itetf ", (yyvsp[(1) - (8)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (8)].ival)), (yyvsp[(3) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(4) - (8)].ival)), (yyvsp[(5) - (8)].pval), P_TOKEN("COMMA ", (yyvsp[(6) - (8)].ival)), (yyvsp[(7) - (8)].pval), P_TOKEN("RPAREN ", (yyvsp[(8) - (8)].ival)),NULL,NULL);;}
    break;

  case 244:

/* Line 1464 of yacc.c  */
#line 711 "tptp5.y"
    {(yyval.pval) = P_BUILD("source", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 245:

/* Line 1464 of yacc.c  */
#line 714 "tptp5.y"
    {(yyval.pval) = P_BUILD("optional_info", P_TOKEN("COMMA ", (yyvsp[(1) - (2)].ival)), (yyvsp[(2) - (2)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 246:

/* Line 1464 of yacc.c  */
#line 715 "tptp5.y"
    {(yyval.pval) = P_BUILD("optional_info", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 247:

/* Line 1464 of yacc.c  */
#line 718 "tptp5.y"
    {(yyval.pval) = P_BUILD("useful_info", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 248:

/* Line 1464 of yacc.c  */
#line 721 "tptp5.y"
    {(yyval.pval) = P_BUILD("include", P_TOKEN("_LIT_include ", (yyvsp[(1) - (6)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (6)].ival)), (yyvsp[(3) - (6)].pval), (yyvsp[(4) - (6)].pval), P_TOKEN("RPAREN ", (yyvsp[(5) - (6)].ival)), P_TOKEN("PERIOD ", (yyvsp[(6) - (6)].ival)),NULL,NULL,NULL,NULL);;}
    break;

  case 249:

/* Line 1464 of yacc.c  */
#line 724 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_selection", P_TOKEN("COMMA ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LBRKT ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RBRKT ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 250:

/* Line 1464 of yacc.c  */
#line 725 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_selection", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 251:

/* Line 1464 of yacc.c  */
#line 728 "tptp5.y"
    {(yyval.pval) = P_BUILD("name_list", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 252:

/* Line 1464 of yacc.c  */
#line 729 "tptp5.y"
    {(yyval.pval) = P_BUILD("name_list", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 253:

/* Line 1464 of yacc.c  */
#line 732 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 254:

/* Line 1464 of yacc.c  */
#line 733 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_term", (yyvsp[(1) - (3)].pval), P_TOKEN("COLON ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 255:

/* Line 1464 of yacc.c  */
#line 734 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_term", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 256:

/* Line 1464 of yacc.c  */
#line 737 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 257:

/* Line 1464 of yacc.c  */
#line 738 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", (yyvsp[(1) - (4)].pval), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 258:

/* Line 1464 of yacc.c  */
#line 739 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 259:

/* Line 1464 of yacc.c  */
#line 740 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 260:

/* Line 1464 of yacc.c  */
#line 741 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", P_TOKEN("distinct_object ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 261:

/* Line 1464 of yacc.c  */
#line 742 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_data", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 262:

/* Line 1464 of yacc.c  */
#line 745 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_data", P_TOKEN("_DLR_thf ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 263:

/* Line 1464 of yacc.c  */
#line 746 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_data", P_TOKEN("_DLR_tff ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 264:

/* Line 1464 of yacc.c  */
#line 747 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_data", P_TOKEN("_DLR_fof ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 265:

/* Line 1464 of yacc.c  */
#line 748 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_data", P_TOKEN("_DLR_cnf ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 266:

/* Line 1464 of yacc.c  */
#line 749 "tptp5.y"
    {(yyval.pval) = P_BUILD("formula_data", P_TOKEN("_DLR_fot ", (yyvsp[(1) - (4)].ival)), P_TOKEN("LPAREN ", (yyvsp[(2) - (4)].ival)), (yyvsp[(3) - (4)].pval), P_TOKEN("RPAREN ", (yyvsp[(4) - (4)].ival)),NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 267:

/* Line 1464 of yacc.c  */
#line 752 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_list", P_TOKEN("LBRKT ", (yyvsp[(1) - (2)].ival)), P_TOKEN("RBRKT ", (yyvsp[(2) - (2)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 268:

/* Line 1464 of yacc.c  */
#line 753 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_list", P_TOKEN("LBRKT ", (yyvsp[(1) - (3)].ival)), (yyvsp[(2) - (3)].pval), P_TOKEN("RBRKT ", (yyvsp[(3) - (3)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 269:

/* Line 1464 of yacc.c  */
#line 756 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_terms", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 270:

/* Line 1464 of yacc.c  */
#line 757 "tptp5.y"
    {(yyval.pval) = P_BUILD("general_terms", (yyvsp[(1) - (3)].pval), P_TOKEN("COMMA ", (yyvsp[(2) - (3)].ival)), (yyvsp[(3) - (3)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 271:

/* Line 1464 of yacc.c  */
#line 760 "tptp5.y"
    {(yyval.pval) = P_BUILD("name", (yyvsp[(1) - (1)].pval),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 272:

/* Line 1464 of yacc.c  */
#line 761 "tptp5.y"
    {(yyval.pval) = P_BUILD("name", P_TOKEN("integer ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 273:

/* Line 1464 of yacc.c  */
#line 764 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_word", P_TOKEN("lower_word ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 274:

/* Line 1464 of yacc.c  */
#line 765 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_word", P_TOKEN("single_quoted ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 275:

/* Line 1464 of yacc.c  */
#line 768 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_defined_word", P_TOKEN("dollar_word ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 276:

/* Line 1464 of yacc.c  */
#line 771 "tptp5.y"
    {(yyval.pval) = P_BUILD("atomic_system_word", P_TOKEN("dollar_dollar_word ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 277:

/* Line 1464 of yacc.c  */
#line 774 "tptp5.y"
    {(yyval.pval) = P_BUILD("number", P_TOKEN("integer ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 278:

/* Line 1464 of yacc.c  */
#line 775 "tptp5.y"
    {(yyval.pval) = P_BUILD("number", P_TOKEN("rational ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 279:

/* Line 1464 of yacc.c  */
#line 776 "tptp5.y"
    {(yyval.pval) = P_BUILD("number", P_TOKEN("real ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 280:

/* Line 1464 of yacc.c  */
#line 779 "tptp5.y"
    {(yyval.pval) = P_BUILD("file_name", P_TOKEN("single_quoted ", (yyvsp[(1) - (1)].ival)),NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;

  case 281:

/* Line 1464 of yacc.c  */
#line 782 "tptp5.y"
    {(yyval.pval) = P_BUILD("null",NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL);;}
    break;



/* Line 1464 of yacc.c  */
#line 4264 "tptp5.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



