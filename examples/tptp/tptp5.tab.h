/* A Bison parser, made by GNU Bison 2.4.2.  */

/* Skeleton interface for Bison's Yacc-like parsers in C
   
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

/* Line 1685 of yacc.c  */
#line 148 "tptp5.y"
int ival; double dval; char* sval; TreeNode* pval;


/* Line 1685 of yacc.c  */
#line 130 "tptp5.tab.h"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif

extern YYSTYPE yylval;


