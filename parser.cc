// A Bison parser, made by GNU Bison 3.8.2.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015, 2018-2021 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.





#include "grammar.hh"


// Unqualified %code blocks.
#line 34 "drewgon.yy"

   // C std code for utility functions
   #include <iostream>
   #include <cstdlib>
   #include <fstream>

   // Our code for interoperation between scanner/parser
   #include "scanner.hpp"
   #include "ast.hpp"
   #include "tokens.hpp"

  //Request tokens from our scanner member, not
  // from a global function
  #undef yylex
  #define yylex scanner.yylex

#line 63 "parser.cc"


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif


// Whether we are compiled with exception support.
#ifndef YY_EXCEPTIONS
# if defined __GNUC__ && !defined __EXCEPTIONS
#  define YY_EXCEPTIONS 0
# else
#  define YY_EXCEPTIONS 1
# endif
#endif



// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << '\n';                       \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yy_stack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YY_USE (Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void> (0)
# define YY_STACK_PRINT()                static_cast<void> (0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 5 "drewgon.yy"
namespace drewgon {
#line 137 "parser.cc"

  /// Build a parser object.
  Parser::Parser (drewgon::Scanner &scanner_yyarg, drewgon::ProgramNode** root_yyarg)
#if YYDEBUG
    : yydebug_ (false),
      yycdebug_ (&std::cerr),
#else
    :
#endif
      scanner (scanner_yyarg),
      root (root_yyarg)
  {}

  Parser::~Parser ()
  {}

  Parser::syntax_error::~syntax_error () YY_NOEXCEPT YY_NOTHROW
  {}

  /*---------.
  | symbol.  |
  `---------*/

  // basic_symbol.
  template <typename Base>
  Parser::basic_symbol<Base>::basic_symbol (const basic_symbol& that)
    : Base (that)
    , value (that.value)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  Parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t)
    : Base (t)
    , value ()
  {}

  template <typename Base>
  Parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_RVREF (value_type) v)
    : Base (t)
    , value (YY_MOVE (v))
  {}


  template <typename Base>
  Parser::symbol_kind_type
  Parser::basic_symbol<Base>::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }


  template <typename Base>
  bool
  Parser::basic_symbol<Base>::empty () const YY_NOEXCEPT
  {
    return this->kind () == symbol_kind::S_YYEMPTY;
  }

  template <typename Base>
  void
  Parser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move (s);
    value = YY_MOVE (s.value);
  }

  // by_kind.
  Parser::by_kind::by_kind () YY_NOEXCEPT
    : kind_ (symbol_kind::S_YYEMPTY)
  {}

#if 201103L <= YY_CPLUSPLUS
  Parser::by_kind::by_kind (by_kind&& that) YY_NOEXCEPT
    : kind_ (that.kind_)
  {
    that.clear ();
  }
#endif

  Parser::by_kind::by_kind (const by_kind& that) YY_NOEXCEPT
    : kind_ (that.kind_)
  {}

  Parser::by_kind::by_kind (token_kind_type t) YY_NOEXCEPT
    : kind_ (yytranslate_ (t))
  {}



  void
  Parser::by_kind::clear () YY_NOEXCEPT
  {
    kind_ = symbol_kind::S_YYEMPTY;
  }

  void
  Parser::by_kind::move (by_kind& that)
  {
    kind_ = that.kind_;
    that.clear ();
  }

  Parser::symbol_kind_type
  Parser::by_kind::kind () const YY_NOEXCEPT
  {
    return kind_;
  }


  Parser::symbol_kind_type
  Parser::by_kind::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }



  // by_state.
  Parser::by_state::by_state () YY_NOEXCEPT
    : state (empty_state)
  {}

  Parser::by_state::by_state (const by_state& that) YY_NOEXCEPT
    : state (that.state)
  {}

  void
  Parser::by_state::clear () YY_NOEXCEPT
  {
    state = empty_state;
  }

  void
  Parser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  Parser::by_state::by_state (state_type s) YY_NOEXCEPT
    : state (s)
  {}

  Parser::symbol_kind_type
  Parser::by_state::kind () const YY_NOEXCEPT
  {
    if (state == empty_state)
      return symbol_kind::S_YYEMPTY;
    else
      return YY_CAST (symbol_kind_type, yystos_[+state]);
  }

  Parser::stack_symbol_type::stack_symbol_type ()
  {}

  Parser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.value))
  {
#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  Parser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.value))
  {
    // that is emptied.
    that.kind_ = symbol_kind::S_YYEMPTY;
  }

#if YY_CPLUSPLUS < 201103L
  Parser::stack_symbol_type&
  Parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    return *this;
  }

  Parser::stack_symbol_type&
  Parser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    // that is emptied.
    that.state = empty_state;
    return *this;
  }
#endif

  template <typename Base>
  void
  Parser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);

    // User destructor.
    YY_USE (yysym.kind ());
  }

#if YYDEBUG
  template <typename Base>
  void
  Parser::yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YY_USE (yyoutput);
    if (yysym.empty ())
      yyo << "empty symbol";
    else
      {
        symbol_kind_type yykind = yysym.kind ();
        yyo << (yykind < YYNTOKENS ? "token" : "nterm")
            << ' ' << yysym.name () << " (";
        YY_USE (yykind);
        yyo << ')';
      }
  }
#endif

  void
  Parser::yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym)
  {
    if (m)
      YY_SYMBOL_PRINT (m, sym);
    yystack_.push (YY_MOVE (sym));
  }

  void
  Parser::yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym)
  {
#if 201103L <= YY_CPLUSPLUS
    yypush_ (m, stack_symbol_type (s, std::move (sym)));
#else
    stack_symbol_type ss (s, sym);
    yypush_ (m, ss);
#endif
  }

  void
  Parser::yypop_ (int n) YY_NOEXCEPT
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  Parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  Parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  Parser::debug_level_type
  Parser::debug_level () const
  {
    return yydebug_;
  }

  void
  Parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  Parser::state_type
  Parser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - YYNTOKENS] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - YYNTOKENS];
  }

  bool
  Parser::yy_pact_value_is_default_ (int yyvalue) YY_NOEXCEPT
  {
    return yyvalue == yypact_ninf_;
  }

  bool
  Parser::yy_table_value_is_error_ (int yyvalue) YY_NOEXCEPT
  {
    return yyvalue == yytable_ninf_;
  }

  int
  Parser::operator() ()
  {
    return parse ();
  }

  int
  Parser::parse ()
  {
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The return value of parse ().
    int yyresult;

#if YY_EXCEPTIONS
    try
#endif // YY_EXCEPTIONS
      {
    YYCDEBUG << "Starting parse\n";


    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, YY_MOVE (yyla));

  /*-----------------------------------------------.
  | yynewstate -- push a new symbol on the stack.  |
  `-----------------------------------------------*/
  yynewstate:
    YYCDEBUG << "Entering state " << int (yystack_[0].state) << '\n';
    YY_STACK_PRINT ();

    // Accept?
    if (yystack_[0].state == yyfinal_)
      YYACCEPT;

    goto yybackup;


  /*-----------.
  | yybackup.  |
  `-----------*/
  yybackup:
    // Try to take a decision without lookahead.
    yyn = yypact_[+yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token\n";
#if YY_EXCEPTIONS
        try
#endif // YY_EXCEPTIONS
          {
            yyla.kind_ = yytranslate_ (yylex (&yyla.value));
          }
#if YY_EXCEPTIONS
        catch (const syntax_error& yyexc)
          {
            YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
            error (yyexc);
            goto yyerrlab1;
          }
#endif // YY_EXCEPTIONS
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    if (yyla.kind () == symbol_kind::S_YYerror)
    {
      // The scanner already issued an error message, process directly
      // to error recovery.  But do not keep the error token as
      // lookahead, it is too special and may lead us to an endless
      // loop in error recovery. */
      yyla.kind_ = symbol_kind::S_YYUNDEF;
      goto yyerrlab1;
    }

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.kind ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.kind ())
      {
        goto yydefault;
      }

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", state_type (yyn), YY_MOVE (yyla));
    goto yynewstate;


  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[+yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;


  /*-----------------------------.
  | yyreduce -- do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_ (yystack_[yylen].state, yyr1_[yyn]);
      /* If YYLEN is nonzero, implement the default value of the
         action: '$$ = $1'.  Otherwise, use the top of the stack.

         Otherwise, the following line sets YYLHS.VALUE to garbage.
         This behavior is undocumented and Bison users should not rely
         upon it.  */
      if (yylen)
        yylhs.value = yystack_[yylen - 1].value;
      else
        yylhs.value = yystack_[0].value;


      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
#if YY_EXCEPTIONS
      try
#endif // YY_EXCEPTIONS
        {
          switch (yyn)
            {
  case 2: // program: globals
#line 158 "drewgon.yy"
                  {
		  (yylhs.value.transProgram) = new ProgramNode((yystack_[0].value.transDeclList));
		  *root = (yylhs.value.transProgram);
		  }
#line 598 "parser.cc"
    break;

  case 3: // globals: globals varDecl SEMICOL
#line 164 "drewgon.yy"
                  {
	  	  (yylhs.value.transDeclList) = (yystack_[2].value.transDeclList);
	  	  DeclNode * declNode = (yystack_[1].value.transVarDecl);
		  (yylhs.value.transDeclList)->push_back(declNode);
	  	  }
#line 608 "parser.cc"
    break;

  case 4: // globals: globals fnDecl
#line 170 "drewgon.yy"
                  {
	  	  (yylhs.value.transDeclList) = (yystack_[1].value.transDeclList);
	  	  DeclNode * declNode = (yystack_[0].value.transFn);
		  (yylhs.value.transDeclList)->push_back(declNode);
		  }
#line 618 "parser.cc"
    break;

  case 5: // globals: %empty
#line 177 "drewgon.yy"
                  {
		  (yylhs.value.transDeclList) = new std::list<DeclNode * >();
		  }
#line 626 "parser.cc"
    break;

  case 6: // varDecl: type id
#line 182 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transType)->pos(), (yystack_[0].value.transID)->pos());
		  (yylhs.value.transVarDecl) = new VarDeclNode(p, (yystack_[1].value.transType), (yystack_[0].value.transID));
		  }
#line 635 "parser.cc"
    break;

  case 7: // type: primType
#line 188 "drewgon.yy"
                  {
		  (yylhs.value.transType) = (yystack_[0].value.transType);
		  }
#line 643 "parser.cc"
    break;

  case 8: // type: FN fnType
#line 192 "drewgon.yy"
                  {
		  (yylhs.value.transType) = (yystack_[0].value.transFnType);
		  }
#line 651 "parser.cc"
    break;

  case 9: // primType: INT
#line 197 "drewgon.yy"
                  {
		  (yylhs.value.transType) = new IntTypeNode((yystack_[0].value.transToken)->pos());
		  }
#line 659 "parser.cc"
    break;

  case 10: // primType: BOOL
#line 201 "drewgon.yy"
                  {
		  (yylhs.value.transType) = new BoolTypeNode((yystack_[0].value.transToken)->pos());
		  }
#line 667 "parser.cc"
    break;

  case 11: // primType: VOID
#line 205 "drewgon.yy"
                  {
		  (yylhs.value.transType) = new VoidTypeNode((yystack_[0].value.transToken)->pos());
		  }
#line 675 "parser.cc"
    break;

  case 12: // fnType: LPAREN typeList RPAREN ARROW type
#line 210 "drewgon.yy"
                  {
		  const Position * pos = new Position((yystack_[4].value.transToken)->pos(), (yystack_[0].value.transType)->pos());
		  (yylhs.value.transFnType) = new FnTypeNode(pos, (yystack_[3].value.transTypeList), (yystack_[0].value.transType));
		  }
#line 684 "parser.cc"
    break;

  case 13: // fnType: LPAREN RPAREN ARROW type
#line 215 "drewgon.yy"
                  {
		  const Position * pos = new Position((yystack_[3].value.transToken)->pos(), (yystack_[0].value.transType)->pos());
		  std::list<TypeNode *> * n = new std::list<TypeNode *>();
		  (yylhs.value.transFnType) = new FnTypeNode(pos,n,(yystack_[0].value.transType));
		  }
#line 694 "parser.cc"
    break;

  case 14: // typeList: type
#line 222 "drewgon.yy"
                  {
		  (yylhs.value.transTypeList) = new std::list<TypeNode *>();
		  (yylhs.value.transTypeList)->push_back((yystack_[0].value.transType));
		  }
#line 703 "parser.cc"
    break;

  case 15: // typeList: typeList COMMA type
#line 227 "drewgon.yy"
                  {
		  (yylhs.value.transTypeList) = (yystack_[2].value.transTypeList);
		  (yylhs.value.transTypeList)->push_back((yystack_[0].value.transType));
		  }
#line 712 "parser.cc"
    break;

  case 16: // fnDecl: type id LPAREN RPAREN LCURLY stmtList RCURLY
#line 234 "drewgon.yy"
                  {
		  const Position * pos = new Position((yystack_[6].value.transType)->pos(), (yystack_[0].value.transToken)->pos());
		  std::list<FormalDeclNode *> * f = new std::list<FormalDeclNode *>();
		  (yylhs.value.transFn) = new FnDeclNode(pos, (yystack_[6].value.transType), (yystack_[5].value.transID), f, (yystack_[1].value.transStmts));
		  }
#line 722 "parser.cc"
    break;

  case 17: // fnDecl: type id LPAREN formals RPAREN LCURLY stmtList RCURLY
#line 240 "drewgon.yy"
                  {
		  const Position * pos = new Position((yystack_[7].value.transType)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transFn) = new FnDeclNode(pos, (yystack_[7].value.transType), (yystack_[6].value.transID), (yystack_[4].value.transFormalList), (yystack_[1].value.transStmts));
		  }
#line 731 "parser.cc"
    break;

  case 18: // formals: formalDecl
#line 246 "drewgon.yy"
                  {
		  (yylhs.value.transFormalList) = new std::list<FormalDeclNode *>();
		  (yylhs.value.transFormalList)->push_back((yystack_[0].value.transFormal));
		  }
#line 740 "parser.cc"
    break;

  case 19: // formals: formals COMMA formalDecl
#line 251 "drewgon.yy"
                  {
		  (yylhs.value.transFormalList) = (yystack_[2].value.transFormalList);
		  (yylhs.value.transFormalList)->push_back((yystack_[0].value.transFormal));
		  }
#line 749 "parser.cc"
    break;

  case 20: // formalDecl: type id
#line 257 "drewgon.yy"
                  {
		  const Position * pos = new Position((yystack_[1].value.transType)->pos(), (yystack_[0].value.transID)->pos());
		  (yylhs.value.transFormal) = new FormalDeclNode(pos, (yystack_[1].value.transType), (yystack_[0].value.transID));
		  }
#line 758 "parser.cc"
    break;

  case 21: // stmtList: %empty
#line 263 "drewgon.yy"
                  {
		  (yylhs.value.transStmts) = new std::list<StmtNode *>();
	   	  }
#line 766 "parser.cc"
    break;

  case 22: // stmtList: stmtList stmt SEMICOL
#line 267 "drewgon.yy"
                  {
		  (yylhs.value.transStmts) = (yystack_[2].value.transStmts);
		  (yylhs.value.transStmts)->push_back((yystack_[1].value.transStmt));
	  	  }
#line 775 "parser.cc"
    break;

  case 23: // stmtList: stmtList blockStmt
#line 272 "drewgon.yy"
                  {
		  (yylhs.value.transStmts) = (yystack_[1].value.transStmts);
		  (yylhs.value.transStmts)->push_back((yystack_[0].value.transStmt));
	  	  }
#line 784 "parser.cc"
    break;

  case 24: // blockStmt: WHILE LPAREN exp RPAREN LCURLY stmtList RCURLY
#line 278 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[6].value.transToken)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new WhileStmtNode(p, (yystack_[4].value.transExp), (yystack_[1].value.transStmts));
		  }
#line 793 "parser.cc"
    break;

  case 25: // blockStmt: FOR LPAREN stmt SEMICOL exp SEMICOL stmt RPAREN LCURLY stmtList RCURLY
#line 283 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[10].value.transToken)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new ForStmtNode(p, (yystack_[8].value.transStmt), (yystack_[6].value.transExp), (yystack_[4].value.transStmt), (yystack_[1].value.transStmts));
		  }
#line 802 "parser.cc"
    break;

  case 26: // blockStmt: IF LPAREN exp RPAREN LCURLY stmtList RCURLY
#line 288 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[6].value.transToken)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new IfStmtNode(p, (yystack_[4].value.transExp), (yystack_[1].value.transStmts));
		  }
#line 811 "parser.cc"
    break;

  case 27: // blockStmt: IF LPAREN exp RPAREN LCURLY stmtList RCURLY ELSE LCURLY stmtList RCURLY
#line 293 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[10].value.transToken)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new IfElseStmtNode(p, (yystack_[8].value.transExp), (yystack_[5].value.transStmts), (yystack_[1].value.transStmts));
		  }
#line 820 "parser.cc"
    break;

  case 28: // stmt: varDecl
#line 299 "drewgon.yy"
                  {
		  const Position * p = (yystack_[0].value.transVarDecl)->pos();
		  (yylhs.value.transStmt) = new VarDeclNode(p, (yystack_[0].value.transVarDecl)->getTypeNode(), (yystack_[0].value.transVarDecl)->ID());
		  }
#line 829 "parser.cc"
    break;

  case 29: // stmt: assignExp
#line 304 "drewgon.yy"
                  {
		  (yylhs.value.transStmt) = new AssignStmtNode((yystack_[0].value.transAssignExp)->pos(), (yystack_[0].value.transAssignExp));
		  }
#line 837 "parser.cc"
    break;

  case 30: // stmt: id POSTDEC
#line 308 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transID)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new PostDecStmtNode(p, (yystack_[1].value.transID));
		  }
#line 846 "parser.cc"
    break;

  case 31: // stmt: id POSTINC
#line 313 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transID)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transStmt) = new PostIncStmtNode(p, (yystack_[1].value.transID));
		  }
#line 855 "parser.cc"
    break;

  case 32: // stmt: INPUT id
#line 318 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transToken)->pos(), (yystack_[0].value.transID)->pos());
		  (yylhs.value.transStmt) = new InputStmtNode(p, (yystack_[0].value.transID));
		  }
#line 864 "parser.cc"
    break;

  case 33: // stmt: OUTPUT exp
#line 323 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transToken)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transStmt) = new OutputStmtNode(p, (yystack_[0].value.transExp));
		  }
#line 873 "parser.cc"
    break;

  case 34: // stmt: RETURN exp
#line 328 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transToken)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transStmt) = new ReturnStmtNode(p, (yystack_[0].value.transExp));
		  }
#line 882 "parser.cc"
    break;

  case 35: // stmt: RETURN
#line 333 "drewgon.yy"
                  {
		  (yylhs.value.transStmt) = new ReturnStmtNode((yystack_[0].value.transToken)->pos(), nullptr);
		  }
#line 890 "parser.cc"
    break;

  case 36: // stmt: callExp
#line 337 "drewgon.yy"
                  {
		  (yylhs.value.transStmt) = new CallStmtNode((yystack_[0].value.transCallExp)->pos(), (yystack_[0].value.transCallExp));
		  }
#line 898 "parser.cc"
    break;

  case 37: // exp: assignExp
#line 342 "drewgon.yy"
                  { (yylhs.value.transExp) = (yystack_[0].value.transAssignExp); }
#line 904 "parser.cc"
    break;

  case 38: // exp: exp MINUS exp
#line 344 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new MinusNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 913 "parser.cc"
    break;

  case 39: // exp: exp PLUS exp
#line 349 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new PlusNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 922 "parser.cc"
    break;

  case 40: // exp: exp TIMES exp
#line 354 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new TimesNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 931 "parser.cc"
    break;

  case 41: // exp: exp DIVIDE exp
#line 359 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new DivideNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 940 "parser.cc"
    break;

  case 42: // exp: exp AND exp
#line 364 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new AndNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 949 "parser.cc"
    break;

  case 43: // exp: exp OR exp
#line 369 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new OrNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 958 "parser.cc"
    break;

  case 44: // exp: exp EQUALS exp
#line 374 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new EqualsNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 967 "parser.cc"
    break;

  case 45: // exp: exp NOTEQUALS exp
#line 379 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new NotEqualsNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 976 "parser.cc"
    break;

  case 46: // exp: exp GREATER exp
#line 384 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new GreaterNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 985 "parser.cc"
    break;

  case 47: // exp: exp GREATEREQ exp
#line 389 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new GreaterEqNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 994 "parser.cc"
    break;

  case 48: // exp: exp LESS exp
#line 394 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new LessNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 1003 "parser.cc"
    break;

  case 49: // exp: exp LESSEQ exp
#line 399 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transExp)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new LessEqNode(p, (yystack_[2].value.transExp), (yystack_[0].value.transExp));
		  }
#line 1012 "parser.cc"
    break;

  case 50: // exp: NOT exp
#line 404 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transToken)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new NotNode(p, (yystack_[0].value.transExp));
		  }
#line 1021 "parser.cc"
    break;

  case 51: // exp: MINUS term
#line 409 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[1].value.transToken)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transExp) = new NegNode(p, (yystack_[0].value.transExp));
		  }
#line 1030 "parser.cc"
    break;

  case 52: // exp: term
#line 414 "drewgon.yy"
                  { (yylhs.value.transExp) = (yystack_[0].value.transExp); }
#line 1036 "parser.cc"
    break;

  case 53: // assignExp: id ASSIGN exp
#line 417 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transID)->pos(), (yystack_[0].value.transExp)->pos());
		  (yylhs.value.transAssignExp) = new AssignExpNode(p, (yystack_[2].value.transID), (yystack_[0].value.transExp));
		  }
#line 1045 "parser.cc"
    break;

  case 54: // callExp: id LPAREN RPAREN
#line 423 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[2].value.transID)->pos(), (yystack_[0].value.transToken)->pos());
		  std::list<ExpNode *> * noargs =
		    new std::list<ExpNode *>();
		  (yylhs.value.transCallExp) = new CallExpNode(p, (yystack_[2].value.transID), noargs);
		  }
#line 1056 "parser.cc"
    break;

  case 55: // callExp: id LPAREN actualsList RPAREN
#line 430 "drewgon.yy"
                  {
		  const Position * p = new Position((yystack_[3].value.transID)->pos(), (yystack_[0].value.transToken)->pos());
		  (yylhs.value.transCallExp) = new CallExpNode(p, (yystack_[3].value.transID), (yystack_[1].value.transActuals));
		  }
#line 1065 "parser.cc"
    break;

  case 56: // actualsList: exp
#line 436 "drewgon.yy"
                  {
		  std::list<ExpNode *> * list =
		    new std::list<ExpNode *>();
		  list->push_back((yystack_[0].value.transExp));
		  (yylhs.value.transActuals) = list;
		  }
#line 1076 "parser.cc"
    break;

  case 57: // actualsList: actualsList COMMA exp
#line 443 "drewgon.yy"
                  {
		  (yylhs.value.transActuals) = (yystack_[2].value.transActuals);
		  (yylhs.value.transActuals)->push_back((yystack_[0].value.transExp));
		  }
#line 1085 "parser.cc"
    break;

  case 58: // term: id
#line 449 "drewgon.yy"
                  { (yylhs.value.transExp) = (yystack_[0].value.transID); }
#line 1091 "parser.cc"
    break;

  case 59: // term: INTLITERAL
#line 451 "drewgon.yy"
                  { (yylhs.value.transExp) = new IntLitNode((yystack_[0].value.transIntToken)->pos(), (yystack_[0].value.transIntToken)->num()); }
#line 1097 "parser.cc"
    break;

  case 60: // term: STRINGLITERAL
#line 453 "drewgon.yy"
                  { (yylhs.value.transExp) = new StrLitNode((yystack_[0].value.transStrToken)->pos(), (yystack_[0].value.transStrToken)->str()); }
#line 1103 "parser.cc"
    break;

  case 61: // term: TRUE
#line 455 "drewgon.yy"
                  { (yylhs.value.transExp) = new TrueNode((yystack_[0].value.transToken)->pos()); }
#line 1109 "parser.cc"
    break;

  case 62: // term: FALSE
#line 457 "drewgon.yy"
                  { (yylhs.value.transExp) = new FalseNode((yystack_[0].value.transToken)->pos()); }
#line 1115 "parser.cc"
    break;

  case 63: // term: LPAREN exp RPAREN
#line 459 "drewgon.yy"
                  { (yylhs.value.transExp) = (yystack_[1].value.transExp); }
#line 1121 "parser.cc"
    break;

  case 64: // term: MAYHEM
#line 461 "drewgon.yy"
                  { (yylhs.value.transExp) = new MayhemNode((yystack_[0].value.transToken)->pos()); }
#line 1127 "parser.cc"
    break;

  case 65: // term: callExp
#line 463 "drewgon.yy"
                  { (yylhs.value.transExp) = (yystack_[0].value.transCallExp); }
#line 1133 "parser.cc"
    break;

  case 66: // id: ID
#line 466 "drewgon.yy"
                  {
		  const Position * pos = (yystack_[0].value.transIDToken)->pos();
		  (yylhs.value.transID) = new IDNode(pos, (yystack_[0].value.transIDToken)->value());
		  }
#line 1142 "parser.cc"
    break;


#line 1146 "parser.cc"

            default:
              break;
            }
        }
#if YY_EXCEPTIONS
      catch (const syntax_error& yyexc)
        {
          YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
          error (yyexc);
          YYERROR;
        }
#endif // YY_EXCEPTIONS
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, YY_MOVE (yylhs));
    }
    goto yynewstate;


  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        context yyctx (*this, yyla);
        std::string msg = yysyntax_error_ (yyctx);
        error (YY_MOVE (msg));
      }


    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.kind () == symbol_kind::S_YYEOF)
          YYABORT;
        else if (!yyla.empty ())
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyla.clear ();
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:
    /* Pacify compilers when the user code never invokes YYERROR and
       the label yyerrorlab therefore never appears in user code.  */
    if (false)
      YYERROR;

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    YY_STACK_PRINT ();
    goto yyerrlab1;


  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    // Pop stack until we find a state that shifts the error token.
    for (;;)
      {
        yyn = yypact_[+yystack_[0].state];
        if (!yy_pact_value_is_default_ (yyn))
          {
            yyn += symbol_kind::S_YYerror;
            if (0 <= yyn && yyn <= yylast_
                && yycheck_[yyn] == symbol_kind::S_YYerror)
              {
                yyn = yytable_[yyn];
                if (0 < yyn)
                  break;
              }
          }

        // Pop the current state because it cannot handle the error token.
        if (yystack_.size () == 1)
          YYABORT;

        yy_destroy_ ("Error: popping", yystack_[0]);
        yypop_ ();
        YY_STACK_PRINT ();
      }
    {
      stack_symbol_type error_token;


      // Shift the error token.
      error_token.state = state_type (yyn);
      yypush_ ("Shifting", YY_MOVE (error_token));
    }
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


  /*-----------------------------------------------------.
  | yyreturn -- parsing is finished, return the result.  |
  `-----------------------------------------------------*/
  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    YY_STACK_PRINT ();
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
#if YY_EXCEPTIONS
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack\n";
        // Do not try to display the values of the reclaimed symbols,
        // as their printers might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
#endif // YY_EXCEPTIONS
  }

  void
  Parser::error (const syntax_error& yyexc)
  {
    error (yyexc.what ());
  }

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  Parser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr;
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
              else
                goto append;

            append:
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }

  std::string
  Parser::symbol_name (symbol_kind_type yysymbol)
  {
    return yytnamerr_ (yytname_[yysymbol]);
  }



  // Parser::context.
  Parser::context::context (const Parser& yyparser, const symbol_type& yyla)
    : yyparser_ (yyparser)
    , yyla_ (yyla)
  {}

  int
  Parser::context::expected_tokens (symbol_kind_type yyarg[], int yyargn) const
  {
    // Actual number of expected tokens
    int yycount = 0;

    const int yyn = yypact_[+yyparser_.yystack_[0].state];
    if (!yy_pact_value_is_default_ (yyn))
      {
        /* Start YYX at -YYN if negative to avoid negative indexes in
           YYCHECK.  In other words, skip the first -YYN actions for
           this state because they are default actions.  */
        const int yyxbegin = yyn < 0 ? -yyn : 0;
        // Stay within bounds of both yycheck and yytname.
        const int yychecklim = yylast_ - yyn + 1;
        const int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
        for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
          if (yycheck_[yyx + yyn] == yyx && yyx != symbol_kind::S_YYerror
              && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
            {
              if (!yyarg)
                ++yycount;
              else if (yycount == yyargn)
                return 0;
              else
                yyarg[yycount++] = YY_CAST (symbol_kind_type, yyx);
            }
      }

    if (yyarg && yycount == 0 && 0 < yyargn)
      yyarg[0] = symbol_kind::S_YYEMPTY;
    return yycount;
  }






  int
  Parser::yy_syntax_error_arguments_ (const context& yyctx,
                                                 symbol_kind_type yyarg[], int yyargn) const
  {
    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yyla) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state merging
         (from LALR or IELR) and default reductions corrupt the expected
         token list.  However, the list is correct for canonical LR with
         one exception: it will still contain any token that will not be
         accepted due to an error action in a later state.
    */

    if (!yyctx.lookahead ().empty ())
      {
        if (yyarg)
          yyarg[0] = yyctx.token ();
        int yyn = yyctx.expected_tokens (yyarg ? yyarg + 1 : yyarg, yyargn - 1);
        return yyn + 1;
      }
    return 0;
  }

  // Generate an error message.
  std::string
  Parser::yysyntax_error_ (const context& yyctx) const
  {
    // Its maximum.
    enum { YYARGS_MAX = 5 };
    // Arguments of yyformat.
    symbol_kind_type yyarg[YYARGS_MAX];
    int yycount = yy_syntax_error_arguments_ (yyctx, yyarg, YYARGS_MAX);

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
      default: // Avoid compiler warnings.
        YYCASE_ (0, YY_("syntax error"));
        YYCASE_ (1, YY_("syntax error, unexpected %s"));
        YYCASE_ (2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_ (3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_ (4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_ (5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    std::string yyres;
    // Argument number.
    std::ptrdiff_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += symbol_name (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const signed char Parser::yypact_ninf_ = -52;

  const signed char Parser::yytable_ninf_ = -1;

  const short
  Parser::yypact_[] =
  {
     -52,     6,    17,   -52,   -52,   -16,   -52,   -52,   -28,    -6,
     -52,   -52,     1,   -52,   -52,   -52,   -10,    11,   -52,    -2,
       5,    17,    17,    21,     9,    -6,    19,   -52,   -52,   -52,
      17,   -52,   -52,    17,    31,   -52,   244,   -52,   -52,    38,
      39,    -6,   472,   472,   -52,    41,   -52,    -6,   -52,    29,
     -52,   -52,    74,   253,   409,   472,   -52,   -52,   -52,   472,
     489,   -52,   472,   -52,   -52,   288,   -52,   -52,   -52,    52,
     288,   472,   -52,   -52,   472,   455,   -52,   -52,   -52,    33,
      25,   162,   -52,    48,   -52,   472,   472,   472,   472,   472,
     472,   472,   472,   472,   472,   472,   472,   189,   288,   -52,
     288,    24,   472,    50,   -52,   423,   -52,   445,   445,   445,
     445,   445,     4,   445,   395,     4,   -52,    53,   472,   -52,
     216,   -52,   -52,   288,   409,   312,   332,    42,    66,   -52,
      60,    61,   -52,   -52,   352,   372,   -52,   -52
  };

  const signed char
  Parser::yydefact_[] =
  {
       5,     0,     2,     1,    10,     0,     9,    11,     0,     0,
       7,     4,     0,     8,     3,    66,     6,     0,    14,     0,
       0,     0,     0,     0,     0,     0,     0,    18,    13,    15,
       0,    21,    20,     0,     0,    12,     0,    19,    21,     0,
       0,     0,     0,    35,    16,     0,    28,     0,    23,     0,
      29,    36,     0,     0,     0,     0,    32,    62,    59,     0,
       0,    64,     0,    60,    61,    33,    37,    65,    52,    58,
      34,     0,     6,    22,     0,     0,    30,    31,    17,     0,
       0,     0,    51,    58,    50,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    53,    54,
      56,     0,     0,     0,    63,    42,    41,    44,    46,    47,
      48,    49,    38,    45,    43,    39,    40,     0,     0,    55,
       0,    21,    21,    57,     0,     0,     0,     0,    26,    24,
       0,     0,    21,    21,     0,     0,    25,    27
  };

  const signed char
  Parser::yypgoto_[] =
  {
     -52,   -52,   -52,    81,    47,   -52,   -52,   -52,   -52,   -52,
      51,   -36,   -52,   -51,    65,   -35,   -32,   -52,    27,    -9
  };

  const signed char
  Parser::yydefgoto_[] =
  {
       0,     1,     2,    46,    47,    10,    13,    19,    11,    26,
      27,    36,    48,    49,    65,    66,    67,   101,    68,    69
  };

  const short
  Parser::yytable_[] =
  {
      16,    50,    53,    79,    51,    22,     3,     4,    12,    14,
      15,     4,    86,     5,    20,    21,    32,     5,    50,    50,
       6,    51,    51,     4,     6,    30,    33,    52,    85,     5,
      31,   118,    56,    86,    23,    87,     6,    17,    72,    88,
      89,    24,     7,    96,    52,    52,     7,    90,    91,     9,
      92,    83,    38,    93,    94,    34,    95,    74,     7,    18,
     119,   103,    54,    55,    96,    71,    73,    25,    28,    29,
     102,   121,    75,   127,   122,   131,    75,    35,   130,    74,
      25,   132,   133,     8,    37,   125,   126,    82,     0,    50,
      50,    50,    51,    51,    51,     0,   134,   135,    75,    50,
      50,     0,    51,    51,     0,     0,    76,    77,    70,     0,
       0,     0,     0,     0,     0,    52,    52,    52,     0,     0,
      80,     0,     0,     0,    81,    52,    52,    84,     0,     0,
       0,     0,     0,     0,     0,     0,    97,     0,     0,    98,
     100,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,     0,     0,     0,    85,     0,   120,     0,     0,
      86,     0,    87,     0,     0,     0,    88,    89,     0,     0,
       0,     0,     0,   123,    90,    91,     0,    92,     0,     0,
      93,    94,    85,    95,     0,     0,     0,    86,   104,    87,
       0,    96,     0,    88,    89,     0,     0,     0,     0,     0,
       0,    90,    91,     0,    92,     0,     0,    93,    94,    85,
      95,     0,     0,     0,    86,   117,    87,     0,    96,     0,
      88,    89,     0,     0,     0,     0,     0,     0,    90,    91,
       0,    92,     0,     0,    93,    94,     0,    95,     0,     0,
       4,     0,     0,   124,     0,    96,     5,    39,     0,     4,
      15,    40,    41,     6,     0,     5,    39,     0,     0,    15,
      40,    41,     6,     0,    42,     0,     0,     0,    43,    44,
       0,     0,     0,    42,     0,     7,    45,    43,    78,     0,
       0,    85,     0,     0,     7,    45,    86,     0,    87,     0,
       0,     0,    88,    89,     0,     0,     0,     0,     0,     0,
      90,    91,     0,    92,     0,     0,    93,    94,     4,    95,
       0,     0,     0,     0,     5,    39,     0,    96,    15,    40,
      41,     6,     0,     0,     0,     0,     0,     0,     4,     0,
       0,     0,    42,     0,     5,    39,    43,   128,    15,    40,
      41,     6,     0,     7,    45,     0,     0,     0,     4,     0,
       0,     0,    42,     0,     5,    39,    43,   129,    15,    40,
      41,     6,     0,     7,    45,     0,     0,     0,     4,     0,
       0,     0,    42,     0,     5,    39,    43,   136,    15,    40,
      41,     6,     0,     7,    45,     0,     0,     0,    85,     0,
       0,     0,    42,    86,     0,    87,    43,   137,     0,    88,
      89,     0,     0,     7,    45,     4,     0,    90,    91,     0,
      92,     5,     0,    93,     0,    15,    95,    41,     6,     0,
       0,    86,     0,    87,    96,     0,     0,    88,    89,    42,
       0,     0,     0,    43,     0,    90,    91,     0,    92,     0,
       7,    93,     0,    86,    95,    -1,     0,     0,     0,    -1,
      -1,     0,    96,     0,     0,     0,    57,    -1,    -1,     0,
      92,    15,     0,    -1,     0,    58,    95,     0,     0,    59,
      60,    61,    62,    57,    96,     0,     0,     0,    15,     0,
       0,    99,    58,    63,     0,    64,    59,    60,    61,    62,
      57,     0,     0,     0,     0,    15,     0,     0,     0,    58,
      63,     0,    64,    59,     0,    61,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    63,     0,    64
  };

  const short
  Parser::yycheck_[] =
  {
       9,    36,    38,    54,    36,     7,     0,     6,    24,    37,
      16,     6,     8,    12,    24,     4,    25,    12,    53,    54,
      19,    53,    54,     6,    19,     4,     7,    36,     3,    12,
      21,     7,    41,     8,    36,    10,    19,    36,    47,    14,
      15,    36,    41,    39,    53,    54,    41,    22,    23,     2,
      25,    60,    21,    28,    29,    36,    31,     5,    41,    12,
      36,    36,    24,    24,    39,    24,    37,    20,    21,    22,
      37,    21,    24,   124,    21,     9,    24,    30,    36,     5,
      33,    21,    21,     2,    33,   121,   122,    60,    -1,   124,
     125,   126,   124,   125,   126,    -1,   132,   133,    24,   134,
     135,    -1,   134,   135,    -1,    -1,    32,    33,    43,    -1,
      -1,    -1,    -1,    -1,    -1,   124,   125,   126,    -1,    -1,
      55,    -1,    -1,    -1,    59,   134,   135,    62,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    71,    -1,    -1,    74,
      75,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    -1,    -1,    -1,     3,    -1,   102,    -1,    -1,
       8,    -1,    10,    -1,    -1,    -1,    14,    15,    -1,    -1,
      -1,    -1,    -1,   118,    22,    23,    -1,    25,    -1,    -1,
      28,    29,     3,    31,    -1,    -1,    -1,     8,    36,    10,
      -1,    39,    -1,    14,    15,    -1,    -1,    -1,    -1,    -1,
      -1,    22,    23,    -1,    25,    -1,    -1,    28,    29,     3,
      31,    -1,    -1,    -1,     8,    36,    10,    -1,    39,    -1,
      14,    15,    -1,    -1,    -1,    -1,    -1,    -1,    22,    23,
      -1,    25,    -1,    -1,    28,    29,    -1,    31,    -1,    -1,
       6,    -1,    -1,    37,    -1,    39,    12,    13,    -1,     6,
      16,    17,    18,    19,    -1,    12,    13,    -1,    -1,    16,
      17,    18,    19,    -1,    30,    -1,    -1,    -1,    34,    35,
      -1,    -1,    -1,    30,    -1,    41,    42,    34,    35,    -1,
      -1,     3,    -1,    -1,    41,    42,     8,    -1,    10,    -1,
      -1,    -1,    14,    15,    -1,    -1,    -1,    -1,    -1,    -1,
      22,    23,    -1,    25,    -1,    -1,    28,    29,     6,    31,
      -1,    -1,    -1,    -1,    12,    13,    -1,    39,    16,    17,
      18,    19,    -1,    -1,    -1,    -1,    -1,    -1,     6,    -1,
      -1,    -1,    30,    -1,    12,    13,    34,    35,    16,    17,
      18,    19,    -1,    41,    42,    -1,    -1,    -1,     6,    -1,
      -1,    -1,    30,    -1,    12,    13,    34,    35,    16,    17,
      18,    19,    -1,    41,    42,    -1,    -1,    -1,     6,    -1,
      -1,    -1,    30,    -1,    12,    13,    34,    35,    16,    17,
      18,    19,    -1,    41,    42,    -1,    -1,    -1,     3,    -1,
      -1,    -1,    30,     8,    -1,    10,    34,    35,    -1,    14,
      15,    -1,    -1,    41,    42,     6,    -1,    22,    23,    -1,
      25,    12,    -1,    28,    -1,    16,    31,    18,    19,    -1,
      -1,     8,    -1,    10,    39,    -1,    -1,    14,    15,    30,
      -1,    -1,    -1,    34,    -1,    22,    23,    -1,    25,    -1,
      41,    28,    -1,     8,    31,    10,    -1,    -1,    -1,    14,
      15,    -1,    39,    -1,    -1,    -1,    11,    22,    23,    -1,
      25,    16,    -1,    28,    -1,    20,    31,    -1,    -1,    24,
      25,    26,    27,    11,    39,    -1,    -1,    -1,    16,    -1,
      -1,    36,    20,    38,    -1,    40,    24,    25,    26,    27,
      11,    -1,    -1,    -1,    -1,    16,    -1,    -1,    -1,    20,
      38,    -1,    40,    24,    -1,    26,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    38,    -1,    40
  };

  const signed char
  Parser::yystos_[] =
  {
       0,    44,    45,     0,     6,    12,    19,    41,    46,    47,
      48,    51,    24,    49,    37,    16,    62,    36,    47,    50,
      24,     4,     7,    36,    36,    47,    52,    53,    47,    47,
       4,    21,    62,     7,    36,    47,    54,    53,    21,    13,
      17,    18,    30,    34,    35,    42,    46,    47,    55,    56,
      58,    59,    62,    54,    24,    24,    62,    11,    20,    24,
      25,    26,    27,    38,    40,    57,    58,    59,    61,    62,
      57,    24,    62,    37,     5,    24,    32,    33,    35,    56,
      57,    57,    61,    62,    57,     3,     8,    10,    14,    15,
      22,    23,    25,    28,    29,    31,    39,    57,    57,    36,
      57,    60,    37,    36,    36,    57,    57,    57,    57,    57,
      57,    57,    57,    57,    57,    57,    57,    36,     7,    36,
      57,    21,    21,    57,    37,    54,    54,    56,    35,    35,
      36,     9,    21,    21,    54,    54,    35,    35
  };

  const signed char
  Parser::yyr1_[] =
  {
       0,    43,    44,    45,    45,    45,    46,    47,    47,    48,
      48,    48,    49,    49,    50,    50,    51,    51,    52,    52,
      53,    54,    54,    54,    55,    55,    55,    55,    56,    56,
      56,    56,    56,    56,    56,    56,    56,    57,    57,    57,
      57,    57,    57,    57,    57,    57,    57,    57,    57,    57,
      57,    57,    57,    58,    59,    59,    60,    60,    61,    61,
      61,    61,    61,    61,    61,    61,    62
  };

  const signed char
  Parser::yyr2_[] =
  {
       0,     2,     1,     3,     2,     0,     2,     1,     2,     1,
       1,     1,     5,     4,     1,     3,     7,     8,     1,     3,
       2,     0,     3,     2,     7,    11,     7,    11,     1,     1,
       2,     2,     2,     2,     2,     1,     1,     1,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       2,     2,     1,     3,     3,     4,     1,     3,     1,     1,
       1,     1,     1,     3,     1,     1,     1
  };


#if YYDEBUG || 1
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a YYNTOKENS, nonterminals.
  const char*
  const Parser::yytname_[] =
  {
  "\"end file\"", "error", "\"invalid token\"", "AND", "ARROW", "ASSIGN",
  "BOOL", "COMMA", "DIVIDE", "ELSE", "EQUALS", "FALSE", "FN", "FOR",
  "GREATER", "GREATEREQ", "ID", "IF", "INPUT", "INT", "INTLITERAL",
  "LCURLY", "LESS", "LESSEQ", "LPAREN", "MINUS", "MAYHEM", "NOT",
  "NOTEQUALS", "OR", "OUTPUT", "PLUS", "POSTDEC", "POSTINC", "RETURN",
  "RCURLY", "RPAREN", "SEMICOL", "STRINGLITERAL", "TIMES", "TRUE", "VOID",
  "WHILE", "$accept", "program", "globals", "varDecl", "type", "primType",
  "fnType", "typeList", "fnDecl", "formals", "formalDecl", "stmtList",
  "blockStmt", "stmt", "exp", "assignExp", "callExp", "actualsList",
  "term", "id", YY_NULLPTR
  };
#endif


#if YYDEBUG
  const short
  Parser::yyrline_[] =
  {
       0,   157,   157,   163,   169,   177,   181,   187,   191,   196,
     200,   204,   209,   214,   221,   226,   233,   239,   245,   250,
     256,   263,   266,   271,   277,   282,   287,   292,   298,   303,
     307,   312,   317,   322,   327,   332,   336,   341,   343,   348,
     353,   358,   363,   368,   373,   378,   383,   388,   393,   398,
     403,   408,   413,   416,   422,   429,   435,   442,   448,   450,
     452,   454,   456,   458,   460,   462,   465
  };

  void
  Parser::yy_stack_print_ () const
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << int (i->state);
    *yycdebug_ << '\n';
  }

  void
  Parser::yy_reduce_print_ (int yyrule) const
  {
    int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):\n";
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG

  Parser::symbol_kind_type
  Parser::yytranslate_ (int t) YY_NOEXCEPT
  {
    // YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to
    // TOKEN-NUM as returned by yylex.
    static
    const signed char
    translate_table[] =
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
      35,    36,    37,    38,    39,    40,    41,    42
    };
    // Last valid token kind.
    const int code_max = 297;

    if (t <= 0)
      return symbol_kind::S_YYEOF;
    else if (t <= code_max)
      return static_cast <symbol_kind_type> (translate_table[t]);
    else
      return symbol_kind::S_YYUNDEF;
  }

#line 5 "drewgon.yy"
} // drewgon
#line 1823 "parser.cc"

#line 471 "drewgon.yy"


void drewgon::Parser::error(const std::string& msg){
	std::cout << msg << std::endl;
	std::cerr << "syntax error" << std::endl;
}
