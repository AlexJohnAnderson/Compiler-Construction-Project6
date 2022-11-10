%skeleton "lalr1.cc"
%require "3.0"
%debug
%defines
%define api.namespace{drewgon}
%define api.parser.class {Parser}
%define parse.error verbose
%output "parser.cc"
%token-table

%code requires{
	#include <list>
	#include "tokens.hpp"
	#include "ast.hpp"
	namespace drewgon {
		class Scanner;
	}

//The following definition is required when
// we don't have the %locations directive
# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

//End "requires" code
}

%parse-param { drewgon::Scanner &scanner }
%parse-param { drewgon::ProgramNode** root }
%code{
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
}

%union {
   bool                                  transBool;
   drewgon::Token*                         transToken;
   drewgon::Token*                         lexeme;
   drewgon::IDToken*                       transIDToken;
   drewgon::IntLitToken*                   transIntToken;
   drewgon::IntLitToken*                   transShortToken;
   drewgon::StrToken*                      transStrToken;
   drewgon::ProgramNode*                   transProgram;
   drewgon::DeclNode *                     transDecl;
   std::list<drewgon::DeclNode *> *        transDeclList;
   drewgon::VarDeclNode *                  transVarDecl;
   std::list<drewgon::TypeNode *> *        transTypeList;
   drewgon::FnTypeNode *                   transFnType;
   std::list<drewgon::VarDeclNode *> *     transVarDeclList;
   drewgon::FormalDeclNode *               transFormal;
   std::list<drewgon::FormalDeclNode *> *  transFormalList;
   drewgon::TypeNode *                     transType;
   drewgon::IDNode *                       transID;
   drewgon::FnDeclNode *                   transFn;
   std::list<drewgon::VarDeclNode *> *     transVarDecls;
   std::list<drewgon::StmtNode *> *        transStmts;
   drewgon::StmtNode *                     transStmt;
   drewgon::ExpNode *                      transExp;
   drewgon::AssignExpNode *                transAssignExp;
   drewgon::CallExpNode *                  transCallExp;
   std::list<drewgon::ExpNode *> *         transActuals;
}

%define parse.assert

%token                   END	   0 "end file"
%token	<transToken>     AND
%token	<transToken>     ARROW
%token	<transToken>     ASSIGN
%token	<transToken>     BOOL
%token	<transToken>     COMMA
%token	<transToken>     DIVIDE
%token	<transToken>     ELSE
%token	<transToken>     EQUALS
%token	<transToken>     FALSE
%token	<transToken>     FN
%token	<transToken>     FOR
%token	<transToken>     GREATER
%token	<transToken>     GREATEREQ
%token	<transIDToken>   ID
%token	<transToken>     IF
%token	<transToken>     INPUT
%token	<transToken>     INT
%token	<transIntToken>  INTLITERAL
%token	<transToken>     LCURLY
%token	<transToken>     LESS
%token	<transToken>     LESSEQ
%token	<transToken>     LPAREN
%token	<transToken>     MINUS
%token	<transToken>     MAYHEM
%token	<transToken>     NOT
%token	<transToken>     NOTEQUALS
%token	<transToken>     OR
%token	<transToken>     OUTPUT
%token	<transToken>     PLUS
%token	<transToken>     POSTDEC
%token	<transToken>     POSTINC
%token	<transToken>     RETURN
%token	<transToken>     RCURLY
%token	<transToken>     RPAREN
%token	<transToken>     SEMICOL
%token	<transStrToken>  STRINGLITERAL
%token	<transToken>     TIMES
%token	<transToken>     TRUE
%token	<transToken>     VOID
%token	<transToken>     WHILE

%type <transProgram> program
%type <transDeclList> globals
%type <transVarDecl> varDecl
%type <transFn> fnDecl
%type <transExp> term
%type <transExp> exp
%type <transActuals> actualsList
%type <transCallExp> callExp
%type <transAssignExp> assignExp
%type <transID> id
%type <transStmt> stmt
%type <transStmt> blockStmt
%type <transStmts> stmtList
%type <transType> type
%type <transFnType> fnType
%type <transTypeList> typeList
%type <transFormal> formalDecl
%type <transFormalList> formals
%type <transType> primType

/* NOTE: Make sure to add precedence and associativity
 * declarations
 */
%right ASSIGN
%left OR
%left AND
%nonassoc LESS GREATER LESSEQ GREATEREQ EQUALS NOTEQUALS
%left MINUS PLUS
%left TIMES DIVIDE
%left NOT

%%

program 	: globals
		  {
		  $$ = new ProgramNode($1);
		  *root = $$;
		  }

globals 	: globals varDecl SEMICOL
	  	  {
	  	  $$ = $1;
	  	  DeclNode * declNode = $2;
		  $$->push_back(declNode);
	  	  }
		| globals fnDecl
		  {
	  	  $$ = $1;
	  	  DeclNode * declNode = $2;
		  $$->push_back(declNode);
		  }

		| /* epsilon */
		  {
		  $$ = new std::list<DeclNode * >();
		  }

varDecl 	: type id
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new VarDeclNode(p, $1, $2);
		  }

type		: primType
		  {
		  $$ = $1;
		  }
		| FN fnType
		  {
		  $$ = $2;
		  }

primType 	: INT
	  	  {
		  $$ = new IntTypeNode($1->pos());
		  }
		| BOOL
		  {
		  $$ = new BoolTypeNode($1->pos());
		  }
		| VOID
		  {
		  $$ = new VoidTypeNode($1->pos());
		  }

fnType		: LPAREN typeList RPAREN ARROW type
		  {
		  const Position * pos = new Position($1->pos(), $5->pos());
		  $$ = new FnTypeNode(pos, $2, $5);
		  }
		| LPAREN RPAREN ARROW type
		  {
		  const Position * pos = new Position($1->pos(), $4->pos());
		  std::list<TypeNode *> * n = new std::list<TypeNode *>();
		  $$ = new FnTypeNode(pos,n,$4);
		  }

typeList	: type
		  {
		  $$ = new std::list<TypeNode *>();
		  $$->push_back($1);
		  }
		| typeList COMMA type
		  {
		  $$ = $1;
		  $$->push_back($3);
		  }


fnDecl 		: type id LPAREN RPAREN LCURLY stmtList RCURLY
		  {
		  const Position * pos = new Position($1->pos(), $7->pos());
		  std::list<FormalDeclNode *> * f = new std::list<FormalDeclNode *>();
		  $$ = new FnDeclNode(pos, $1, $2, f, $6);
		  }
		| type id LPAREN formals RPAREN LCURLY stmtList RCURLY
		  {
		  const Position * pos = new Position($1->pos(), $8->pos());
		  $$ = new FnDeclNode(pos, $1, $2, $4, $7);
		  }

formals 	: formalDecl
		  {
		  $$ = new std::list<FormalDeclNode *>();
		  $$->push_back($1);
		  }
		| formals COMMA formalDecl
		  {
		  $$ = $1;
		  $$->push_back($3);
		  }

formalDecl 	: type id
		  {
		  const Position * pos = new Position($1->pos(), $2->pos());
		  $$ = new FormalDeclNode(pos, $1, $2);
		  }

stmtList 	: /* epsilon */
	   	  {
		  $$ = new std::list<StmtNode *>();
	   	  }
		| stmtList stmt SEMICOL
	  	  {
		  $$ = $1;
		  $$->push_back($2);
	  	  }
		| stmtList blockStmt
	  	  {
		  $$ = $1;
		  $$->push_back($2);
	  	  }

blockStmt	: WHILE LPAREN exp RPAREN LCURLY stmtList RCURLY
		  {
		  const Position * p = new Position($1->pos(), $7->pos());
		  $$ = new WhileStmtNode(p, $3, $6);
		  }
		| FOR LPAREN stmt SEMICOL exp SEMICOL stmt RPAREN LCURLY stmtList RCURLY
		  {
		  const Position * p = new Position($1->pos(), $11->pos());
		  $$ = new ForStmtNode(p, $3, $5, $7, $10);
		  }
		| IF LPAREN exp RPAREN LCURLY stmtList RCURLY
		  {
		  const Position * p = new Position($1->pos(), $7->pos());
		  $$ = new IfStmtNode(p, $3, $6);
		  }
		| IF LPAREN exp RPAREN LCURLY stmtList RCURLY ELSE LCURLY stmtList RCURLY
		  {
		  const Position * p = new Position($1->pos(), $11->pos());
		  $$ = new IfElseStmtNode(p, $3, $6, $10);
		  }

stmt		: varDecl
		  {
		  const Position * p = $1->pos();
		  $$ = new VarDeclNode(p, $1->getTypeNode(), $1->ID());
		  }
		| assignExp
		  {
		  $$ = new AssignStmtNode($1->pos(), $1);
		  }
		| id POSTDEC
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new PostDecStmtNode(p, $1);
		  }
		| id POSTINC
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new PostIncStmtNode(p, $1);
		  }
		| INPUT id
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new InputStmtNode(p, $2);
		  }
		| OUTPUT exp
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new OutputStmtNode(p, $2);
		  }
		| RETURN exp
		  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new ReturnStmtNode(p, $2);
		  }
		| RETURN
		  {
		  $$ = new ReturnStmtNode($1->pos(), nullptr);
		  }
		| callExp
		  {
		  $$ = new CallStmtNode($1->pos(), $1);
		  }

exp		: assignExp
		  { $$ = $1; }
		| exp MINUS exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new MinusNode(p, $1, $3);
		  }
		| exp PLUS exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new PlusNode(p, $1, $3);
		  }
		| exp TIMES exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new TimesNode(p, $1, $3);
		  }
		| exp DIVIDE exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new DivideNode(p, $1, $3);
		  }
		| exp AND exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new AndNode(p, $1, $3);
		  }
		| exp OR exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new OrNode(p, $1, $3);
		  }
		| exp EQUALS exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new EqualsNode(p, $1, $3);
		  }
		| exp NOTEQUALS exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new NotEqualsNode(p, $1, $3);
		  }
		| exp GREATER exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new GreaterNode(p, $1, $3);
		  }
		| exp GREATEREQ exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new GreaterEqNode(p, $1, $3);
		  }
		| exp LESS exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new LessNode(p, $1, $3);
		  }
		| exp LESSEQ exp
	  	  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new LessEqNode(p, $1, $3);
		  }
		| NOT exp
	  	  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new NotNode(p, $2);
		  }
		| MINUS term
	  	  {
		  const Position * p = new Position($1->pos(), $2->pos());
		  $$ = new NegNode(p, $2);
		  }
		| term
	  	  { $$ = $1; }

assignExp	: id ASSIGN exp
		  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  $$ = new AssignExpNode(p, $1, $3);
		  }

callExp		: id LPAREN RPAREN
		  {
		  const Position * p = new Position($1->pos(), $3->pos());
		  std::list<ExpNode *> * noargs =
		    new std::list<ExpNode *>();
		  $$ = new CallExpNode(p, $1, noargs);
		  }
		| id LPAREN actualsList RPAREN
		  {
		  const Position * p = new Position($1->pos(), $4->pos());
		  $$ = new CallExpNode(p, $1, $3);
		  }

actualsList	: exp
		  {
		  std::list<ExpNode *> * list =
		    new std::list<ExpNode *>();
		  list->push_back($1);
		  $$ = list;
		  }
		| actualsList COMMA exp
		  {
		  $$ = $1;
		  $$->push_back($3);
		  }

term 		: id
		  { $$ = $1; }
		| INTLITERAL
		  { $$ = new IntLitNode($1->pos(), $1->num()); }
		| STRINGLITERAL
		  { $$ = new StrLitNode($1->pos(), $1->str()); }
		| TRUE
		  { $$ = new TrueNode($1->pos()); }
		| FALSE
		  { $$ = new FalseNode($1->pos()); }
		| LPAREN exp RPAREN
		  { $$ = $2; }
		| MAYHEM
		  { $$ = new MayhemNode($1->pos()); }
		| callExp
		  { $$ = $1; }

id		: ID
		  {
		  const Position * pos = $1->pos();
		  $$ = new IDNode(pos, $1->value());
		  }

%%

void drewgon::Parser::error(const std::string& msg){
	std::cout << msg << std::endl;
	std::cerr << "syntax error" << std::endl;
}
