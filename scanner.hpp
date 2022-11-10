#ifndef __DREWGON_SCANNER_HPP__
#define __DREWGON_SCANNER_HPP__ 1

#if ! defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

#include "grammar.hh"
#include "errors.hpp"

using TokenKind = drewgon::Parser::token;

namespace drewgon{

class Scanner : public yyFlexLexer{
public:

   Scanner(std::istream *in) : yyFlexLexer(in)
   {
	lineNum = 1;
	colNum = 1;
   };
   virtual ~Scanner() {
   };

   //get rid of override virtual function warning
   using FlexLexer::yylex;

   // YY_DECL defined in the flex drewgon.l
   virtual int yylex( drewgon::Parser::semantic_type * const lval);

   int makeBareToken(int tagIn){
	size_t len = static_cast<size_t>(yyleng);
	Position * pos = new Position(
	  this->lineNum, this->colNum,
	  this->lineNum, this->colNum+len);
        this->yylval->lexeme = new Token(pos, tagIn);
        colNum += len;
        return tagIn;
   }

   void errIllegal(Position * pos, std::string match){
	drewgon::Report::fatal(pos,
	"Illegal character " + match);
   }

   void errStrEsc(Position * pos){
	drewgon::Report::fatal(pos,
	"String literal with bad escape sequence detected");
   }

   void errStrUnterm(Position * pos){
	drewgon::Report::fatal(pos,
	"Unterminated string literal detected");
   }

   void errStrEscAndUnterm(Position * pos){
	drewgon::Report::fatal(pos,
	"Unterminated string literal with bad escape sequence detected");
   }

   void errIntOverflow(Position * pos){
	drewgon::Report::fatal(pos, "Integer literal overflow");
   }

   static std::string tokenKindString(int tokenKind);

   void outputTokens(std::ostream& outstream);

private:
   drewgon::Parser::semantic_type *yylval = nullptr;
   size_t lineNum;
   size_t colNum;
};

} /* end namespace */

#endif /* END __DREWGON_SCANNER_HPP__ */
