#ifndef DREWGON_AST_HPP
#define DREWGON_AST_HPP

#include <ostream>
#include <sstream>
#include <string.h>
#include <list>
#include "tokens.hpp"
#include "types.hpp"
#include "3ac.hpp"

namespace drewgon {

class TypeAnalysis;

class Opd;

class SymbolTable;
class SemSymbol;

class DeclNode;
class VarDeclNode;
class StmtNode;
class AssignExpNode;
class FormalDeclNode;
class TypeNode;
class ExpNode;
class IDNode;

class ASTNode{
public:
	ASTNode(const Position * pos) : myPos(pos){ }
	virtual void unparse(std::ostream&, int) = 0;
	const Position * pos() { return myPos; };
	std::string posStr(){ return pos()->span(); }
	virtual bool nameAnalysis(SymbolTable *) = 0;
	//Note that there is no ASTNode::typeAnalysis. To allow
	// for different type signatures, type analysis is
	// implemented as needed in various subclasses
protected:
	const Position * myPos = nullptr;
};

class ProgramNode : public ASTNode{
public:
	ProgramNode(std::list<DeclNode *> * globalsIn);
	void unparse(std::ostream&, int) override;
	virtual bool nameAnalysis(SymbolTable *) override;
	virtual void typeAnalysis(TypeAnalysis *);
	IRProgram * to3AC(TypeAnalysis * ta);
	virtual ~ProgramNode(){ }
private:
	std::list<DeclNode *> * myGlobals;
};

class ExpNode : public ASTNode{
protected:
	ExpNode(const Position * p) : ASTNode(p){ }
public:
	virtual void unparseNested(std::ostream& out);
	//virtual void unparse(std::ostream& out, int indent) override = 0;
	virtual bool nameAnalysis(SymbolTable * symTab) override = 0;
	virtual void typeAnalysis(TypeAnalysis *) = 0;
	virtual Opd * flatten(Procedure * proc) = 0;
};

class IDNode : public ExpNode{
public:
	IDNode(const Position * p, std::string nameIn)
	: ExpNode(p), name(nameIn), mySymbol(nullptr){}
	std::string getName(){ return name; }
	void unparse(std::ostream& out, int indent) override;
	void unparseNested(std::ostream& out) override;
	void attachSymbol(SemSymbol * symbolIn);
	SemSymbol * getSymbol() const { return mySymbol; }
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
private:
	std::string name;
	SemSymbol * mySymbol;
};

class TypeNode : public ASTNode{
public:
	TypeNode(const Position * p) : ASTNode(p){ }
	void unparse(std::ostream&, int) override = 0;
	virtual const DataType * getType() const = 0;
	virtual bool nameAnalysis(SymbolTable *) override;
	virtual void typeAnalysis(TypeAnalysis *);
};

class StmtNode : public ASTNode{
public:
	StmtNode(const Position * p) : ASTNode(p){ }
	virtual void unparse(std::ostream& out, int indent) override = 0;
	virtual void typeAnalysis(TypeAnalysis *) = 0;
	virtual void to3AC(Procedure * proc) = 0;
};

class DeclNode : public StmtNode{
public:
	DeclNode(const Position * p) : StmtNode(p){ }
	void unparse(std::ostream& out, int indent) override =0;
	virtual void typeAnalysis(TypeAnalysis *) override = 0;
	virtual void to3AC(IRProgram * prog) = 0;
	virtual void to3AC(Procedure * proc) override = 0;
};

class VarDeclNode : public DeclNode{
public:
	VarDeclNode(const Position * p, TypeNode * typeIn, IDNode * IDIn)
	: DeclNode(p), myType(typeIn), myID(IDIn){ }
	void unparse(std::ostream& out, int indent) override;
	IDNode * ID(){ return myID; }
	TypeNode * getTypeNode() const{ return myType; }
	bool nameAnalysis(SymbolTable * symTab) override;
	void typeAnalysis(TypeAnalysis * typing) override;
	virtual void to3AC(Procedure * proc) override;
	virtual void to3AC(IRProgram * prog) override;
private:
	TypeNode * myType;
	IDNode * myID;
};

class FormalDeclNode : public VarDeclNode{
public:
	FormalDeclNode(const Position * p, TypeNode * type, IDNode * id)
	: VarDeclNode(p, type, id){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void to3AC(Procedure * proc) override;
	virtual void to3AC(IRProgram * prog) override;
};

class FnDeclNode : public DeclNode{
public:
	FnDeclNode(const Position * p,
	  TypeNode * retTypeIn, IDNode * idIn,
	  std::list<FormalDeclNode *> * formalsIn,
	  std::list<StmtNode *> * bodyIn)
	: DeclNode(p), myRetType(retTypeIn), myID(idIn),
	  myFormals(formalsIn), myBody(bodyIn){
	}
	IDNode * ID() const { return myID; }
	std::list<FormalDeclNode *> * getFormals() const{
		return myFormals;
	}
	virtual TypeNode * getRetTypeNode() {
		return myRetType;
	}
	void unparse(std::ostream& out, int indent) override;
	virtual bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	void to3AC(IRProgram * prog) override;
	void to3AC(Procedure * prog) override;
private:
	TypeNode * myRetType;
	IDNode * myID;
	std::list<FormalDeclNode *> * myFormals;
	std::list<StmtNode *> * myBody;
};

class AssignStmtNode : public StmtNode{
public:
	AssignStmtNode(const Position * p, AssignExpNode * expIn)
	: StmtNode(p), myExp(expIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	AssignExpNode * myExp;
};

class InputStmtNode : public StmtNode{
public:
	InputStmtNode(const Position * p, IDNode * dstIn)
	: StmtNode(p), myDst(dstIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	IDNode * myDst;
};

class OutputStmtNode : public StmtNode{
public:
	OutputStmtNode(const Position * p, ExpNode * srcIn)
	: StmtNode(p), mySrc(srcIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	ExpNode * mySrc;
};

class PostDecStmtNode : public StmtNode{
public:
	PostDecStmtNode(const Position * p, IDNode * inID)
	: StmtNode(p), myID(inID){ }
	void unparse(std::ostream& out, int indent) override;
	virtual bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	IDNode * myID;
};

class PostIncStmtNode : public StmtNode{
public:
	PostIncStmtNode(const Position * p, IDNode * inID)
	: StmtNode(p), myID(inID){ }
	void unparse(std::ostream& out, int indent) override;
	virtual bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	IDNode * myID;
};

class IfStmtNode : public StmtNode{
public:
	IfStmtNode(const Position * p, ExpNode * condIn,
	  std::list<StmtNode *> * bodyIn)
	: StmtNode(p), myCond(condIn), myBody(bodyIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	ExpNode * myCond;
	std::list<StmtNode *> * myBody;
};

class IfElseStmtNode : public StmtNode{
public:
	IfElseStmtNode(const Position * p, ExpNode * condIn,
	  std::list<StmtNode *> * bodyTrueIn,
	  std::list<StmtNode *> * bodyFalseIn)
	: StmtNode(p), myCond(condIn),
	  myBodyTrue(bodyTrueIn), myBodyFalse(bodyFalseIn) { }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	ExpNode * myCond;
	std::list<StmtNode *> * myBodyTrue;
	std::list<StmtNode *> * myBodyFalse;
};

class WhileStmtNode : public StmtNode{
public:
	WhileStmtNode(const Position * p, ExpNode * condIn,
	  std::list<StmtNode *> * bodyIn)
	: StmtNode(p), myCond(condIn), myBody(bodyIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	ExpNode * myCond;
	std::list<StmtNode *> * myBody;
};

class ForStmtNode : public StmtNode{
public:
	ForStmtNode(const Position * p, StmtNode * init, ExpNode * condIn, 
	  StmtNode * itrIn, std::list<StmtNode *> * bodyIn)
	: StmtNode(p), myInit(init), myCond(condIn), myItr(itrIn),
	  myBody(bodyIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * prog) override;
private:
	StmtNode * myInit;
	ExpNode * myCond;
	StmtNode * myItr;
	std::list<StmtNode *> * myBody;
};

class ReturnStmtNode : public StmtNode{
public:
	ReturnStmtNode(const Position * p, ExpNode * exp)
	: StmtNode(p), myExp(exp){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * proc) override;
private:
	ExpNode * myExp;
};

class CallExpNode : public ExpNode{
public:
	CallExpNode(const Position * p, IDNode * id,
	  std::list<ExpNode *> * argsIn)
	: ExpNode(p), myID(id), myArgs(argsIn){ }
	void unparse(std::ostream& out, int indent) override;
	void unparseNested(std::ostream& out) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	void typeAnalysis(TypeAnalysis *) override;
	DataType * getRetType();

	virtual Opd * flatten(Procedure * proc) override;
private:
	IDNode * myID;
	std::list<ExpNode *> * myArgs;
};

class BinaryExpNode : public ExpNode{
public:
	BinaryExpNode(const Position * p, ExpNode * lhs, ExpNode * rhs)
	: ExpNode(p), myExp1(lhs), myExp2(rhs) { }
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override = 0;
	virtual Opd * flatten(Procedure * prog) override = 0;
protected:
	ExpNode * myExp1;
	ExpNode * myExp2;
	void binaryLogicTyping(TypeAnalysis * typing);
	void binaryEqTyping(TypeAnalysis * typing);
	void binaryRelTyping(TypeAnalysis * typing);
	void binaryMathTyping(TypeAnalysis * typing);
};

class PlusNode : public BinaryExpNode{
public:
	PlusNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class MinusNode : public BinaryExpNode{
public:
	MinusNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class TimesNode : public BinaryExpNode{
public:
	TimesNode(const Position * p, ExpNode * e1In, ExpNode * e2In)
	: BinaryExpNode(p, e1In, e2In){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class DivideNode : public BinaryExpNode{
public:
	DivideNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class AndNode : public BinaryExpNode{
public:
	AndNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class OrNode : public BinaryExpNode{
public:
	OrNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class EqualsNode : public BinaryExpNode{
public:
	EqualsNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class NotEqualsNode : public BinaryExpNode{
public:
	NotEqualsNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class LessNode : public BinaryExpNode{
public:
	LessNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
};

class LessEqNode : public BinaryExpNode{
public:
	LessEqNode(const Position * pos, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(pos, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class GreaterNode : public BinaryExpNode{
public:
	GreaterNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
};

class GreaterEqNode : public BinaryExpNode{
public:
	GreaterEqNode(const Position * p, ExpNode * e1, ExpNode * e2)
	: BinaryExpNode(p, e1, e2){ }
	void unparse(std::ostream& out, int indent) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class UnaryExpNode : public ExpNode {
public:
	UnaryExpNode(const Position * p, ExpNode * expIn)
	: ExpNode(p){
		this->myExp = expIn;
	}
	virtual void unparse(std::ostream& out, int indent) override = 0;
	virtual bool nameAnalysis(SymbolTable * symTab) override = 0;
	virtual void typeAnalysis(TypeAnalysis *) override = 0;
	virtual Opd * flatten(Procedure * prog) override = 0;
protected:
	ExpNode * myExp;
};

class NegNode : public UnaryExpNode{
public:
	NegNode(const Position * p, ExpNode * exp)
	: UnaryExpNode(p, exp){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class NotNode : public UnaryExpNode{
public:
	NotNode(const Position * p, ExpNode * exp)
	: UnaryExpNode(p, exp){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class VoidTypeNode : public TypeNode{
public:
	VoidTypeNode(const Position * p) : TypeNode(p){}
	void unparse(std::ostream& out, int indent) override;
	virtual const DataType * getType() const override {
		return BasicType::VOID();
	}
};

class IntTypeNode : public TypeNode{
public:
	IntTypeNode(const Position * p): TypeNode(p){}
	void unparse(std::ostream& out, int indent) override;
	virtual const DataType * getType() const override;
};

class FnTypeNode : public TypeNode{
public:
	FnTypeNode(const Position * p, std::list<TypeNode *> * inTypes, TypeNode * outType)
	: TypeNode(p), myInTypes(inTypes), myOutType(outType){}
	void unparse(std::ostream& out, int indent) override;
	virtual const DataType * getType() const override;
	virtual bool nameAnalysis(SymbolTable * symTab) override;
private:
	const std::list<TypeNode *> * myInTypes;
	TypeNode * myOutType;
};

class BoolTypeNode : public TypeNode{
public:
	BoolTypeNode(const Position * p): TypeNode(p) { }
	void unparse(std::ostream& out, int indent) override;
	virtual const DataType * getType() const override;
};

class AssignExpNode : public ExpNode{
public:
	AssignExpNode(const Position * p, IDNode * inDst, ExpNode * inSrc)
	: ExpNode(p), myDst(inDst), mySrc(inSrc){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
private:
	IDNode * myDst;
	ExpNode * mySrc;
};

class IntLitNode : public ExpNode{
public:
	IntLitNode(const Position * p, const int numIn)
	: ExpNode(p), myNum(numIn){ }
	virtual void unparseNested(std::ostream& out) override{
		unparse(out, 0);
	}
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
private:
	const int myNum;
};

class StrLitNode : public ExpNode{
public:
	StrLitNode(const Position * p, const std::string strIn)
	: ExpNode(p), myStr(strIn){ }
	virtual void unparseNested(std::ostream& out) override{
		unparse(out, 0);
	}
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable *) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
private:
	 const std::string myStr;
};

class MayhemNode : public ExpNode{
public:
	MayhemNode(const Position * p): ExpNode(p){ }
	virtual void unparseNested(std::ostream& out) override{
		unparse(out, 0);
	}
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * proc) override;
};


class TrueNode : public ExpNode{
public:
	TrueNode(const Position * p): ExpNode(p){ }
	virtual void unparseNested(std::ostream& out) override{
		unparse(out, 0);
	}
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class FalseNode : public ExpNode{
public:
	FalseNode(const Position * p): ExpNode(p){ }
	virtual void unparseNested(std::ostream& out) override{
		unparse(out, 0);
	}
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual Opd * flatten(Procedure * prog) override;
};

class CallStmtNode : public StmtNode{
public:
	CallStmtNode(const Position * p, CallExpNode * expIn)
	: StmtNode(p), myCallExp(expIn){ }
	void unparse(std::ostream& out, int indent) override;
	bool nameAnalysis(SymbolTable * symTab) override;
	virtual void typeAnalysis(TypeAnalysis *) override;
	virtual void to3AC(Procedure * proc) override;
private:
	CallExpNode * myCallExp;
};

} //End namespace drewgon

#endif

