#include "ast.hpp"

namespace drewgon{

IRProgram * ProgramNode::to3AC(TypeAnalysis * ta){
	IRProgram * prog = new IRProgram(ta);
	for (auto global : *myGlobals){
		global->to3AC(prog);
	}
	return prog;
}

static void formalsTo3AC(Procedure * proc, 
  std::list<FormalDeclNode *> * myFormals){
	for (auto formal : *myFormals){
		formal->to3AC(proc);
	}
	unsigned int argIdx = 1;
	for (auto formal : *myFormals){
		SemSymbol * sym = formal->ID()->getSymbol();
		SymOpd * opd = proc->getSymOpd(sym);
		Quad * inQuad = new GetArgQuad(argIdx, opd);
		proc->addQuad(inQuad);
		argIdx += 1;
	}
}

void FnDeclNode::to3AC(IRProgram * prog){
	SemSymbol * mySym = this->ID()->getSymbol();
	Procedure * proc = prog->makeProc(mySym->getName());
	//Generate the getin quads
	prog->gatherGlobal(mySym);
	formalsTo3AC(proc, myFormals);

	for (auto stmt : *myBody){
		stmt->to3AC(proc);
	}
}

void FnDeclNode::to3AC(Procedure * proc){
	//This never needs to be implemented,
	// the function only exists because of
	// inheritance needs (A function declaration
	// never occurs within another function)

	throw new InternalError("FnDecl at a local scope");
}

void FormalDeclNode::to3AC(IRProgram * prog){
	//This never needs to be implemented,
	// the function only exists because of
	// inheritance needs (A formal never
	// occurs at global scope)
	throw new InternalError("Formal at a global scope");
}

void FormalDeclNode::to3AC(Procedure * proc){
	SemSymbol * sym = ID()->getSymbol();
	proc->gatherFormal(sym);
}

Opd * MayhemNode::flatten(Procedure * proc){
	Opd * retVal = proc->makeTmp(8);
	Quad * may = new MayhemQuad(retVal);
	proc->addQuad(may);
	return retVal;
}

Opd * IntLitNode::flatten(Procedure * proc){
	const DataType * type = proc->getProg()->nodeType(this);
	return new LitOpd(std::to_string(myNum), 8);
}

Opd * StrLitNode::flatten(Procedure * proc){
	Opd * res = proc->getProg()->makeString(myStr);
	return res;
}

Opd * TrueNode::flatten(Procedure * proc){
	Opd * res = new LitOpd("1", 8);
	return res;
}

Opd * FalseNode::flatten(Procedure * proc){
	Opd * res = new LitOpd("0", 8);
	return res;
}

Opd * AssignExpNode::flatten(Procedure * proc){
	Opd * op1 = mySrc->flatten(proc);
	Opd * op2 = myDst->flatten(proc);
	if (!op1){
		throw InternalError("null Dst");
	}
	
	AssignQuad * quad = new AssignQuad(op2, op1);
	quad->setComment("Assign");
	proc->addQuad(quad);
	return op1;
}

static void argsTo3AC(Procedure * proc, std::list<ExpNode *> * args){
	std::list<std::pair<Opd *, const DataType *>> argOpds;
	for (auto argNode : *args){
		Opd * argOpd = argNode->flatten(proc);
		const DataType * argType = proc->getProg()->nodeType(argNode);
		argOpds.push_back(std::make_pair(argOpd, argType));
	}
	size_t argIdx = 1;
	for (auto argOpd : argOpds){
		Quad * argQuad = new SetArgQuad(argIdx, argOpd.first);
		proc->addQuad(argQuad);
		argIdx++;
	}
}

Opd * CallExpNode::flatten(Procedure * proc){
	argsTo3AC(proc, myArgs);
	Quad * callQuad = new CallQuad(myID->getSymbol());
	proc->addQuad(callQuad);

	SemSymbol * idSym = myID->getSymbol();
	const FnType * calleeType = idSym->getDataType()->asFn();
	const DataType * retType = calleeType->getReturnType();
	if (retType->isVoid()){
		return nullptr;
	} else {
		Opd * retVal = proc->makeTmp(Opd::width(retType));
		Quad * getRet = new GetRetQuad(retVal);
		proc->addQuad(getRet);
		return retVal;
	}
}

Opd * NegNode::flatten(Procedure * proc){
	Opd * op1 = myExp->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * dst = proc->makeTmp(width);
	UnaryOp opr = UnaryOp::NEG64;
	Quad * quad = new UnaryOpQuad(dst, opr, op1);
	proc->addQuad(quad);
	return dst;
}

Opd * NotNode::flatten(Procedure * proc){
	Opd * op1= myExp->flatten(proc);
	size_t width = proc->getProg()->opWidth(myExp);
	Opd * dst = proc->makeTmp(width);
	Quad * quad = new UnaryOpQuad(dst, NOT8, op1);
	proc->addQuad(quad);
	return dst;
}

Opd * PlusNode::flatten(Procedure * proc){
	Opd * op1 = myExp1->flatten(proc);
	Opd * op2 = myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * dst = proc->makeTmp(width);
	BinOp opr = BinOp::ADD64;
	Quad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * MinusNode::flatten(Procedure * proc){
	Opd * op1 = myExp1->flatten(proc);
	Opd * op2 = myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * dst = proc->makeTmp(width);
	BinOp opr = BinOp::SUB64;
	Quad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * TimesNode::flatten(Procedure * proc){
	Opd * op1 = myExp1->flatten(proc);
	Opd * op2 = myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * dst = proc->makeTmp(width);
	BinOp opr = BinOp::MULT64;
	Quad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * DivideNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * dst = proc->makeTmp(width);
	BinOp opr = BinOp::DIV64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * AndNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * opRes = proc->makeTmp(width);
	BinOpQuad * quad = new BinOpQuad(opRes, AND64, op1, op2);
	proc->addQuad(quad);
	return opRes;
}

Opd * OrNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this);
	Opd * opRes = proc->makeTmp(width);
	BinOpQuad * quad = new BinOpQuad(opRes, OR64, op1, op2);
	proc->addQuad(quad);
	return opRes;
}

Opd * EqualsNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::EQ64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * NotEqualsNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::NEQ64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * LessNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::LT64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * GreaterNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::GT64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * LessEqNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::LTE64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

Opd * GreaterEqNode::flatten(Procedure * proc){
	Opd * op1 = this->myExp1->flatten(proc);
	Opd * op2 = this->myExp2->flatten(proc);
	size_t width = proc->getProg()->opWidth(this->myExp1);
	size_t resWidth = Opd::width(BasicType::BOOL());
	Opd * dst = proc->makeTmp(resWidth);
	BinOp opr = BinOp::GTE64;
	BinOpQuad * quad = new BinOpQuad(dst, opr, op1, op2);
	proc->addQuad(quad);
	return dst;
}

void AssignStmtNode::to3AC(Procedure * proc){
	Opd * res = myExp->flatten(proc);
}

void PostIncStmtNode::to3AC(Procedure * proc){
	Opd * op1 = this->myID->flatten(proc);
	size_t width = proc->getProg()->opWidth(myID);
	BinOp opr = BinOp::ADD64;
	LitOpd * litOpd = new LitOpd("1", width);
	BinOpQuad * quad = new BinOpQuad(op1, opr, op1, litOpd);
	proc->addQuad(quad);
}

void PostDecStmtNode::to3AC(Procedure * proc){
	Opd * op1 = this->myID->flatten(proc);
	size_t width = proc->getProg()->opWidth(myID);
	BinOp opr = BinOp::SUB64;
	LitOpd * litOpd = new LitOpd("1", width);
	BinOpQuad * quad = new BinOpQuad(op1, opr, op1, litOpd);
	proc->addQuad(quad);
}

void OutputStmtNode::to3AC(Procedure * proc){
	Opd * child = this->mySrc->flatten(proc);
	proc->addQuad(new ReportQuad(child,
	proc->getProg()->nodeType(mySrc)));
}

void InputStmtNode::to3AC(Procedure * proc){
	Opd * child = this->myDst->flatten(proc);
	proc->addQuad(new ReceiveQuad(child,
	proc->getProg()->nodeType(myDst)));
}

void IfStmtNode::to3AC(Procedure * proc){
	Opd * myCond = this->myCond->flatten(proc);
	Label * afterLabel = proc->makeLabel();
	Quad * nop = new NopQuad();
	nop->addLabel(afterLabel);

	proc->addQuad(new IfzQuad(myCond, afterLabel));
	for (auto stmt : *myBody){
		stmt->to3AC(proc);
	}
	proc->addQuad(nop);

}

void IfElseStmtNode::to3AC(Procedure * proc){
	Label * elseLabel = proc->makeLabel();
	Quad * elseNop = new NopQuad();
	elseNop->addLabel(elseLabel);
	Label * afterLabel = proc->makeLabel();
	Quad * afterNop = new NopQuad();
	afterNop->addLabel(afterLabel);

	Opd * condition = myCond->flatten(proc);

	Quad * jmpFalse = new IfzQuad(condition, elseLabel);
	proc->addQuad(jmpFalse);
	for (auto stmt : *myBodyTrue){
		stmt->to3AC(proc);
	}
	
	Quad * gotojump = new GotoQuad(afterLabel);
	proc->addQuad(gotojump);

	proc->addQuad(elseNop);
	
	for (auto stmt : *myBodyFalse){
		stmt->to3AC(proc);
	}

	proc->addQuad(afterNop);
}

void WhileStmtNode::to3AC(Procedure * proc){
	Quad * headNop = new NopQuad();
	Label * headLabel = proc->makeLabel();
	headNop->addLabel(headLabel);

	Label * afterLabel = proc->makeLabel();
	Quad * afterQuad = new NopQuad();
	afterQuad->addLabel(afterLabel);

	proc->addQuad(headNop);
	Opd * cond = myCond->flatten(proc);
	Quad * jmpFalse = new IfzQuad(cond, afterLabel);
	proc->addQuad(jmpFalse);

	for (auto stmt : *myBody){
		stmt->to3AC(proc);
	}

	Quad * loopBack = new GotoQuad(headLabel);
	proc->addQuad(loopBack);
	proc->addQuad(afterQuad);

}

void ForStmtNode::to3AC(Procedure * proc){
	Quad * headNop = new NopQuad();
	Label * headLabel = proc->makeLabel();
	headNop->addLabel(headLabel);

	Label * afterLabel = proc->makeLabel();
	Quad * afterQuad = new NopQuad();
	afterQuad->addLabel(afterLabel);

	proc->addQuad(headNop);
	
	//Opd * cond = myCond->flatten(proc);
	//Quad * jmpFalse = new IfzQuad(cond, afterLabel);
	//proc->addQuad(jmpFalse);

	//for (auto stmt : *myBody){
	//	stmt->to3AC(proc);
	//}

	Quad * loopBack = new GotoQuad(headLabel);
	proc->addQuad(loopBack);
	proc->addQuad(afterQuad);
}

void CallStmtNode::to3AC(Procedure * proc){
	Opd * res = myCallExp->flatten(proc);
	if (res != nullptr){
		Quad * last = proc->popQuad();
	}
}

void ReturnStmtNode::to3AC(Procedure * proc){
	if (myExp != nullptr){
		Opd * res = myExp->flatten(proc);
		Quad * setRet = new SetRetQuad(res);
		proc->addQuad(setRet);
	}
	
	Label * leaveLbl = proc->getLeaveLabel();
	Quad * jmpLeave = new GotoQuad(leaveLbl);
	proc->addQuad(jmpLeave);
}

void VarDeclNode::to3AC(Procedure * proc){
	SemSymbol * sym = ID()->getSymbol();
	assert(sym != nullptr);
	proc->gatherLocal(sym);
}

void VarDeclNode::to3AC(IRProgram * prog){
	SemSymbol * sym = ID()->getSymbol();
	assert(sym != nullptr);
	prog->gatherGlobal(sym);
}

//We only get to this node if we are in a stmt
// context (DeclNodes protect descent)
Opd * IDNode::flatten(Procedure * proc){
	SemSymbol * sym = this->getSymbol();
	Opd * res = proc->getSymOpd(sym);
	if (!res){
		throw new InternalError("null id sym");;
	}
	return res;
}
}