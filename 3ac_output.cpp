#include "ast.hpp"

namespace drewgon{

IRProgram * ProgramNode::to3AC(TypeAnalysis * ta){
	IRProgram * prog = new IRProgram(ta);
	for (auto global : *myGlobals){
		global->to3AC(prog);
	}
	return prog;
}

void FnDeclNode::to3AC(IRProgram * prog){
	TODO(Implement me)
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
	TODO(Implement me)
}

Opd * MayhemNode::flatten(Procedure * proc){
	TODO(Implement me)
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
	
	AssignQuad * quad = new AssignQuad(op1, op2);
	quad->setComment("Assign");
	proc->addQuad(quad);
	return op1;
}

Opd * CallExpNode::flatten(Procedure * proc){
	TODO(Implement me)
	// myArgs->to3AC(proc);
	// Quad * callQuad = new CallQuad(myID->getSymbol());
	// proc->addQuad(callQuad);

	// SemSymbol * idSym = myID->getSymbol();
	// const FnType * calleeType = idSym->getDataType()->asFn();
	// if (calleeType->getReturnType()->isVoid()){
	// 	return nullptr;
	// } else {
	// 	Opd * retVal = proc->makeTmp(8);
	// 	Quad * getRet = new GetRetQuad(1, retVal);
	// 	proc->addQuad(getRet);
	// 	return retVal;
	// }
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
	TODO(Implement me)
}

void InputStmtNode::to3AC(Procedure * proc){
	TODO(Implement me)
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
	TODO(Implement me)
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
	TODO(Implement me)
	// Opd * baseOpd = myBase->flatten(proc);
	// const DataType * baseType = proc->getProg()->nodeType(myBase);
	// const RecordType * recordType = baseType->asRecord();
	// assert(recordType != nullptr);
	
	// //Opd * offOpd = myIdx->flatten(proc);
	// size_t offsetVal = recordType->getOffset(myIdx->getName());
	// size_t width = 8;
	// LitOpd * offOpd = new LitOpd(to_string(offsetVal), 8);
	
	// AddrOpd * idxLoc = proc->makeAddrOpd(width);
	// IndexQuad * idx = new IndexQuad(idxLoc, baseOpd, offOpd);
	// proc->addQuad(idx);
	// return idxLoc;

}
}
