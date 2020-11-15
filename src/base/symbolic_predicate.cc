// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include "base/symbolic_predicate.h"
#include <stdio.h>
namespace crest {

SymbolicPred::SymbolicPred()
  : op_(ops::EQ), expr_(new SymbolicExpr(0)) {
    // fprintf(stderr, "SymbolicPred: Constructor\n");
  }

  SymbolicPred::SymbolicPred(compare_op_t op, SymbolicExpr* expr)
    : op_(op), expr_(expr) { }


    // compare_op_t op_;
    // SymbolicExpr* expr_;
  // void SymbolicPred::clone(SymbolicPred &sp) {
  //   sp.op_ = op_;
  //   // check copy constructor called here
  //   sp.expr_ = expr_;
  //   // sp.expr_->const_ = expr->const_;
  //   // sp.expr->coeff_ = expr->coeff_;
  // }
  // value_t const_;
// path.constraints_[i] = new SymbolicPred(constraints_[i]->op(), constraints_[i]->expr());
  SymbolicPred::SymbolicPred(compare_op_t op, SymbolicExpr &expr) {
    // copy constructor called
    fprintf(stderr, "SymbolicPred copy \n");
    op_ = op;
    // expr_ = new SymbolicExpr(expr);
    expr.clone(expr_);
    // *expr_ = expr;


  }

// void SymbolicPred::clone(SymbolicPred &sp) {
//   sp.op_ = sp.op();
// }

// // Redefine copy constructor for deep copying
// SymbolicPred::SymbolicPred(const SymbolicPred& sp) {
//   fprintf(stderr, "SymbolicPred: copy\n");
//   op_ = sp.op_;
//   expr_ = sp.expr_;
// }

// // redifine operator= for deep copying
// SymbolicPred& SymbolicPred::operator=(const SymbolicPred& sp) {
//   fprintf(stderr, "copying predicate operator=\n");
//   fprintf(stderr, "SymbolicPred:: copy called\n");
//   if(this == &sp) {
//     return *this;
//   }
//   op_ = sp.op_;
//   expr_ = sp.expr_;
//   // *expr_ = sp.expr();
//   // expr_ = std::move(new SymbolicExpr(sp.expr()));
//   // expr_ = new SymbolicExpr(sp.expr());
// }
//
// SymbolicPred& SymbolicPred::operator=(SymbolicPred &&move) {
//   fprintf(stderr, "SymbolicPred:: mov called\n");
//   if(this== &move) {
//     return *this;
//   }
//   op_ = move.op_;
//   expr_ = std::move(move.expr_);
//   move.expr_ = nullptr;
// }
//
// SymbolicPred::SymbolicPred(SymbolicPred &&move) {
//   fprintf(stderr, "move pred\n");
//   op_ = move.op_;
//   expr_ = std::move(move.expr_);
//   move.expr_ = nullptr;
//
// }
// SymbolicExecution::SymbolicExecution(SymbolicExecution &&move) {
//   fprintf(stderr, "move se\n");
//   // *this = move;
//   vars_ = std::move(move.vars());
//   inputs_ = std::move(move.inputs());
//   path_ = std::move(move.path_);
//
// }


SymbolicPred::~SymbolicPred() {
  // fprintf(stderr , " Symbolic Pred destruc\n");
  if (this != nullptr) {
    delete expr_;
    expr_ = nullptr;
  }
}

void SymbolicPred::Negate() {
  op_ = NegateCompareOp(op_);
}

void SymbolicPred::AppendToString(string* s) const {
  const char* symbol[] = { "=", "/=", ">", "<=", "<", ">=" };
  s->push_back('(');
  s->append(symbol[op_]);
  s->push_back(' ');
  expr_->AppendToString(s);
  s->append(" 0)");
}

void SymbolicPred::Serialize(string* s) const {
  s->push_back(static_cast<char>(op_));
  expr_->Serialize(s);
}

bool SymbolicPred::Parse(istream& s) {
  op_ = static_cast<compare_op_t>(s.get());
  return (expr_->Parse(s) && !s.fail());
}

bool SymbolicPred::Equal(const SymbolicPred& p) const {
  return ((op_ == p.op_) && (*expr_ == *p.expr_));
}


}  // namespace crest
