// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <utility>

#include "base/symbolic_execution.h"
#include <stdio.h>

namespace crest {

SymbolicExecution::SymbolicExecution() {
  fprintf(stderr, "constructor se\n");
}


SymbolicExecution::SymbolicExecution(const SymbolicExecution& se)
{
  fprintf(stderr, "copying se : copy constructor\n");
  vars_ = se.vars();
  inputs_ = se.inputs();
  path_ = se.path();
}

SymbolicExecution& SymbolicExecution::operator=(const SymbolicExecution& rhs) {
  fprintf(stderr, "copying se : operator=\n");
  if (this == &rhs) {
    return *this;
  }
  vars_ = rhs.vars_;
  inputs_ = rhs.inputs_;
  path_ = rhs.path_;
  fprintf(stderr, "copying se : operator= end\n");
}
SymbolicExecution::SymbolicExecution(SymbolicExecution &&move) {
  fprintf(stderr, "move se\n");
  // *this = move;
  vars_ = std::move(move.vars());
  inputs_ = std::move(move.inputs());
  path_ = std::move(move.path_);

}
SymbolicExecution & SymbolicExecution::operator=(SymbolicExecution &&move) {

  fprintf(stderr, "operator= &&move se\n");
  if(this== &move) {
    return *this;
  }
  vars_ = std::move(move.vars_);
  inputs_ = std::move(move.inputs_);
  path_ = std::move(move.path_);
  // *this = move;
  fprintf(stderr, "operator= &&move se end\n");
}

/*
SymbolicExecution::SymbolicExecution(const SymbolicExecution& se)
{
  // fprintf(stderr, "copying se : copy constructor\n");
  vars_ = se.vars();
  inputs_ = se.inputs();
  path_.branches_ = se.path().branches();
  path_.constraints_idx_ = se.path().constraints_idx_;
  path_.constraints_ = vector<SymbolicPred*>(se.path().constraints().size());
  for(size_t i = 0 ; i < se.path().constraints().size(); i++) {
    path_.constraints_.push_back(new SymbolicPred(*se.path().constraints()[i]));
  }
  //new_path. = se.path().branches();

  //path_ = se.path();
}

SymbolicExecution& SymbolicExecution::operator=(const SymbolicExecution& rhs) {
  fprintf(stderr, "copying se : operator=\n");
  if (this == &rhs) {
    return *this;
  }
  vars_ = rhs.vars();
  inputs_ = rhs.inputs();
  // path_ = rhs.path();
  path_.branches_ = rhs.path().branches();
  path_.constraints_idx_ = rhs.path().constraints_idx_;
  path_.constraints_ = vector<SymbolicPred*>(rhs.path().constraints().size());
  fprintf(stderr, "copying se : operator= 2\n");
  for(size_t i = 0 ; i < rhs.path().constraints().size(); i++) {
    path_.constraints_.push_back(new SymbolicPred(*rhs.path().constraints()[i]));
  }
  fprintf(stderr, "copying se : operator= 3\n");
}
*/

SymbolicExecution::SymbolicExecution(bool pre_allocate)
  : path_(pre_allocate) { }

SymbolicExecution::~SymbolicExecution() {
fprintf(stderr, "Symbolic Execution Destructor : path size : %zu\n", path_.constraints().size() );
 }

void SymbolicExecution::Swap(SymbolicExecution& se) {
  fprintf(stderr, "SE swap\n");
  // vars_ = std::move(se.vars_);
  // inputs_ = std::move(se.inputs_);
  // path_ = std::move(se.path_);
  // vars_.swap(se.vars_);
  // inputs_.swap(se.inputs_);
  // path_.Swap(se.path_);
  fprintf(stderr, "SE swap 1\n");
  SymbolicExecution tmp =std::move(se);
  fprintf(stderr, "SE swap 2\n");
  se =std::move(*this);
  fprintf(stderr, "SE swap 3\n");
  *this =std::move(tmp);
  fprintf(stderr, "SE swap 4\n");

  // se.mov=std::move(tmp);

}

void SymbolicExecution::Serialize(string* s) const {
  typedef map<var_t,type_t>::const_iterator VarIt;

  // Write the inputs.
  size_t len = vars_.size();
  s->append((char*)&len, sizeof(len));
  for (VarIt i = vars_.begin(); i != vars_.end(); ++i) {
    s->push_back(static_cast<char>(i->second));
    s->append((char*)&inputs_[i->first], sizeof(value_t));
  }

  // Write the path.
  path_.Serialize(s);
}

bool SymbolicExecution::Parse(istream& s) {
  // Read the inputs.
  size_t len;
  s.read((char*)&len, sizeof(len));
  vars_.clear();
  inputs_.resize(len);
  for (size_t i = 0; i < len; i++) {
    vars_[i] = static_cast<type_t>(s.get());
    s.read((char*)&inputs_[i], sizeof(value_t));
  }

  // Write the path.
  return (path_.Parse(s) && !s.fail());
}

}  // namespace crest
