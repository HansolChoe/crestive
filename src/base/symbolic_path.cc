// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include "base/symbolic_path.h"
#include <stdio.h>
#include <memory>
namespace crest {

SymbolicPath::SymbolicPath() { }

// redifine copy constructor for deep copying
SymbolicPath::SymbolicPath(const SymbolicPath& sp) {
  fprintf(stderr, "copying SymbolicPath - copy constructor\n");
  branches_ = sp.branches_;
  constraints_idx_ = sp.constraints_idx_;
  constraints_ = vector<SymbolicPred*>(sp.constraints().size());
  for(size_t i = 0 ; i < sp.constraints().size(); i++) {
    constraints_[i] = new SymbolicPred(*sp.constraints()[i]);
    // constraints_[i] = std::move(new SymbolicPred(*sp.constraints()[i]));
  }
}



// redifine operator= for deep copying
SymbolicPath& SymbolicPath::operator=(const SymbolicPath& sp) {
  fprintf(stderr, "copying SymbolicPath - operator=\n");

  if(this== &sp) {
    return *this;
  }
  branches_ = sp.branches_;
  constraints_idx_ = sp.constraints_idx_;
  fprintf(stderr, "operator = constraints size : %zu\n",sp.constraints().size());
  // constraints_ = sp.constraints();
  constraints_ = vector<SymbolicPred*>(sp.constraints().size());
  for(size_t i = 0 ; i < sp.constraints().size(); i++) {
    // std::unique_ptr<SymbolicPred> new_sp(new SymbolicPred(*sp.constraints()[i]));
    // constraints_[i] = &new_sp;
    constraints_[i] = new SymbolicPred(*sp.constraints()[i]);
    // *constraints_[i] = *sp.constraints_[i];
    // constraints_.push_back(new SymbolicPred(*sp.constraints()[i]));
    // constraints_[i] = std::move(new SymbolicPred(*sp.constraints()[i]));
  }
  // std::for_each(constraints_[i].begin(), constraints_[i].end(),)
}

SymbolicPath::SymbolicPath(SymbolicPath&& move) {
  fprintf(stderr, "mov SymbolicPath - operator=\n");

  for(size_t i = 0 ; i < constraints_.size(); i++) {
    fprintf(stderr, "delete constraints %u\n",i);
    delete constraints_[i];
    // constraints_[i] = move.constraints()[i];
  }
  branches_ = std::move(move.branches_);
  constraints_idx_ = std::move(move.constraints_idx_);
  fprintf(stderr, "mov constraints size before %zu\n", move.constraints_.size());
  constraints_ = vector<SymbolicPred*>(move.constraints().size());
  for(size_t i = 0 ; i < constraints_.size(); i++) {
    *constraints_[i] = *move.constraints_[i];
    move.constraints_[i] = nullptr;
    // fprintf(stderr, "delete constraints %u\n",i);
    // delete constraints_[i];
    // constraints_[i] = move.constraints()[i];
  }
  // constraints_ = std::move(move.constraints_);

  // constraints_ = vector<SymbolicPred*>(move.constraints().size());
  // fprintf(stderr, "constraints size : %zu\n",move.constraints().size());
  // constraints_ = vector<SymbolicPred *>(move.constraints_.size());
  // for(size_t i = 0 ; i < move.constraints().size(); i++) {
  //   // constraints_.push_back(new SymbolicPred(*move.constraints()[i]));
  //   constraints_[i] = move.constraints_[i];
  //   move.constraints_[i] = nullptr;
  //   // constraints_[i] = new SymbolicPred(*move.constraints()[i]);
  // }
  // fprintf(stderr, "mov constraints size= %zu\n", move.constraints_.size());

  fprintf(stderr, "mov constraints size= %zu\n", move.constraints_.size());
}

SymbolicPath& SymbolicPath::operator=( SymbolicPath&& move) {
  fprintf(stderr, "mov SymbolicPath - operator=\n");
  if(this== &move) {
    return *this;
  }
  branches_ = std::move(move.branches_);
  constraints_idx_ = std::move(move.constraints_idx_);
  fprintf(stderr, "mov constraints size before %zu\n", move.constraints_.size());
  move.constraints_ = std::move(move.constraints_);
  // vector<SymbolicPred*> constraints_

  // for(size_t i = 0 ; i < constraints_.size(); i++) {
  //   fprintf(stderr, "delete constraints %u\n",i);
  //   delete constraints_[i];
  //   // constraints_[i] = move.constraints()[i];
  // }
  // constraints_
  // constraints_ = vector<SymbolicPred*>(move.constraints().size());
  for(size_t i = 0 ; i < constraints_.size(); i++) {
    // constraints_[i] = move.constraints_[i];
    // move.constraints_[i] = nullptr;
    // constraints_[i] = std::move(new SymbolicPred(*move.constraints_[i]));
    // move.constraints_[i] = nullptr;
    // constraints_[i] = std::move(new SymbolicPred(*move.constraints_[i]));


    // *constraints_[i] = std::move(*move.constraints_[i]);
    // }
    //   // delete constraints_[i];
    //   // constraints_[i] = move.constraints()[i];
  }

  // constraints_ = std::move(move.constraints_);

  // constraints_ = vector<SymbolicPred*>(move.constraints().size());
  // fprintf(stderr, "constraints size : %zu\n",move.constraints().size());
  // constraints_ = vector<SymbolicPred *>(move.constraints_.size());
  // for(size_t i = 0 ; i < move.constraints().size(); i++) {
  //   // constraints_.push_back(new SymbolicPred(*move.constraints()[i]));
  //   constraints_[i] = move.constraints_[i];
  //   move.constraints_[i] = nullptr;
  //   // constraints_[i] = new SymbolicPred(*move.constraints()[i]);
  // }
  // fprintf(stderr, "mov constraints size= %zu\n", move.constraints_.size());

  fprintf(stderr, "mov constraints size= %zu\n", move.constraints_.size());
}


//
// void Search::PrintPathConstraint(const SymbolicPath &sym_path) {
//   string tmp;
//   if (sym_path.constraints().size() == 0) {
//     std::cerr << "(Empty)" << std::endl;
//     return;
//   }
//   for (size_t i = 0; i < sym_path.constraints().size(); i++) {
//     tmp.clear();
//     size_t b_idx = sym_path.constraints_idx()[i];
//     branch_id_t bid = sym_path.branches()[b_idx];
//     sym_path.constraints()[i]->AppendToString(&tmp);
//     std::cerr << i << "("<<bid << "): " << tmp << '\n';
//   }
// }

// redifine equals for path comparison
// only branches that executed is concerned
// SymbolicPath& SymbolicPath::operator==(const SymbolicPath& lhs, const SymbolicPath& rhs) {
  // for(size_t i = 0 ; i < sp.constraints().size(); i++) {
  //   constraints_[i] = new SymbolicPred(*sp.constraints()[i]);
  // }
  // return lhs.branches() == rhs.branches();
// }


SymbolicPath::SymbolicPath(bool pre_allocate) {
  if (pre_allocate) {
    // To cut down on re-allocation.
    branches_.reserve(4000000);
    constraints_idx_.reserve(50000);
    constraints_.reserve(50000);
  }
}

SymbolicPath::~SymbolicPath() {
  for (size_t i = 0; i < constraints_.size(); i++)
    delete constraints_[i];
}

void SymbolicPath::Swap(SymbolicPath& sp) {
  fprintf(stderr, "Swap path\n");
  branches_.swap(sp.branches_);
  constraints_idx_.swap(sp.constraints_idx_);
  constraints_.swap(sp.constraints_);
  // branches_ = std::move(sp.branches_);
  // constraints_idx_ = std::move(sp.constraints_idx_);
  // constraints_.swap(sp.constraints_);
}

void SymbolicPath::Push(branch_id_t bid) {
  branches_.push_back(bid);
}

void SymbolicPath::Push(branch_id_t bid, SymbolicPred* constraint) {
  if (constraint) {
    constraints_.push_back(constraint);
    constraints_idx_.push_back(branches_.size());
  }
  branches_.push_back(bid);
}

void SymbolicPath::Serialize(string* s) const {
  typedef vector<SymbolicPred*>::const_iterator ConIt;

  // Write the path.
  size_t len = branches_.size();
  s->append((char*)&len, sizeof(len));
  s->append((char*)&branches_.front(), branches_.size() * sizeof(branch_id_t));

  // Write the path constraints.
  len = constraints_.size();
  s->append((char*)&len, sizeof(len));
  s->append((char*)&constraints_idx_.front(), constraints_.size() * sizeof(size_t));
  for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
    (*i)->Serialize(s);
  }
}

bool SymbolicPath::Parse(istream& s) {
  typedef vector<SymbolicPred*>::iterator ConIt;
  size_t len;

  // Read the path.
  s.read((char*)&len, sizeof(size_t));
  branches_.resize(len);
  s.read((char*)&branches_.front(), len * sizeof(branch_id_t));
  if (s.fail())
    return false;

  // Clean up any existing path constraints.
  for (size_t i = 0; i < constraints_.size(); i++) {
    delete constraints_[i];
  }

  // Read the path constraints.
  s.read((char*)&len, sizeof(size_t));
  constraints_idx_.resize(len);
  constraints_.resize(len);
  s.read((char*)&constraints_idx_.front(), len * sizeof(size_t));
  fprintf(stderr, "parse constraints start\n");
  for (ConIt i = constraints_.begin(); i != constraints_.end(); ++i) {
    // *i = new SymbolicPred();
    *i = new SymbolicPred();
    // if (!(*i)->Parse(s))
    //   return false;
    if(!(*i)->Parse(s)){
      return false;
    }
  }
  fprintf(stderr, "parse constraints end\n");

  return !s.fail();
}

}  // namespace crest
