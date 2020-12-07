// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <algorithm>
#include <assert.h>
#include <unistd.h>
#include <cmath>
#include <iostream>
#include <fstream>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <deque>
#include <utility>
#include <sstream>
#include <cstring>

#include "base/z3_solver.h"
#include "run_crest/concolic_search.h"

using std::ifstream;
using std::ios;
using std::min;
using std::max;
using std::numeric_limits;
using std::pair;
using std::queue;
using std::deque;
using std::random_shuffle;
using std::stable_sort;
using std::strcmp;

namespace crest {
  Runner::Runner(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

  Runner::~Runner() { }
  void Runner::Run() { }

////////////////////////////////////////////////////////////////////////
//// Search ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

void Search::ResetInitialInputFiles() {
  system("cp initial_input input");
}

void Search::PrintPathConstraint(const SymbolicPath &sym_path) {
  string tmp;
  if (sym_path.constraints().size() == 0) {
    std::cerr << "(Empty)" << std::endl;
    return;
  }
  for (size_t i = 0; i < sym_path.constraints().size(); i++) {
    tmp.clear();
    size_t b_idx = sym_path.constraints_idx()[i];
    branch_id_t bid = sym_path.branches()[b_idx];
    sym_path.constraints()[i]->AppendToString(&tmp);
    std::cerr << i << "("<<bid << "): " << tmp << '\n';
  }
}

Search::Search(const string& program, int max_iterations)
  : program_(program), max_iters_(max_iterations), num_iters_(0) {
    error_count = 0;
  start_time_ = time(NULL);
  begin_total_ = std::chrono::high_resolution_clock::now();
  summary_time_ = 0;
  //time_out_ = 1800;
  time_out_ =600;
  num_prediction_fail_ = 0;
  num_unsat_ = 0;

  { // Read in the set of branches.
    max_branch_ = 0;
    max_function_ = 0;
    branches_.reserve(100000);
    branch_count_.reserve(100000);
    branch_count_.push_back(0);

    ifstream in("branches");
    assert(in);
    function_id_t fid;
    int numBranches;
    while (in >> fid >> numBranches) {
      branch_count_.push_back(2 * numBranches);
      branch_id_t b1, b2;
      for (int i = 0; i < numBranches; i++) {
	assert(in >> b1 >> b2);
	branches_.push_back(b1);
	branches_.push_back(b2);
	max_branch_ = max(max_branch_, max(b1, b2));
      }
    }
    in.close();
    max_branch_ ++;
    max_function_ = branch_count_.size();
  }

  // Compute the paired-branch map.
  paired_branch_.resize(max_branch_);
  for (size_t i = 0; i < branches_.size(); i += 2) {
    paired_branch_[branches_[i]] = branches_[i+1];
    paired_branch_[branches_[i+1]] = branches_[i];
  }

  // Compute the branch-to-function map.
  branch_function_.resize(max_branch_);
  { size_t i = 0;
    for (function_id_t j = 0; j < branch_count_.size(); j++) {
      for (size_t k = 0; k < branch_count_[j]; k++) {
	branch_function_[branches_[i++]] = j;
      }
    }
  }

  // Initialize all branches to "uncovered" (and functions to "unreached").
  total_num_covered_ = num_covered_ = 0;
  reachable_functions_ = reachable_branches_ = 0;
  covered_.resize(max_branch_, false);
  total_covered_.resize(max_branch_, false);
  reached_.resize(max_function_, false);
#if 0
  { // Read in any previous coverage (for faster debugging).
    ifstream in("coverage");
    branch_id_t bid;
    while (in >> bid) {
      covered_[bid] = true;
      num_covered_ ++;
      if (!reached_[branch_function_[bid]]) {
	reached_[branch_function_[bid]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[bid]];
      }
    }

    total_num_covered_ = 0;
    total_covered_ = covered_;
  }
#endif

  // Print out the initial coverage.
  fprintf(stderr, "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
          num_covered_, reachable_functions_, reachable_branches_);

  // Sort the branches.
  sort(branches_.begin(), branches_.end());
}


Search::~Search() { }


void Search::WriteInputToFileOrDie(const char* file_name,
				   const vector<value_t>& input) {
  FILE* f = fopen(file_name, "w");
  if (!f) {
    fprintf(stderr, "Failed to open %s.\n", file_name);
    perror("Error: ");
    exit(-1);
  }

  for (size_t i = 0; i < input.size(); i++) {
    fprintf(f, "%lld\n", input[i]);
  }

  fclose(f);
}


void Search::WriteCoverageToFileOrDie(const string& file) {
  FILE* f = fopen(file.c_str(), "w");
  if (!f) {
    fprintf(stderr, "Failed to open %s.\n", file.c_str());
    perror("Error: ");
    exit(-1);
  }

  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    if (total_covered_[*i]) {
      fprintf(f, "%d\n", *i);
    }
  }

  fclose(f);
}



void Search::LaunchProgram(const vector<value_t>& inputs) {
  WriteInputToFileOrDie("input", inputs);
  setenv("CREST_INPUT_FILE_NAME", "input", 1);
   // auto start = std::chrono::high_resolution_clock::now();
   int ret = system(program_.c_str());
   // auto end = std::chrono::high_resolution_clock::now();
   // elapsed_time_program_ += (end - start);
  // if (ret == -1 || WEXITSTATUS(ret) != 0) {
  //   error_count++;
  // }
  // fprintf(stderr, "ret = %d\n",WEXITSTATUS(ret));
  // fprintf(stderr, "error_count = %u\n",error_count);

  // fprintf( stderr , " time program : %.2f\n", elapsed_time_program_.count());

}


void Search::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  end_total_ = std::chrono::high_resolution_clock::now();
  elapsed_time_total_ = end_total_ - begin_total_;

  if (++num_iters_ > max_iters_ || elapsed_time_total_.count() >= time_out_) {
    // fprintf(stderr, "max Q size = %u\n", max_Q_size);
    // fprintf(stderr, "# of all pf branches:\n");
    // for (auto i : pf_count_) {
    //     fprintf(stderr, "%u,%u\n", i.first, i.second);
    // }
    // fprintf(stderr, "\n# of (pf >= 10) branches:\n");
    // for (auto i : pf_count_) {
    //   if(i.second > 10) {
    //     fprintf(stderr, "%u,%u\n", i.first, i.second);
    //   }
    // }
    //
    // fprintf(stderr, "\n# of all unsat branches:\n");
    // for (auto i : unsat_count_) {
    //     fprintf(stderr, "%u,%u\n", i.first, i.second);
    // }
    // fprintf(stderr, "\n# of (unsat >= 10) branches:\n");
    // for (auto i : unsat_count_) {
    //   if(i.second > 10) {
    //     fprintf(stderr, "%u,%u\n", i.first, i.second);
    //   }
    // }
    exit(0);
  }

  // Run the program.
  LaunchProgram(inputs);

  ifstream in(("szd_execution"), ios::in | ios::binary);
  assert(in && ex->Parse(in));
  in.close();
}


bool Search::UpdateCoverage(const SymbolicExecution& ex) {
  return UpdateCoverage(ex, NULL);
}

bool Search::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches) {
  // auto start = std::chrono::high_resolution_clock::now();
  const unsigned int prev_covered_ = num_covered_;
  const vector<branch_id_t>& branches = ex.path().branches();
  for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
    if ((*i > 0) && !covered_[*i]) {
      covered_[*i] = true;
      num_covered_++;
      if (new_branches) {
	new_branches->insert(*i);
      }
      if (!reached_[branch_function_[*i]]) {
	reached_[branch_function_[*i]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[*i]];
      }
    }
    if ((*i > 0) && !total_covered_[*i]) {
      total_covered_[*i] = true;
      total_num_covered_++;
    }
  }


  fprintf(stderr, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);

  // PrintPathConstraint(ex.path());

  bool found_new_branch = (num_covered_ > prev_covered_);
  if (found_new_branch) {
    WriteCoverageToFileOrDie("coverage");
  }

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;

  if (log_file_name_ != 0) {
    FILE *f = fopen(log_file_name_, "a");
    if (!f) {
      fprintf(stderr, "Writing logging, failed to open %s. \n", log_file_name_);
      return found_new_branch;
    }
    fprintf(f, "%u,%.2lf,%u,%u\n",
      total_num_covered_,
      time_diff,
      num_prediction_fail_,
      num_unsat_
    );
    fclose(f);
  }

  if (summary_file_name_ != 0) {
    while(summary_time_ <= time_diff.count()) {
      FILE *ff = fopen(summary_file_name_, "a");
      if (!ff) {
        fprintf(stderr, "Writing summary, failed to open %s. \n", summary_file_name_);
        return found_new_branch;
      }
      fprintf(ff, "%u,%.2lf,%u,%u\n",
            total_num_covered_,
            time_diff,
            num_prediction_fail_,
            num_unsat_
           );

      fclose(ff);
      summary_time_ += 10;
    }
  }
  return found_new_branch;
}

bool RandomMDSearch::UpdateCoverage(const SymbolicExecution& ex, EXContext &context) {
  return UpdateCoverage(ex, NULL, context);
}

bool RandomMDSearch::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches, EXContext &context) {

  const unsigned int prev_covered_ = num_covered_;
  const vector<branch_id_t>& branches = ex.path().branches();
  for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
    if ((*i > 0) && !covered_[*i]) {
      covered_[*i] = true;
      covered_branches_.insert(*i);
      num_covered_++;
      if (new_branches) {
	new_branches->insert(*i);
      }
      if (!reached_[branch_function_[*i]]) {
	reached_[branch_function_[*i]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[*i]];
      }
    }
    if ((*i > 0) && !total_covered_[*i]) {
      total_covered_[*i] = true;
      total_num_covered_++;
    }
  }

  // set<branch_id_t> u;
  // for(const branch_id_t b: covered_branches_) {
  //   if(!covered_[paired_branch_[b]]) {
  //     u.insert(b);
  //   }
  // }

  fprintf(stderr, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);

  bool found_new_branch = (num_covered_ > prev_covered_);
  if (found_new_branch) {
    WriteCoverageToFileOrDie("coverage");
  }

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;

  if (log_file_name_ != 0) {
    FILE *f = fopen(log_file_name_, "a");
    if (!f) {
      fprintf(stderr, "Writing logging, failed to open %s. \n", log_file_name_);
      return found_new_branch;
    }
    fprintf(f, "%u,%.2lf,%u,%u,%u,%u\n",
      total_num_covered_,
      time_diff,
      num_prediction_fail_,
      num_unsat_,
      Q.size(),
      context.energy);
    fclose(f);
  }

  if (summary_file_name_ != 0) {
    while(summary_time_ <= time_diff.count()) {
      FILE *ff = fopen(summary_file_name_, "a");
      if (!ff) {
        fprintf(stderr, "Writing summary, failed to open %s. \n", summary_file_name_);
        return found_new_branch;
      }
      fprintf(ff, "%u,%.2lf,%u,%u,%u,%u\n",
         total_num_covered_,
         time_diff,
         num_prediction_fail_,
         num_unsat_,
         Q.size(),
         context.energy);

      fclose(ff);
      summary_time_ += 10;
    }
  }

  return found_new_branch;
}

bool CfgHeuristicMDSearch::UpdateCoverage(const SymbolicExecution& ex, Context &context) {
  return UpdateCoverage(ex, NULL, context);
}

bool CfgHeuristicMDSearch::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches, Context &context) {
  const unsigned int prev_covered_ = context.num_covered;
  // auto start = std::chrono::high_resolution_clock::now();
  // auto end = std::chrono::high_resolution_clock::now();
  // fprintf(stderr, "num_covered1 : %u\n", context.num_covered);
  const vector<branch_id_t>& branches = ex.path().branches();
  // start = std::chrono::high_resolution_clock::now();
  for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
    if ((*i > 0) && !context.covered[*i]) {
      // fprintf(stderr, "branch %d : %d\n", *i, covered_[*i]);
      covered_[*i] = true;
      covered_branches_.insert(*i);
      // elapsed_time_searching_9_ += (end - start);
      context.covered[*i] = true;

      context.num_covered++;
      if (new_branches) {
	new_branches->insert(*i);
  // covered_branches_.insert(*i);
      // fprintf(stderr, "size of new branches = %u\n",new_branches->size());
      }
      if (!reached_[branch_function_[*i]]) {
	reached_[branch_function_[*i]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[*i]];
      }
    }
    if ((*i > 0) && !total_covered_[*i]) {
      total_covered_[*i] = true;
      total_num_covered_++;
    }
  }


  fprintf(stderr, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);

  bool found_new_branch = (context.num_covered > prev_covered_);
  if (found_new_branch) {
     WriteCoverageToFileOrDie("coverage");
  } else {

 }

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;

  if (log_file_name_ != 0) {
    FILE *f = fopen(log_file_name_, "a");
    if (!f) {
      fprintf(stderr, "Writing logging, failed to open %s. \n", log_file_name_);
      return found_new_branch;
    }
    fprintf(f, "%u,%.2lf,%u,%u,%u,%u\n",
     total_num_covered_,
     time_diff,
     num_prediction_fail_,
     num_unsat_,
     Q.size(),
     context.energy);
    fclose(f);
  }

  if (summary_file_name_ != 0) {
    while(summary_time_ <= time_diff.count()) {
      FILE *ff = fopen(summary_file_name_, "a");
      if (!ff) {
        fprintf(stderr, "Writing summary, failed to open %s. \n", summary_file_name_);
        return found_new_branch;
      }
      fprintf(ff, "%u,%.2lf,%u,%u,%u,%u\n",
         total_num_covered_,
         time_diff,
         num_prediction_fail_,
         num_unsat_,
         Q.size(),
         context.energy);
      fclose(ff);
      summary_time_ += 10;
    }
  }


  return found_new_branch;
}

void Search::RandomInput(const map<var_t,type_t>& vars, vector<value_t>* input) {
  input->resize(vars.size());

  for (map<var_t,type_t>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
    unsigned long long val = 0;
    for (size_t j = 0; j < 8; j++)
      val = (val << 8) + (rand() / 256);

    switch (it->second) {
    case types::U_CHAR:
      input->at(it->first) = (unsigned char)val; break;
    case types::CHAR:
      input->at(it->first) = (char)val; break;
    case types::U_SHORT:
      input->at(it->first) = (unsigned short)val; break;
    case types::SHORT:
      input->at(it->first) = (short)val; break;
    case types::U_INT:
      input->at(it->first) = (unsigned int)val; break;
    case types::INT:
      input->at(it->first) = (int)val; break;
    case types::U_LONG:
      input->at(it->first) = (unsigned long)val; break;
    case types::LONG:
      input->at(it->first) = (long)val; break;
    case types::U_LONG_LONG:
      input->at(it->first) = (unsigned long long)val; break;
    case types::LONG_LONG:
      input->at(it->first) = (long long)val; break;
    }
  }
}


bool Search::SolveAtBranch(const SymbolicExecution& ex,
                           size_t branch_idx,
                           vector<value_t>* input) {

  const vector<SymbolicPred*>& constraints = ex.path().constraints();
  // Optimization: If any of the previous constraints are idential to the
  // branch_idx-th constraint, immediately return false.
  for (int i = static_cast<int>(branch_idx) - 1; i >= 0; i--) {
      if (constraints[branch_idx]->Equal(*constraints[i])) {
          num_unsat_++;
          unsat_count_[ex.path().branches()[ex.path().constraints_idx()[branch_idx]]]++;
      return false;

      }
  }

  vector<const SymbolicPred*> cs(constraints.begin(),
				 constraints.begin()+branch_idx+1);
  map<var_t,value_t> soln;
  constraints[branch_idx]->Negate();
  // fprintf(stderr, "Yices . . . ");
  bool success ;
  // auto start = std::chrono::high_resolution_clock::now();
  success = Z3Solver::IncrementalSolve(ex.inputs(), ex.vars(), cs, &soln);
  // auto end = std::chrono::high_resolution_clock::now();
  // elapsed_time_solving_ += (end - start);

  constraints[branch_idx]->Negate();
  if (success) {
    // Merge the solution with the previous input to get the next
    // input.  (Could merge with random inputs, instead.)
    *input = ex.inputs();
    // RandomInput(ex.vars(), input);

    typedef map<var_t,value_t>::const_iterator SolnIt;
    for (SolnIt i = soln.begin(); i != soln.end(); ++i) {
      (*input)[i->first] = i->second;
    }

    return true;
  }
  num_unsat_++;
  unsat_count_[ex.path().branches()[ex.path().constraints_idx()[branch_idx]]]++;
  return false;
}


bool Search::CheckPrediction(const SymbolicExecution& old_ex,
			     const SymbolicExecution& new_ex,
			     size_t branch_idx) {

  if ((old_ex.path().branches().size() <= branch_idx)
      || (new_ex.path().branches().size() <= branch_idx)) {
    num_prediction_fail_++;
    pf_count_[branch_idx]++;
    return false;
  }

   for (size_t j = 0; j < branch_idx; j++) {
     if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
       num_prediction_fail_++;
       pf_count_[branch_idx]++;
       return false;
     }
   }
   return (new_ex.path().branches()[branch_idx]
           == paired_branch_[old_ex.path().branches()[branch_idx]]);
}


////////////////////////////////////////////////////////////////////////
//// BoundedDepthFirstSearch ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

BoundedDepthFirstSearch::BoundedDepthFirstSearch
(const string& program, int max_iterations, int max_depth)
  : Search(program, max_iterations), max_depth_(max_depth) { }

BoundedDepthFirstSearch::~BoundedDepthFirstSearch() { }

void BoundedDepthFirstSearch::Run() {
  // Initial execution (on empty/random inputs).
  SymbolicExecution ex;
  RunProgram(vector<value_t>(), &ex);
  UpdateCoverage(ex);

  DFS(0, max_depth_, ex);
}


void BoundedDepthFirstSearch::DFS(size_t pos, int depth, SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;

  const SymbolicPath& path = prev_ex.path();

  for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); i++) {
    // Solve constraints[0..i].
    if (!SolveAtBranch(prev_ex, i, &input)) {
      continue;
    }

    // Run on those constraints.
    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);

    // Check for prediction failure.
    size_t branch_idx = path.constraints_idx()[i];
    if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
      fprintf(stderr, "Prediction failed!\n");
      continue;
    }

    // We successfully solved the branch, recurse.
    depth--;
    DFS(i+1, depth, cur_ex);
  }
}


////////////////////////////////////////////////////////////////////////
//// RandomInputSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomInputSearch::RandomInputSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomInputSearch::~RandomInputSearch() { }

void RandomInputSearch::Run() {
  vector<value_t> input;
  RunProgram(input, &ex_);

  while (true) {
    RandomInput(ex_.vars(), &input);
    RunProgram(input, &ex_);
    UpdateCoverage(ex_);
  }
}


////////////////////////////////////////////////////////////////////////
//// UniformRandomSearch ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

UniformRandomSearch::UniformRandomSearch(const string& program,
					 int max_iterations,
					 size_t max_depth)
  : Search(program, max_iterations), max_depth_(max_depth) { }

UniformRandomSearch::~UniformRandomSearch() { }

void UniformRandomSearch::Run() {
  // Initial execution (on empty/random inputs).
  RunProgram(vector<value_t>(), &prev_ex_);
  UpdateCoverage(prev_ex_);

  while (true) {
    fprintf(stderr, "RESET\n");
    // Uniform random path.
    DoUniformRandomPath();
  }
}


void UniformRandomSearch::DoUniformRandomPath() {
  vector<value_t> input;

  size_t i = 0;
  size_t depth = 0;
  fprintf(stderr, "%zu constraints.\n", prev_ex_.path().constraints().size());
  while ((i < prev_ex_.path().constraints().size()) && (depth < max_depth_)) {
    if (SolveAtBranch(prev_ex_, i, &input)) {
      fprintf(stderr, "Solved constraint %zu/%zu.\n",
      (i+1), prev_ex_.path().constraints().size());
      depth++;

      // With probability 0.5, force the i-th constraint.
      if (rand() % 2 == 0) {
        RunProgram(input, &cur_ex_);
        UpdateCoverage(cur_ex_);
        size_t branch_idx = prev_ex_.path().constraints_idx()[i];
        if (!CheckPrediction(prev_ex_, cur_ex_, branch_idx)) {
          fprintf(stderr, "prediction failed\n");
          depth--;
        } else {
          cur_ex_.Swap(prev_ex_);
        }
      }
    }

    i++;
  }
}


////////////////////////////////////////////////////////////////////////
//// HybridSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

HybridSearch::HybridSearch(const string& program, int max_iterations, int step_size)
  : Search(program, max_iterations), step_size_(step_size) { }

HybridSearch::~HybridSearch() { }

void HybridSearch::Run() {
  SymbolicExecution ex;

  while (true) {
    // Execution on empty/random inputs.
    RunProgram(vector<value_t>(), &ex);
    UpdateCoverage(ex);

    // Local searches at increasingly deeper execution points.
    for (size_t pos = 0; pos < ex.path().constraints().size(); pos += step_size_) {
      RandomLocalSearch(&ex, pos, pos+step_size_);
    }
  }
}

void HybridSearch::RandomLocalSearch(SymbolicExecution *ex, size_t start, size_t end) {
  for (int iters = 0; iters < 100; iters++) {
    if (!RandomStep(ex, start, end))
      break;
  }
}

bool HybridSearch::RandomStep(SymbolicExecution *ex, size_t start, size_t end) {

  if (end > ex->path().constraints().size()) {
    end = ex->path().constraints().size();
  }
  assert(start < end);

  SymbolicExecution next_ex;
  vector<value_t> input;

  fprintf(stderr, "%zu-%zu\n", start, end);
  vector<size_t> idxs(end - start);
  for (size_t i = 0; i < idxs.size(); i++) {
    idxs[i] = start + i;
  }

  for (int tries = 0; tries < 1000; tries++) {
    // Pick a random index.
    if (idxs.size() == 0)
      break;
    size_t r = rand() % idxs.size();
    size_t i = idxs[r];
    swap(idxs[r], idxs.back());
    idxs.pop_back();

    if (SolveAtBranch(*ex, i, &input)) {
      RunProgram(input, &next_ex);
      UpdateCoverage(next_ex);
      if (CheckPrediction(*ex, next_ex, ex->path().constraints_idx()[i])) {
	ex->Swap(next_ex);
	return true;
      }
    }
  }

  return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgBaselineSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgBaselineSearch::CfgBaselineSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

CfgBaselineSearch::~CfgBaselineSearch() { }


void CfgBaselineSearch::Run() {
  SymbolicExecution ex;

  while (true) {
    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    UpdateCoverage(ex);

    while (DoSearch(5, 250, 0, ex)) {
      // As long as we keep finding new branches . . . .
      ex.Swap(success_ex_);
    }
  }
}


bool CfgBaselineSearch::DoSearch(int depth, int iters, int pos,
				 const SymbolicExecution& prev_ex) {

  // For each symbolic branch/constraint in the execution path, we will
  // compute a heuristic score, and then attempt to force the branches
  // in order of increasing score.
  vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    scoredBranches[i].first = i + pos;
  }

  { // Compute (and sort by) the scores.
    random_shuffle(scoredBranches.begin(), scoredBranches.end());
    map<branch_id_t,int> seen;
    for (size_t i = 0; i < scoredBranches.size(); i++) {
      size_t idx = scoredBranches[i].first;
      size_t branch_idx = prev_ex.path().constraints_idx()[idx];
      branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];
      if (covered_[bid]) {
	scoredBranches[i].second = 100000000 + seen[bid];
      } else {
	scoredBranches[i].second = seen[bid];
      }
      seen[bid] += 1;
    }
  }
  stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

  // Solve.
  SymbolicExecution cur_ex;
  vector<value_t> input;
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    if (iters <= 0) {
      return false;
    }

    if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
      continue;
    }

    RunProgram(input, &cur_ex);
    iters--;

    if (UpdateCoverage(cur_ex, NULL)) {
      success_ex_.Swap(cur_ex);
      return true;
    }
  }

  return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgHeuristicSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgHeuristicSearch::CfgHeuristicSearch
(const string& program, int max_iterations)
  : Search(program, max_iterations),
    cfg_(max_branch_), cfg_rev_(max_branch_), dist_(max_branch_) {
  fprintf(stderr, "Read cfg_branches\n");
  // Read in the CFG.
  ifstream in("cfg_branches", ios::in | ios::binary);
  assert(in);
  size_t num_branches;
  in.read((char*)&num_branches, sizeof(num_branches));
  assert(num_branches == branches_.size());
  for (size_t i = 0; i < num_branches; i++) {
    branch_id_t src;
    size_t len;
    in.read((char*)&src, sizeof(src));
    in.read((char*)&len, sizeof(len));
    cfg_[src].resize(len);
    in.read((char*)&cfg_[src].front(), len * sizeof(branch_id_t));
    fprintf(stderr, "branch : %u\n", src);
    fprintf(stderr, "len : %u\n", len);
    for(size_t j = 0 ; j < len; j++) {
      fprintf(stderr, "%u ", cfg_[src][j]);
    }
    fprintf(stderr, "\n");
  }
  in.close();

  // Construct the reversed CFG.
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
      cfg_rev_[*j].push_back(*i);
    }
  }
}


CfgHeuristicSearch::~CfgHeuristicSearch() { }


void CfgHeuristicSearch::Run() {
  set<branch_id_t> newly_covered_;
  SymbolicExecution ex;

  while (true) {
    covered_.assign(max_branch_, false);
    num_covered_ = 0;

    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    ResetInitialInputFiles();

    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      UpdateBranchDistances();
      // PrintStats();
    }

    // while (DoSearch(3, 200, 0, kInfiniteDistance+10, ex)) {
    while (DoSearch(5, 30, 0, kInfiniteDistance, ex)) {
    // while (DoSearch(3, 10000, 0, kInfiniteDistance, ex)) {
      // PrintStats();
      // As long as we keep finding new branches . . . .
      UpdateBranchDistances();
      ex.Swap(success_ex_);
    }
    // PrintStats();
  }
}


void CfgHeuristicSearch::PrintStats() {
  fprintf(stderr, "Cfg solves: %u/%u (%u lucky [%u continued], %u on 0's, %u on others,"
	  "%u unsats, %u prediction failures)\n",
	  (num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
	  num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
	  num_inner_zero_successes_, num_inner_nonzero_successes_,
	  num_inner_unsats_, num_inner_pred_fails_);
  fprintf(stderr, "    (recursive successes: %u)\n", num_inner_recursive_successes_);
  fprintf(stderr, "Top-level SolveAlongCfg: %u/%u\n",
	  num_top_solve_successes_, num_top_solves_);
  fprintf(stderr, "All SolveAlongCfg: %u/%u  (%u all concrete, %u no paths)\n",
	  num_solve_successes_, num_solves_,
	  num_solve_all_concrete_, num_solve_no_paths_);
  fprintf(stderr, "    (sat failures: %u/%u)  (prediction failures: %u) (recursions: %u)\n",
	  num_solve_unsats_, num_solve_sat_attempts_,
	  num_solve_pred_fails_, num_solve_recurses_);
}

void CfgHeuristicSearch::UpdateBranchDistances() {
  // We run a BFS backward, starting simultaneously at all uncovered vertices.
  queue<branch_id_t> Q;
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    if (!covered_[*i]) {
      dist_[*i] = 0;
      Q.push(*i);
    } else {
      dist_[*i] = kInfiniteDistance;
    }
  }

  while (!Q.empty()) {
    branch_id_t i = Q.front();
    size_t dist_i = dist_[i];
    Q.pop();

    for (BranchIt j = cfg_rev_[i].begin(); j != cfg_rev_[i].end(); ++j) {
      if (dist_i + 1 < dist_[*j]) {
      	dist_[*j] = dist_i + 1;
      	Q.push(*j);
      }
    }
  }
}


bool CfgHeuristicSearch::DoSearch(int depth,
				  int iters,
				  int pos,
				  int maxDist,
				  const SymbolicExecution& prev_ex) {

  fprintf(stderr, "DoSearch(%d, %d, %d, %zu)\n",
	  depth, pos, maxDist, prev_ex.path().branches().size());

  if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
    return false;

  if (depth == 0)
    return false;


  // For each symbolic branch/constraint in the execution path, we will
  // compute a heuristic score, and then attempt to force the branches
  // in order of increasing score.
  vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    scoredBranches[i].first = i + pos;
  }

  { // Compute (and sort by) the scores.
    random_shuffle(scoredBranches.begin(), scoredBranches.end());
    map<branch_id_t,int> seen;
    for (size_t i = 0; i < scoredBranches.size(); i++) {
      size_t idx = scoredBranches[i].first;
      size_t branch_idx = prev_ex.path().constraints_idx()[idx];
      branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];

      scoredBranches[i].second = dist_[bid] + seen[bid];
      seen[bid] += 1;
    }
  }
  stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

  // Solve.
  SymbolicExecution cur_ex;
  vector<value_t> input;
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    if ((iters <= 0) || (scoredBranches[i].second > maxDist))
      return false;

    num_inner_solves_ ++;

    if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
      num_inner_unsats_ ++;
      continue;
    }

    RunProgram(input, &cur_ex);
    iters--;

    size_t b_idx = prev_ex.path().constraints_idx()[scoredBranches[i].first];
    branch_id_t bid = paired_branch_[prev_ex.path().branches()[b_idx]];
    set<branch_id_t> new_branches;
    bool found_new_branch = UpdateCoverage(cur_ex, &new_branches);
    bool prediction_failed = !CheckPrediction(prev_ex, cur_ex, b_idx);


    if (found_new_branch && prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(stderr, "Found new branch by forcing at "
	              "distance %zu (%d) [lucky, pred failed].\n",
	      dist_[bid], scoredBranches[i].second);

      // We got lucky, and can't really compute any further stats
      // because prediction failed.
      num_inner_lucky_successes_ ++;
      num_inner_successes_pred_fail_ ++;
      success_ex_.Swap(cur_ex);
      return true;
    }

    if (found_new_branch && !prediction_failed) {
      fprintf(stderr, "Found new branch by forcing at distance %zu (%d).\n",
	      dist_[bid], scoredBranches[i].second);
      size_t min_dist = MinCflDistance(b_idx, cur_ex, new_branches);
      // Check if we were lucky.
          if (FindAlongCfg(b_idx, dist_[bid], cur_ex, new_branches)) {
    	assert(min_dist <= dist_[bid]);
    	// A legitimate find -- return success.
    	if (dist_[bid] == 0) {
    	  num_inner_zero_successes_ ++;
    	} else {
    	  num_inner_nonzero_successes_ ++;
    	}
    	success_ex_.Swap(cur_ex);
    	return true;
      } else {
	// We got lucky, but as long as there were no prediction failures,
	// we'll finish the CFG search to see if that works, too.
	assert(min_dist > dist_[bid]);
	assert(dist_[bid] != 0);
	num_inner_lucky_successes_ ++;
      }
    }

    if (prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      if (!found_new_branch) {
	num_inner_pred_fails_ ++;
	continue;
      }
    }

    // If we reached here, then scoredBranches[i].second is greater than 0.
    num_top_solves_ ++;
    if ((dist_[bid] > 0) &&
        SolveAlongCfg(b_idx, scoredBranches[i].second-1, cur_ex)) {
      num_top_solve_successes_ ++;
      // PrintStats();
      return true;
    }

    if (found_new_branch) {
      success_ex_.Swap(cur_ex);
      return true;
    }

    /*
    if (DoSearch(depth-1, 5, scoredBranches[i].first+1, scoredBranches[i].second-1, cur_ex)) {
      num_inner_recursive_successes_ ++;
      return true;
    }
    */
  }

  return false;
}


size_t CfgHeuristicSearch::MinCflDistance
(size_t i, const SymbolicExecution& ex, const set<branch_id_t>& bs) {

  const vector<branch_id_t>& p = ex.path().branches();

  if (i >= p.size())
    return numeric_limits<size_t>::max();

  if (bs.find(p[i]) != bs.end())
    return 0;

  vector<size_t> stack;
  size_t min_dist = numeric_limits<size_t>::max();
  size_t cur_dist = 1;

  fprintf(stderr, "Found uncovered branches at distances:");
  for (BranchIt j = p.begin()+i+1; j != p.end(); ++j) {
    if (bs.find(*j) != bs.end()) {
      min_dist = min(min_dist, cur_dist);
      fprintf(stderr, " %zu", cur_dist);
    }

    if (*j >= 0) {
      cur_dist++;
    } else if (*j == kCallId) {
      stack.push_back(cur_dist);
    } else if (*j == kReturnId) {
      if (stack.size() == 0)
	break;
      cur_dist = stack.back();
      stack.pop_back();
    } else {
      fprintf(stderr, "\nBad branch id: %d\n", *j);
      exit(1);
    }
  }

  fprintf(stderr, "\n");
  return min_dist;
}

bool CfgHeuristicSearch::FindAlongCfg(size_t i, unsigned int dist,
				      const SymbolicExecution& ex,
				      const set<branch_id_t>& bs) {

  const vector<branch_id_t>& path = ex.path().branches();

  if (i >= path.size())
    return false;

  branch_id_t bid = path[i];
  if (bs.find(bid) != bs.end())
    return true;

  if (dist == 0)
    return false;

  // Compute the indices of all branches on the path that immediately
  // follow the current branch (corresponding to the i-th constraint)
  // in the CFG. For example, consider the path:
  //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
  // where '*' is the current branch.  The branches immediately
  // following '*' are : 1, 4, 5, 8, and 9.
  vector<size_t> idxs;
  { size_t pos = i + 1;
    CollectNextBranches(path, &pos, &idxs);
  }

  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
    if (FindAlongCfg(*j, dist-1, ex, bs))
      return true;
  }

  return false;
}


bool CfgHeuristicSearch::SolveAlongCfg(size_t i, unsigned int max_dist,
				       const SymbolicExecution& prev_ex) {
  num_solves_ ++;

  fprintf(stderr, "SolveAlongCfg(%zu,%u)\n", i, max_dist);
  SymbolicExecution cur_ex;
  vector<value_t> input;
  const vector<branch_id_t>& path = prev_ex.path().branches();

  // Compute the indices of all branches on the path that immediately
  // follow the current branch (corresponding to the i-th constraint)
  // in the CFG. For example, consider the path:
  //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
  // where '*' is the current branch.  The branches immediately
  // following '*' are : 1, 4, 5, 8, and 9.
  bool found_path = false;
  vector<size_t> idxs;
  { size_t pos = i + 1;
    CollectNextBranches(path, &pos, &idxs);
     fprintf(stderr, "Branches following %d:", path[i]);
    for (size_t j = 0; j < idxs.size(); j++) {
       fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
            dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
      if ((dist_[path[idxs[j]]] <= max_dist)
	  || (dist_[paired_branch_[path[idxs[j]]]] <= max_dist))
	found_path = true;
    }
    fprintf(stderr, "\n");
  }

  if (!found_path) {
    num_solve_no_paths_ ++;
    return false;
  }

  bool all_concrete = true;
  num_solve_all_concrete_ ++;

  // We will iterate through these indices in some order (random?
  // increasing order of distance? decreasing?), and try to force and
  // recurse along each one with distance no greater than max_dist.
  random_shuffle(idxs.begin(), idxs.end());
  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
    // Skip if distance is wrong.
    if ((dist_[path[*j]] > max_dist)
	&& (dist_[paired_branch_[path[*j]]] > max_dist)) {
      continue;
    }

    if (dist_[path[*j]] <= max_dist) {
      // No need to force, this branch is on a shortest path.
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, max_dist-1, prev_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }

    // Find the constraint corresponding to branch idxs[*j].
    vector<size_t>::const_iterator idx =
      lower_bound(prev_ex.path().constraints_idx().begin(),
		  prev_ex.path().constraints_idx().end(), *j);
    if ((idx == prev_ex.path().constraints_idx().end()) || (*idx != *j)) {
      fprintf(stderr, "branch is concrete\n");
      continue;  // Branch is concrete.
    }
    size_t c_idx = idx - prev_ex.path().constraints_idx().begin();

    if (all_concrete) {
      all_concrete = false;
      num_solve_all_concrete_ --;
    }

    if(dist_[paired_branch_[path[*j]]] <= max_dist) {
      num_solve_sat_attempts_ ++;
      // The paired branch is along a shortest path, so force.
      if (!SolveAtBranch(prev_ex, c_idx, &input)) {
	num_solve_unsats_ ++;
	continue;
      }
      RunProgram(input, &cur_ex);
      if (UpdateCoverage(cur_ex)) {
	num_solve_successes_ ++;
	success_ex_.Swap(cur_ex);
	return true;
      }
      if (!CheckPrediction(prev_ex, cur_ex, *j)) {
	num_solve_pred_fails_ ++;
	continue;
      }

      // Recurse.
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, max_dist-1, cur_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }
  }

  return false;
}

void CfgHeuristicSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
  while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
    if (path[*pos] == kCallId) {
      (*pos)++;
      SkipUntilReturn(path, pos);
      if (*pos >= path.size())
	return;
      assert(path[*pos] == kReturnId);
    }
    (*pos)++;
  }
}

void CfgHeuristicSearch::CollectNextBranches
(const vector<branch_id_t>& path, size_t* pos, vector<size_t>* idxs) {
  // fprintf(stderr, "Collect(%u,%u,%u)\n", path.size(), *pos, idxs->size());

  // Eat an arbitrary sequence of call-returns, collecting inside each one.
  while ((*pos < path.size()) && (path[*pos] == kCallId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
    SkipUntilReturn(path, pos);
    if (*pos >= path.size())
      return;
    assert(path[*pos] == kReturnId);
    (*pos)++;
  }

  // If the sequence of calls is followed by a branch, add it.
  if ((*pos < path.size()) && (path[*pos] >= 0)) {
    idxs->push_back(*pos);
    (*pos)++;
    return;
  }

  // Alternatively, if the sequence is followed by a return, collect the branches
  // immediately following the return.
  /*
  if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
  }
  */
}


bool CfgHeuristicSearch::DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex) {
  if (depth <= 0)
    return false;

  fprintf(stderr, "%d (%d: %d) (%d: %d)\n", depth,
          i-1, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i-1]],
          i, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i]]);

  SymbolicExecution cur_ex;
  vector<value_t> input;
  const vector<SymbolicPred*>& constraints = prev_ex.path().constraints();
  for (size_t j = static_cast<size_t>(i); j < constraints.size(); j++) {
    if (!SolveAtBranch(prev_ex, j, &input)) {
      continue;
    }

    RunProgram(input, &cur_ex);
    iters_left_--;
    if (UpdateCoverage(cur_ex)) {
      success_ex_.Swap(cur_ex);
      return true;
    }

    if (!CheckPrediction(prev_ex, cur_ex, prev_ex.path().constraints_idx()[j])) {
      fprintf(stderr, "Prediction failed!\n");
      continue;
    }

    return (DoBoundedBFS(j+1, depth-1, cur_ex)
	    || DoBoundedBFS(j+1, depth-1, prev_ex));
  }

  return false;
}

////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomSearch::RandomSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomSearch::~RandomSearch() { }

void RandomSearch::Run() {
  SymbolicExecution next_ex;

  while (true) {
    // Execution (on empty/random inputs).
    fprintf(stderr, "RESET\n");
    ResetInitialInputFiles();
    vector<value_t> next_input;
    RunProgram(next_input, &ex_);
    UpdateCoverage(ex_);

    // Do some iterations.
    int count = 0;
    while (count++ < 10000) {
      // fprintf(stderr, "Uncovered bounded DFS.\n");
      // SolveUncoveredBranches(0, 20, ex_);

      size_t idx;
      if (SolveRandomBranch(&next_input, &idx)) {
	RunProgram(next_input, &next_ex);
	bool found_new_branch = UpdateCoverage(next_ex);
	bool prediction_failed =
	  !CheckPrediction(ex_, next_ex, ex_.path().constraints_idx()[idx]);

	if (found_new_branch) {
	  count = 0;
	  ex_.Swap(next_ex);
	  if (prediction_failed)
	    fprintf(stderr, "Prediction failed (but got lucky).\n");
	} else if (!prediction_failed) {
	  ex_.Swap(next_ex);
	} else {
	  fprintf(stderr, "Prediction failed.\n");
	}
      }
    }
  }
}

  /*
bool RandomSearch::SolveUncoveredBranches(SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;
  bool success = false;
  int cnt = 0;
  for (size_t i = 0; i < prev_ex.path().constraints().size(); i++) {
    size_t bid_idx = prev_ex.path().constraints_idx()[i];
    branch_id_t bid = prev_ex.path().branches()[bid_idx];
    if (covered_[paired_branch_[bid]])
      continue;
    if (!SolveAtBranch(prev_ex, i, &input)) {
      if (++cnt == 1000) {
	cnt = 0;
	fprintf(stderr, "Failed to solve at %u/%u.\n",
		i, prev_ex.path().constraints().size());
      }
      continue;
    }
    cnt = 0;
    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);
    if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
      fprintf(stderr, "Prediction failed.\n");
      continue;
    }
    success = true;
    cur_ex.Swap(prev_ex);
  }
  return success;
}
  */

void RandomSearch::SolveUncoveredBranches(size_t i, int depth,
					  const SymbolicExecution& prev_ex) {
  if (depth < 0)
    return;

  fprintf(stderr, "position: %zu/%zu (%d)\n",
	  i, prev_ex.path().constraints().size(), depth);

  SymbolicExecution cur_ex;
  vector<value_t> input;

  int cnt = 0;

  for (size_t j = i; j < prev_ex.path().constraints().size(); j++) {
    size_t bid_idx = prev_ex.path().constraints_idx()[j];
    branch_id_t bid = prev_ex.path().branches()[bid_idx];
    if (covered_[paired_branch_[bid]])
      continue;

    if (!SolveAtBranch(prev_ex, j, &input)) {
      if (++cnt == 1000) {
	cnt = 0;
	fprintf(stderr, "Failed to solve at %zu/%zu.\n",
		j, prev_ex.path().constraints().size());
      }
      continue;
    }
    cnt = 0;

    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);
    if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
      fprintf(stderr, "Prediction failed.\n");
      continue;
    }

    SolveUncoveredBranches(j+1, depth-1, cur_ex);
  }
  }


  bool RandomSearch::SolveRandomBranch(vector<value_t>* next_input, size_t* idx) {
    vector<size_t> idxs(ex_.path().constraints().size());
      for (size_t i = 0; i < idxs.size(); i++)
      idxs[i] = i;

    for (int tries = 0; tries < 1000; tries++) {
      // Pick a random index.
      if (idxs.size() == 0)
        break;
      size_t r = rand() % idxs.size();
      size_t i = idxs[r];
      swap(idxs[r], idxs.back());
      idxs.pop_back();

      if (SolveAtBranch(ex_, i, next_input)) {
        fprintf(stderr, "Solved %zu/%zu\n", i, idxs.size());
        *idx = i;
        return true;
      }
    }

    // We failed to solve a branch, so reset the input.
    fprintf(stderr, "FAIL\n");
    next_input->clear();
    return false;
  }


  ////////////////////////////////////////////////////////////////////////
  //// RandomMDSearch ////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////

  size_t RandomMDSearch::AssignEnergy(EXContext &c) {
     size_t energy = 0;
     set<branch_id_t> all_branches;
     for(const size_t &i : c.ex->path().constraints_idx()) {
       branch_id_t b = c.ex->path().branches()[i];
       all_branches.insert(b);
     }
     for(const branch_id_t &t : all_branches) {
       branch_id_t b= paired_branch_[t];
         energy += 10 - min(pf_count_[paired_branch_[b]],(size_t) 10);
         // if(!covered_[b]) {
         // energy += 10 - min(unsat_count_[paired_branch_[b]],(size_t) 10);
       // }
     }
    energy = std::max(energy,(size_t) 10);
    energy = std::min(energy, (size_t)300);
     fprintf(stderr, "Energy is %u\n",energy);
     return  energy;
  }

void RandomMDSearch::Run() {
    size_t idx = 0;
    while(true) {
        fprintf(stderr, "RESET");
        ResetInitialInputFiles();

        SymbolicExecution *next_ex = new SymbolicExecution();
        vector<value_t> next_input;
        ResetInitialInputFiles();
        covered_.assign(max_branch_, false);
        reachable_branches_set_.clear();
        covered_branches_.clear();
        F.clear();

        RunProgram(next_input, next_ex);
        set<branch_id_t> uncovered_branches;
        for (const size_t &i: next_ex->path().constraints_idx()) {
            // covered_branches_.insert(next_ex->path().branches()[i]);
            uncovered_branches.insert(paired_branch_[next_ex->path().branches()[i]]);
        }

        SymbolicExecution *new_ex = new SymbolicExecution();
        next_ex->clone(*new_ex);
        Q.push_back(EXContext(new_ex, uncovered_branches));

        if(UpdateCoverage(*new_ex, Q.front())) {
            fprintf(stderr, "found new branch \n");
        }
        // size_t count = 0;
        // while (count++ < 10000) {
        while (Q.size()!= 0) {
          fprintf(stderr,"Q size %zu\n", Q.size());
            EXContext c = Q.front();
            Q.pop_front();
            if(c.count >= 10000) {
              fprintf(stderr, "c.count >= 10000 (fail)\n");
              F.insert(c.target_branches.begin(), c.target_branches.end());
              delete c.ex;
              continue;
            }
            set<branch_id_t> cur_target_branches;
            set_difference(
                    c.target_branches.begin(),
                    c.target_branches.end(),
                    covered_branches_.begin(),
                    covered_branches_.end(),
                    std::inserter(cur_target_branches,cur_target_branches.end())
                    );
            fprintf(stderr,"cur_target_branches size %zu\n", cur_target_branches.size());
            if(cur_target_branches.empty()) {
                fprintf(stderr,"Q size %zu\n", Q.size());
                delete c.ex;
                continue;
            }

            SymbolicExecution *ex = new SymbolicExecution();
            c.ex->clone(*ex);

            bool search_failed = false;
            for(size_t i = 200; i > 0 && c.count < 10000; i--) {
              fprintf(stderr, "i : %u\n",i);
                if (SolveRandomBranch(*ex, &next_input, &idx)) {
                    RunProgram(next_input, next_ex);
                    if(UpdateCoverage(*next_ex, c)) {
                        fprintf(stderr, "found new branch \n");
                        c.count=0;
                    } else {
                      c.count++;
                    }
                    fprintf(stderr,"c.count : %zu\n", c.count);

                    if(!CheckPrediction(*ex, *next_ex, ex->path().constraints_idx()[idx]) ) {
                        // pf_count_[c.ex.path().branches()[c.ex.path().constraints_idx()[idx]]]++;
                        fprintf(stderr, "Prediction Failure!\n");
                    }
                    set<branch_id_t> current_uncovered_branches;
                    for (const size_t &i: next_ex->path().constraints_idx()) {
                        branch_id_t b = next_ex->path().branches()[i];
                        if(!covered_[paired_branch_[b]]) {
                            current_uncovered_branches.insert(paired_branch_[b]);
                        }
                    }
                    set<branch_id_t> u = current_uncovered_branches;
                    // set_difference(
                    //         current_uncovered_branches.begin(),
                    //         current_uncovered_branches.end(),
                    //         c.target_branches.begin(),
                    //         c.target_branches.end(),
                    //         std::inserter(u,u.end())
                    //         );
                    set<branch_id_t> tmp;
                    for(const EXContext &cc: Q) {
                      tmp.clear();
                      set_difference(
                              u.begin(),
                              u.end(),
                              cc.target_branches.begin(),
                              cc.target_branches.end(),
                              std::inserter(tmp,tmp.end())
                              );
                      u = tmp;
                    }
                    // set<branch_id_t> tmp;
                    tmp.clear();
                    set_difference(
                            u.begin(),
                            u.end(),
                            F.begin(),
                            F.end(),
                            std::inserter(tmp,tmp.end())
                            );
                    u = tmp;
                    if(u.size() > 0 ) {
                        fprintf(stderr ,"uncovered branches size : %zu\n", u.size());
                        SymbolicExecution *new_ex = new SymbolicExecution();
                        next_ex->clone(*new_ex);
                        Q.push_back(EXContext(new_ex, u));
                    }
                    SymbolicExecution *pe = ex;
                    ex = next_ex;
                    next_ex = pe;
                } else {
                    search_failed = true;
                    break;
                }
            }
            delete ex;

            set<branch_id_t> u;
            set_difference(
                    c.target_branches.begin(),
                    c.target_branches.end(),
                    covered_branches_.begin(),
                    covered_branches_.end(),
                    std::inserter(u,u.end())
                    );
            set<branch_id_t> tmp;
            for(const EXContext &cc: Q) {
              tmp.clear();
                set_difference(
                        u.begin(),
                        u.end(),
                        cc.target_branches.begin(),
                        cc.target_branches.end(),
                        std::inserter(tmp,tmp.end())
                        );
                u = tmp;
            }
            if(search_failed) {
              fprintf(stderr, "search failed\n");
              F.insert(c.target_branches.begin(), c.target_branches.end());
              delete c.ex;
            } else if ( u.empty() ) {
              fprintf(stderr, "target branch is empty\n");
              delete c.ex;
            } else {
              Q.push_back(EXContext(c.ex, u,c.count));
            }
        }
        delete next_ex;
    }
}

  bool RandomMDSearch::SolveRandomBranch(SymbolicExecution &ex, vector<value_t>* next_input, size_t* idx) {
    vector<size_t> idxs(ex.path().constraints().size());
    for (size_t i = 0; i < idxs.size(); i++)
      idxs[i] = i;

    for (int tries = 0; tries < 1000; tries++) {
      // Pick a random index.
      if (idxs.size() == 0)
        break;
      size_t r = rand() % idxs.size();
      size_t i = idxs[r];
      swap(idxs[r], idxs.back());
      idxs.pop_back();

      if (SolveAtBranch(ex, i, next_input)) {
        fprintf(stderr, "Solved %zu/%zu\n", i+1, ex.path().constraints().size());
        *idx = i;
        return true;
      }
    }

    // We failed to solve a branch, so reset the input.
    fprintf(stderr, "FAIL\n");
    next_input->clear();
    return false;
  }

  ////////////////////////////////////////////////////////////////////////
  //// CfgHeuristicMDSearch //////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////
/*
  size_t CfgHeuristicMDSearch::AssignEnergy(Context &c) {
      size_t energy = 0;
      set<branch_id_t> all_branches;
      for(const size_t &i : c.cur_ex.path().constraints_idx()) {
        branch_id_t b = c.cur_ex.path().branches()[i];
        all_branches.insert(b);
      }
      for(const branch_id_t &t : all_branches) {
        branch_id_t b= paired_branch_[t];
        if(!covered_[b]) {
          energy += 10 - min(pf_count_[paired_branch_[b]],(size_t) 10);
          // if(covered_[paired_branch_[b]]) {
            // energy += 10;
          // } else {
            energy += 10 - min(unsat_count_[paired_branch_[b]],(size_t) 10);
          // }
        }
      }
     energy = std::max(energy,(size_t) 10);
     energy = std::min(energy, (size_t)300);
  fprintf(stderr, "Energy is %u\n", energy);

     return  energy;
  }
*/
  CfgHeuristicMDSearch::CfgHeuristicMDSearch(const string& program, int max_iterations) : Search(program, max_iterations),
      cfg_(max_branch_), cfg_rev_(max_branch_), dist_notusing(max_branch_) {
    cur_ex_ = new SymbolicExecution();
    // Read in the CFG.
    ifstream in("cfg_branches", ios::in | ios::binary);
    assert(in);
    size_t num_branches;
    in.read((char*)&num_branches, sizeof(num_branches));
    assert(num_branches == branches_.size());
    for (size_t i = 0; i < num_branches; i++) {
      branch_id_t src;
      size_t len;
      in.read((char*)&src, sizeof(src));
      in.read((char*)&len, sizeof(len));
      cfg_[src].resize(len);
      in.read((char*)&cfg_[src].front(), len * sizeof(branch_id_t));
    }
    in.close();

    // Construct the reversed CFG.
    for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
      for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
        cfg_rev_[*j].push_back(*i);
      }
    }
  }

  CfgHeuristicMDSearch::~CfgHeuristicMDSearch() {
    delete cur_ex_;
   }

  void CfgHeuristicMDSearch::UpdateCurContext() {
    fprintf(stderr, "Size of Q : %u\n", Q.size());
    fprintf(stderr, "cur energy : %u\n", Q.front().energy);
    // assert(Q.size()!=0);
    if( Q.front().energy > 0) {
      --Q.front().energy;
    } else {
      if(Q.front().is_do_search_failed) {
        F.insert(Q.front().target_branches.begin(), Q.front().target_branches.end());
        Q.pop_front();
      } else {
        // only when search is not failed
        set<branch_id_t> target_branches;
        set_difference(
          cur_target_branches_.begin(),
          cur_target_branches_.end(),
          covered_branches_.begin(),
          covered_branches_.end(),
          std::inserter(target_branches,target_branches.end())
        );
        set<branch_id_t> u = target_branches;
        set<branch_id_t> tmp;
        for(size_t i = 1 ; i < Q.size(); i++) {
          tmp.clear();
          Context &cc = Q[i];
          set_difference(
            u.begin(),
            u.end(),
            cc.target_branches.begin(),
            cc.target_branches.end(),
            std::inserter(tmp,tmp.end())
          );
          u = tmp;
        }
        tmp.clear();
        set_difference(
                u.begin(),
                u.end(),
                F.begin(),
                F.end(),
                std::inserter(tmp,tmp.end())
                );
        u = tmp;

        if(u.empty()) {
          Q.pop_front();
        } else {
          Q.emplace_back();
          cur_ex_->clone(*Q.back().cur_ex);
          Q.back().iters = Q.front().iters;
          Q.back().covered = covered_;
          Q.back().dist.resize(max_branch_, 0);
          Q.back().target_branches = u;
          Q.pop_front();
        }
      }
      while (Q.size()!=0) {
        set<branch_id_t> target_branches;
        set_difference(
          Q.front().target_branches.begin(),
          Q.front().target_branches.end(),
          covered_branches_.begin(),
          covered_branches_.end(),
          std::inserter(target_branches,target_branches.end())
        );
        if(target_branches.empty()) {
          Q.pop_front();
          continue;
        }
        Q.front().target_branches = target_branches;
        delete cur_ex_;
        cur_ex_ = new SymbolicExecution();
        Q.front().cur_ex->clone(*cur_ex_);
        Q.front().energy = 200;
        Q.front().num_covered = num_covered_;
        Q.front().covered = covered_;
        UpdateBranchDistances(Q.front().covered, Q.front().dist);
        return;
      }
    }
  }

  void CfgHeuristicMDSearch::GetNewTargetBranches(SymbolicExecution &next_ex,set<branch_id_t> &u){
    // auto start = std::chrono::high_resolution_clock::now();
    set<branch_id_t> current_uncovered_branches;
    // {bar(b)|b\inB'} - C
    for (const size_t &i: next_ex.path().constraints_idx()) {
      branch_id_t b = next_ex.path().branches()[i];
      if(!covered_[paired_branch_[b]]) {
        u.insert(paired_branch_[b]);
      }
    }
    // fprintf(stderr, "u\n");
    // for(branch_id_t b : u) {
    //     fprintf(stderr, "%d ", b);
    // }
    // fprintf(stderr, "\n");
    // fprintf(stderr, "u size %zu\n", u.size());
    // // T' <- {t\inT''| (phi'',T'')\in Q}
    set<branch_id_t> tmp;
    for(size_t i = 1; i < Q.size(); i++) {
      Context &c = Q[i];
      tmp.clear();
      set_difference(
         u.begin(),
         u.end(),
         c.target_branches.begin(),
         c.target_branches.end(),
         std::inserter(tmp,tmp.end())
        );
        u = tmp;
    }
    tmp.clear();
    set_difference(
            u.begin(),
            u.end(),
            F.begin(),
            F.end(),
            std::inserter(tmp,tmp.end())
            );
    u = tmp;
    // fprintf(stderr, "NewTargetBranches\n");
    // for(branch_id_t b : u) {
    //     fprintf(stderr, "%u ", b);
    // }
    // fprintf(stderr, "\n");
  }

  void CfgHeuristicMDSearch::Run() {
    num_covered_ = 0;
    covered_.resize(max_branch_, false);
    max_Q_size = 0;
    while(true) {
      {
        if (Q.empty()) {
          fprintf(stderr, "RESET Search\n");
          ResetInitialInputFiles();
          num_no_target_contexts_ = 0;
          Q = deque<Context>();
          F.clear();
          covered_branches_.clear();
          covered_.assign(max_branch_, false);
          Q.emplace_back();
          Context &new_context = Q.front();
          new_context.covered.resize(max_branch_, false);
          new_context.dist.resize(max_branch_, 0);
          RunProgram(vector<value_t>(), new_context.cur_ex);
          // fprintf(stderr, "Uncovered Branch:\n");
          UpdateCoverage(*new_context.cur_ex, new_context);
          for (const size_t &i: new_context.cur_ex->path().constraints_idx()) {
              branch_id_t b = new_context.cur_ex->path().branches()[i];
              if(!covered_[paired_branch_[b]]) {
                new_context.target_branches.insert(paired_branch_[b]);
                // fprintf(stderr, "%d ", paired_branch_[b]);
              }
          }
          // fprintf(stderr, "\n");
          cur_target_branches_ = new_context.target_branches;
          delete cur_ex_;
          cur_ex_ = new SymbolicExecution();
          new_context.cur_ex->clone(*cur_ex_);
          UpdateBranchDistances(new_context.covered, new_context.dist);
          UpdateCurContext();

        }
        // fprintf(stderr, "Q.iters = %u\n",Q.front().iters);
        if(Q.front().stack_sub_context.empty()) {
          if(DoSearchOnce()) {
            SymbolicExecution *tmp = Q.front().latest_success_ex;
            Q.front().latest_success_ex = Q.front().cur_ex;
            Q.front().cur_ex = tmp;
            Q.front().iters=30;
            Q.front().cur_idx = 0;
            Q.front().scoredBranches.clear();
            Q.front().do_search_once_found_new_branch = false;
            Q.front().new_branches.clear();
            Q.front().covered = covered_;
            UpdateBranchDistances(Q.front().covered, Q.front().dist);
            UpdateCurContext();

          } else {
            // 1. 새로운 브랜치를 못찾고, prediction failure
            // 2. FindAlongCfg 성공후 stack에 추가
            // 3. Do search fail ( execution 종료)
            if (Q.front().is_do_search_failed) {
              Q.front().energy =0;
              fprintf(stderr, "Search is failed. pop\n");
              // Q.pop_front();
              UpdateCurContext();
            }
          }
          // auto end = std::chrono::high_resolution_clock::now();
          // elapsed_time_searching_4_ += (end - start);
          // fprintf(stderr, "elapsed_time_searching_4(DoSearch): %.2f\n", elapsed_time_searching_4_ );
        } else {
          // fprintf(stderr,"stack is not empty\n");

          if(!SolveOnePathAlongCfg()) {
            if(!Q.front().stack_sub_context.empty()) {
                // Keep solve one path along cfg
                UpdateCurContext();
            } else { // stack is empty
              if(Q.front().do_search_once_found_new_branch) {
                 Q.front().covered = covered_;
                 UpdateBranchDistances(Q.front().covered, Q.front().dist);
                 SymbolicExecution *tmp = Q.front().cur_ex;
                 Q.front().cur_ex = Q.front().latest_success_ex;
                 Q.front().latest_success_ex = tmp;
                 Q.front().new_branches.clear();
                 Q.front().scoredBranches.clear();
                 Q.front().iters=30;
                 Q.front().cur_idx = 0;
                 UpdateCurContext();
              } else {
                Q.front().cur_idx++;
                UpdateCurContext();
              }
              Q.front().do_search_once_found_new_branch = false;
            }
          } else {
            // Solve One Path Along Cfg Success
            // We empty the stack
            std::stack<SubContext*> &stack = Q.front().stack_sub_context;
            while(!stack.empty()) {
              delete stack.top();
              stack.pop();
            }

            UpdateBranchDistances(Q.front().covered, Q.front().dist);
            // Q[context_idx_].cur_ex.Swap(Q[context_idx_].latest_success_ex);
            SymbolicExecution *tmp = Q.front().cur_ex;
            Q.front().cur_ex = Q.front().latest_success_ex;
            Q.front().latest_success_ex = tmp;
            Q.front().scoredBranches.clear();
            Q.front().new_branches.clear();
            Q.front().cur_idx = 0;
            Q.front().iters=30;
            UpdateCurContext();
          }
        }
      }
    }
  }


  void CfgHeuristicMDSearch::UpdateBranchDistances(vector<bool>& covered, vector<long unsigned int>& dist) {
    // We run a BFS backward, starting simultaneously at all uncovered vertices.
    // fprintf(stderr, "covered size: %u, dist size %u", covered.size(), dist.size());
    // auto start = std::chrono::high_resolution_clock::now();
    queue<branch_id_t> Q;
    for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
      if (!covered[*i]) {
        dist[*i] = 0;
        Q.push(*i);
      } else {
        dist[*i] = kInfiniteDistance;
      }
    }

    while (!Q.empty()) {
      branch_id_t i = Q.front();
      size_t dist_i = dist[i];
      Q.pop();

      for (BranchIt j = cfg_rev_[i].begin(); j != cfg_rev_[i].end(); ++j) {
        if (dist_i + 1 < dist[*j]) {
  	dist[*j] = dist_i + 1;
  	Q.push(*j);
        }
      }
    }

  }

  bool CfgHeuristicMDSearch::DoSearchOnce() {
    if(Q.front().scoredBranches.empty()) {
      // fprintf(stderr, "scoredBranches is empty\n");
      // auto start = std::chrono::high_resolution_clock::now();
      Q.front().covered = covered_;
      Q.front().scoredBranches.resize(Q.front().cur_ex->path().constraints().size());
      for (size_t i = 0; i < Q.front().scoredBranches.size(); i++) {
        Q.front().scoredBranches[i].first = i;
      }

      { // Compute (and sort by) the scores.
         // fprintf(stderr,"start computing scores\n");
        random_shuffle(Q.front().scoredBranches.begin(), Q.front().scoredBranches.end());
        map<branch_id_t,int> seen;
        for (size_t i = 0; i < Q.front().scoredBranches.size(); i++) {
          // fprintf(stderr, "%u ", i);
          size_t idx = Q.front().scoredBranches[i].first;

          size_t branch_idx = Q.front().cur_ex->path().constraints_idx()[idx];

          branch_id_t bid = paired_branch_[Q.front().cur_ex->path().branches()[branch_idx]];
          Q.front().scoredBranches[i].second = Q.front().dist[bid] + seen[bid];
          seen[bid] += 1;
        }
      }
      // fprintf(stderr, "\n");

      stable_sort(Q.front().scoredBranches.begin(), Q.front().scoredBranches.end(), ScoredBranchComp());
    }

    // Solve.
    SymbolicExecution new_ex;
    vector<value_t> input;
    // for (size_t i = 0; i < scoredBranches.size(); i++) {
    while(Q.front().cur_idx < Q.front().scoredBranches.size()) {

      if ((Q.front().iters <= 0) ||
       (Q.front()
         .scoredBranches[Q.front().cur_idx]
         .second > kInfiniteDistance)) {
            Q.front().is_do_search_failed = true;

            return false;
      }
      num_inner_solves_ ++;

      if (!SolveAtBranch(*Q.front().cur_ex, Q.front().scoredBranches[Q.front().cur_idx].first, &input)) { // Unsat

        Q.front().cur_idx++;
        continue;
      }
      RunProgram(input, &new_ex);
      Q.front().iters--;

      size_t b_idx = Q.front().cur_ex->path().constraints_idx()[Q.front().scoredBranches[Q.front().cur_idx].first];
      branch_id_t bid = paired_branch_[Q.front().cur_ex->path().branches()[b_idx]];
      bool found_new_branch = UpdateCoverage(new_ex, &(Q.front().new_branches), Q.front());
      set<branch_id_t> new_target_branches;
      GetNewTargetBranches(new_ex, new_target_branches);
      if(!new_target_branches.empty()) {
          Q.emplace_back();
          Q.back().target_branches = new_target_branches;
          Q.front().clone(Q.back());
          fprintf(stderr, "new branch size is %zu\n",Q.front().target_branches.size());
      }
      bool prediction_failed = !CheckPrediction(*Q.front().cur_ex, new_ex, b_idx);
      if (found_new_branch && prediction_failed) {
        num_inner_lucky_successes_ ++;
        num_inner_successes_pred_fail_ ++;
        // new_ex.clone(*Q.front().latest_success_ex);
        Q.front().latest_success_ex->Swap(new_ex);
        return true;
      }
      if (found_new_branch && !prediction_failed) {
        size_t min_dist = MinCflDistance(b_idx, new_ex, Q.front().new_branches);
        if (FindAlongCfg(b_idx, Q.front().dist[bid], new_ex, Q.front().new_branches)) {
        	assert(min_dist <= Q.front().dist[bid]);
        	if (Q.front().dist[bid] == 0) {
        	  num_inner_zero_successes_ ++;
        	} else {
        	  num_inner_nonzero_successes_ ++;
        	}
          new_ex.Swap(*Q.front().latest_success_ex);
          // delete Q.front().latest_success_ex;
          // Q.front().latest_success_ex = new SymbolicExecution();
          // new_ex.clone(*Q.front().latest_success_ex);
        	// Q[context_idx_].latest_success_ex.Swap(new_ex);
        	return true;
        } else {
        	// We got lucky, but as long as there were no prediction failures,
        	// we'll finish the CFG search to see if that works, too.
        	assert(min_dist > Q.front().dist[bid]);
        	assert(Q.front().dist[bid] != 0);
        	num_inner_lucky_successes_ ++;
        }
      }
      if (prediction_failed) {
        fprintf(stderr, "Prediction failed.\n");
        if (!found_new_branch) {
  	      num_inner_pred_fails_ ++;
           Q.front().cur_idx++;
           UpdateCurContext();
           return false;
        }
      }
      num_top_solves_ ++;
      num_top_solve_successes_ ++;
      // Q[context_idx_].stack_sub_context.push(SubContext(b_idx, Q[context_idx_].scoredBranches[Q[context_idx_].cur_idx].second -1));
      Q.front().stack_sub_context.push(new SubContext(b_idx, Q.front().scoredBranches[Q.front().cur_idx].second -1, &new_ex));
      // new_ex.clone((Q[context_idx_].stack_sub_context.top().cur_ex));
      if (found_new_branch) {
        new_ex.Swap(*Q.front().latest_success_ex);
        // new_ex.clone(*Q.front().latest_success_ex);
        // Q[context_idx_].latest_success_ex.Swap(new_ex);
        Q.front().do_search_once_found_new_branch = true;
      } else {
        Q.front().do_search_once_found_new_branch = false;
      }
      return false;
    }
    // context.is_reset = true;
    // fprintf(stderr,"set context[%d]'s is_dosearch filed true",input_file_idx_);
    Q.front().is_do_search_failed = true;
    return false;
  }


  bool CfgHeuristicMDSearch::SolveOnePathAlongCfg() {
    // Context &context = Q[context_idx_];
    stack<SubContext*>&stack = Q.front().stack_sub_context;
    vector<value_t> input;
    while(!stack.empty()) {
      SubContext& sc = *(stack.top());
      vector<branch_id_t> path = sc.cur_ex->path().branches();
      // fprintf(stderr, "stack size : %u\n",stack.size());
      // fprintf(stderr, "cur_ex constraints size : %u\n", sc.cur_ex.path().constraints().size());
      // fprintf(stderr, "cur_idx : %u\n",sc.cur_idx);
      // fprintf(stderr, "next idxs size : %u\n",sc.idxs.size());
      // fprintf(stderr, "sc.b_idx : %u\n", sc.b_idx);
      // fprintf(stderr, "dist : %u\n",sc.dist);

      if(sc.idxs.empty()) { // idxs empty means next branches are not found
        bool found_path = false;
        {
          size_t pos = sc.cur_idx + 1;
          CollectNextBranches(path, &pos, &sc.idxs);
          // fprintf(stderr, "Branches following %d:", path[sc.cur_idx]);
          for (size_t j = 0; j < sc.idxs.size(); j++) {
            //    fprintf(stderr, " %d(%u,%u,%u)", path[sc.idxs[j]], sc.idxs[j],
            //       context.dist[path[sc.idxs[j]]], context.dist[paired_branch_[path[sc.idxs[j]]]]);
            if ((Q.front().dist[path[sc.idxs[j]]] <= sc.dist)
                || (Q.front().dist[paired_branch_[path[sc.idxs[j]]]] <= sc.dist))
              found_path = true;
          }
           //  fprintf(stderr, "\n");
        }

        if (!found_path) {
          delete stack.top();
          stack.pop();
          if(!stack.empty()) {
            // never use sc it's evil!
            stack.top()->b_idx++;
          }
          continue;
        }

        // We will iterate through these indices in some order (random?
        // increasing order of distance? decreasing?), and try to force and
        // recurse along each one with distance no greater than max_dist.
        random_shuffle(sc.idxs.begin(), sc.idxs.end());
        for(int i = 0 ;i  < sc.idxs.size(); i++) {
          // fprintf(stderr,"idxs[%d]:%d\n", i, sc.idxs[i]);
        }
      } else if (sc.idxs.size() > 0 && sc.b_idx < sc.idxs.size()) {
        // point next index
        if((Q.front().dist[path[sc.idxs[sc.b_idx]]] > sc.dist && (Q.front().dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] > sc.dist))) {
            // fprintf(stderr, "dist_[%d](%u) > sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);
            sc.b_idx++;
            continue;
        }

        if (Q.front().dist[path[sc.idxs[sc.b_idx]]] <= sc.dist ) {
            // fprintf(stderr, "dist_[%d](%u) <= sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);

              if(sc.seen.find(sc.b_idx)== sc.seen.end()) {
                // fprintf(stderr,"not seen %d,push \n", sc.b_idx);
                sc.seen.insert(sc.b_idx);
                  // stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist -1 ));
                  stack.push(new SubContext(sc.idxs[sc.b_idx], sc.dist -1, sc.cur_ex));
                  // sc.cur_ex.clone(stack.top().cur_ex);
                  continue;
             //   }
              }
        }

        // Find the constraint corresponding to branch idxs[*j].
        SymbolicExecution new_ex;
        // fprintf(stderr, "sc.idxs[%d]:%d\n",sc.b_idx, sc.idxs[sc.b_idx]);
        vector<size_t>::const_iterator idx =
          lower_bound( sc.cur_ex->path().constraints_idx().begin(),
           sc.cur_ex->path().constraints_idx().end(), sc.idxs[sc.b_idx]);
        for(int i = 0 ; i <  sc.cur_ex->path().constraints_idx().size(); i++) {
          // fprintf(stderr, " constraint[%d] = %d\n", i, sc.cur_ex.path().constraints_idx()[i]);
        }
        if ((idx ==  sc.cur_ex->path().constraints_idx().end()) || (*idx != sc.idxs[sc.b_idx])) {
          // fprintf(stderr, "branch is concrete\n");
          sc.b_idx++;
          continue;  // Branch is concrete.
        }
           // fprintf(stderr, "branch is not concrete\n");
        size_t c_idx = idx -  sc.cur_ex->path().constraints_idx().begin();
        if(Q.front().dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] <= sc.dist) {
          if (!SolveAtBranch(*sc.cur_ex, c_idx, &input)) {
            sc.b_idx++;
            continue;
          }
          RunProgram(input, &new_ex);
          bool found_new_branch = UpdateCoverage(new_ex, Q.front());
          //
          set<branch_id_t> new_target_branches;
          GetNewTargetBranches(new_ex, new_target_branches);
          if(!new_target_branches.empty()) {
              Q.emplace_back();
              Q.back().target_branches = new_target_branches;
              Q.front().clone(Q.back());
          }

          if(found_new_branch) {
            new_ex.Swap(*Q.front().latest_success_ex);
            // delete Q.front().latest_success_ex;
            // Q.front().latest_success_ex = new SymbolicExecution();
            // new_ex.clone(*Q.front().latest_success_ex);
            return true;
          }

          if (!CheckPrediction(*sc.cur_ex, new_ex, sc.idxs[sc.b_idx])) {
            num_solve_pred_fails_ ++;
            sc.b_idx++;
            return false;
          }
             if(sc.seen2.find(sc.b_idx)== sc.seen2.end()) {
                sc.seen2.insert(sc.b_idx);
                stack.push(new SubContext(sc.idxs[sc.b_idx], sc.dist-1, &new_ex));
                return false;
              } else {
                sc.b_idx++;
              }
          return false;
        }
        sc.b_idx++;
      } else {
        delete stack.top();
        stack.pop();
      }
    } // end while
    return false;
  }

  void CfgHeuristicMDSearch::PrintStats() {
    fprintf(stderr, "Cfg solves: %u/%u (%u lucky [%u continued], %u on 0's, %u on others,"
  	  "%u unsats, %u prediction failures)\n",
  	  (num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
  	  num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
  	  num_inner_zero_successes_, num_inner_nonzero_successes_,
  	  num_inner_unsats_, num_inner_pred_fails_);
    fprintf(stderr, "    (recursive successes: %u)\n", num_inner_recursive_successes_);
    fprintf(stderr, "Top-level SolveAlongCfg: %u/%u\n",
  	  num_top_solve_successes_, num_top_solves_);
    fprintf(stderr, "All SolveAlongCfg: %u/%u  (%u all concrete, %u no paths)\n",
  	  num_solve_successes_, num_solves_,
  	  num_solve_all_concrete_, num_solve_no_paths_);
    fprintf(stderr, "    (sat failures: %u/%u)  (prediction failures: %u) (recursions: %u)\n",
  	  num_solve_unsats_, num_solve_sat_attempts_,
  	  num_solve_pred_fails_, num_solve_recurses_);
  }

  size_t CfgHeuristicMDSearch::MinCflDistance
  (size_t i, const SymbolicExecution& ex, const set<branch_id_t>& bs) {

    const vector<branch_id_t>& p = ex.path().branches();

    if (i >= p.size())
    return numeric_limits<size_t>::max();

    if (bs.find(p[i]) != bs.end())
    return 0;

    vector<size_t> stack;
    size_t min_dist = numeric_limits<size_t>::max();
    size_t cur_dist = 1;

    fprintf(stderr, "Found uncovered branches at distances:");
    for (BranchIt j = p.begin()+i+1; j != p.end(); ++j) {
      if (bs.find(*j) != bs.end()) {
        min_dist = min(min_dist, cur_dist);
        fprintf(stderr, " %zu", cur_dist);
      }

      if (*j >= 0) {
        cur_dist++;
      } else if (*j == kCallId) {
        stack.push_back(cur_dist);
      } else if (*j == kReturnId) {
        if (stack.size() == 0)
        break;
        cur_dist = stack.back();
        stack.pop_back();
      } else {
        fprintf(stderr, "\nBad branch id: %d\n", *j);
        exit(1);
      }
    }

    fprintf(stderr, "\n");
    return min_dist;
  }

  bool CfgHeuristicMDSearch::FindAlongCfg(size_t i, unsigned int dist,
  				      const SymbolicExecution& ex,
  				      const set<branch_id_t>& bs) {
    const vector<branch_id_t>& path = ex.path().branches();

    if (i >= path.size())
      return false;

    branch_id_t bid = path[i];
    if (bs.find(bid) != bs.end())
      return true;

    if (dist == 0)
      return false;

    // Compute the indices of all branches on the path that immediately
    // follow the current branch (corresponding to the i-th constraint)
    // in the CFG. For example, consider the path:
    //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
    // where '*' is the current branch.  The branches immediately
    // following '*' are : 1, 4, 5, 8, and 9.
    vector<size_t> idxs;
    { size_t pos = i + 1;
      CollectNextBranches(path, &pos, &idxs);
    }

    for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
      if (FindAlongCfg(*j, dist-1, ex, bs))
        return true;
    }

    return false;
  }
  void CfgHeuristicMDSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
    while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
      if (path[*pos] == kCallId) {
        (*pos)++;
        SkipUntilReturn(path, pos);
        if (*pos >= path.size())
  	return;
        assert(path[*pos] == kReturnId);
      }
      (*pos)++;
    }
  }
  void CfgHeuristicMDSearch::CollectNextBranches
  (const vector<branch_id_t>& path, size_t* pos, vector<size_t>* idxs) {
    // Eat an arbitrary sequence of call-returns, collecting inside each one.
    while ((*pos < path.size()) && (path[*pos] == kCallId)) {
      (*pos)++;
      CollectNextBranches(path, pos, idxs);
      SkipUntilReturn(path, pos);
      if (*pos >= path.size())
        return;
      assert(path[*pos] == kReturnId);
      (*pos)++;
    }

    // If the sequence of calls is followed by a branch, add it.
    if ((*pos < path.size()) && (path[*pos] >= 0)) {
      idxs->push_back(*pos);
      (*pos)++;
      return;
    }
  }
  bool CfgHeuristicMDSearch::DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex) {
    if (depth <= 0)
      return false;

    fprintf(stderr, "%d (%d: %d) (%d: %d)\n", depth,
            i-1, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i-1]],
            i, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i]]);

    SymbolicExecution cur_ex;
    vector<value_t> input;
    const vector<SymbolicPred*>& constraints = prev_ex.path().constraints();
    for (size_t j = static_cast<size_t>(i); j < constraints.size(); j++) {
      if (!SolveAtBranch(prev_ex, j, &input)) {
        continue;
      }

      RunProgram(input, &cur_ex);
      iters_left_--;
      Context c;
      if (UpdateCoverage(cur_ex, c)) {
        success_ex_.Swap(cur_ex);
        return true;
      }

      if (!CheckPrediction(prev_ex, cur_ex, prev_ex.path().constraints_idx()[j])) {
        fprintf(stderr, "Prediction failed!\n");
        continue;
      }

      return (DoBoundedBFS(j+1, depth-1, cur_ex)
  	    || DoBoundedBFS(j+1, depth-1, prev_ex));
    }

    return false;
  }

}  // namespace crest
