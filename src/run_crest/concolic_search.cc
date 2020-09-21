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
#include <cmath>
#include <fstream>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <utility>

#include "base/z3_solver.h"
#include "run_crest/concolic_search.h"

using std::ifstream;
using std::ios;
using std::min;
using std::max;
using std::numeric_limits;
using std::pair;
using std::queue;
using std::random_shuffle;
using std::stable_sort;

namespace crest {

////////////////////////////////////////////////////////////////////////
//// Search ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

void Search::read_directory(const std::string& name, vector<string>& v) {
  DIR* dirp = opendir(name.c_str());
  struct dirent * dp;
  while ((dp = readdir(dirp)) != NULL) {
    if(dp->d_type==DT_REG) {
      v.push_back(dp->d_name);
      fprintf(stderr, "%s\n", dp->d_name);
    }
  }
  std::sort(v.begin(), v.end());
  for (int i = 0 ;i < v.size(); i++) {
    fprintf(stderr, "%d: %s\n",i,v[i].c_str());
  }
  closedir(dirp);
}


void Search::UpdateInputFileIdx() {
    rotation_count_ = (++rotation_count_) % 10;
    if(rotation_count_ == 0) {
      input_file_idx_ = (++input_file_idx_) % input_file_names_.size();
    }
    // fprintf(stderr, "UpdateInputFileIdx: rotation count = %d, input_file_idx=%d\n", rotation_count_, input_file_idx_);
}


Search::Search(const string& program, int max_iterations)
  : program_(program), max_iters_(max_iterations), num_iters_(0) {

  start_time_ = time(NULL);

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


  // Initialize for input switching
  input_file_idx_=0;
  rotation_count_ = 0;
  read_directory("inputs", input_file_names_);


  // Print out the initial coverage.
  fprintf(stderr, "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
          num_covered_, reachable_functions_, reachable_branches_);

  // Sort the branches.
  sort(branches_.begin(), branches_.end());
}


Search::~Search() { }


void Search::WriteInputToFileOrDie(const string& file,
				   const vector<value_t>& input) {
  string file_path = std::string("inputs/") + file;
  FILE* f = fopen(file_path.c_str(), "w");
  // fprintf(stderr, "run_crest:write %s.\n", file_path.c_str());
  if (!f) {
    fprintf(stderr, "Failed to open %s.\n", file.c_str());
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
  if (inputs.size() != 0 ) {
    WriteInputToFileOrDie(input_file_names_[input_file_idx_], inputs);
  }

  // WriteInputToFileOrDie("input", inputs);
  setenv("CREST_INPUT_FILE_NAME", input_file_names_[input_file_idx_].c_str(), 1);
  // fprintf(stderr, "env CREST_INPUT_FILE_NAME = %s\n", getenv("CREST_INPUT_FILE_NAME"));

  /*
  pid_t pid = fork();
  assert(pid != -1);

  if (!pid) {
    system(program_.c_str());
    exit(0);
  }
  */

  system(program_.c_str());
}


void Search::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  if (++num_iters_ > max_iters_) {
    // TODO(jburnim): Devise a better system for capping the iterations.
    exit(0);
  }

  // Run the program.
  LaunchProgram(inputs);

  // Read the execution from the program.
  // Want to do this with sockets.  (Currently doing it with files.)
  // ifstream in("szd_execution", ios::in | ios::binary);

  // fprintf(stderr, "parse se/ex_%s\n", input_file_names_[input_file_idx_].c_str());
  ifstream in(("se/ex_" + input_file_names_[input_file_idx_]), ios::in | ios::binary);
  assert(in && ex->Parse(in));
  in.close();


  /*
  for (size_t i = 0; i < ex->path().branches().size(); i++) {
    fprintf(stderr, "%d ", ex->path().branches()[i]);
  }
  fprintf(stderr, "\n");
  */
}


bool Search::UpdateCoverage(const SymbolicExecution& ex) {
  return UpdateCoverage(ex, NULL);
}

bool Search::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches) {

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

  bool found_new_branch = (num_covered_ > prev_covered_);
  if (found_new_branch) {
    WriteCoverageToFileOrDie("coverage");
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
    if (constraints[branch_idx]->Equal(*constraints[i]))
      return false;
  }

  vector<const SymbolicPred*> cs(constraints.begin(),
				 constraints.begin()+branch_idx+1);
  map<var_t,value_t> soln;
  constraints[branch_idx]->Negate();
  // fprintf(stderr, "Yices . . . ");
  bool success ;
  success = Z3Solver::IncrementalSolve(ex.inputs(), ex.vars(), cs, &soln);
  // fprintf(stderr, "%d\n", success);

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

  return false;
}


bool Search::CheckPrediction(const SymbolicExecution& old_ex,
			     const SymbolicExecution& new_ex,
			     size_t branch_idx) {

  if ((old_ex.path().branches().size() <= branch_idx)
      || (new_ex.path().branches().size() <= branch_idx)) {
    return false;
  }

   for (size_t j = 0; j < branch_idx; j++) {
     if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
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
  // DFS(0, ex);
}

  /*
void BoundedDepthFirstSearch::DFS(int depth, SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;

  const SymbolicPath& path = prev_ex.path();

  int last = min(max_depth_, static_cast<int>(path.constraints().size()) - 1);
  for (int i = last; i >= depth; i--) {
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

    // Recurse.
    DFS(i+1, cur_ex);
  }
}
  */


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
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomSearch::RandomSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomSearch::~RandomSearch() { }

void RandomSearch::Run() {
  // vector<SymbolicExecution> next_ex;
  v_ex_.resize(input_file_names_.size());
  SymbolicExecution next_ex;
  vector<unsigned> v_count(input_file_names_.size());
  vector<vector<value_t>> v_next_input(input_file_names_.size());
  while(true) {
	  // count is 0 , run on seed input
    // fprintf(stderr, "v_count[%d]=%d",input_file_idx_,v_count[input_file_idx_]);
	  if( v_count[input_file_idx_] == 0) {
		  fprintf(stderr, "RESET input idx %u\n",input_file_idx_);
		  v_next_input[input_file_idx_].clear();
		  RunProgram(v_next_input[input_file_idx_], &v_ex_[input_file_idx_]);
		  UpdateCoverage(v_ex_[input_file_idx_]);
          	  v_count[input_file_idx_] = (++v_count[input_file_idx_])%10000;
		  UpdateInputFileIdx();
	  } else {
		  // run on the searched input
		  size_t idx;
		  if (SolveRandomBranch(&v_next_input[input_file_idx_], &idx)) {
			  // RunProgram(next_input, &next_ex);
			  RunProgram(v_next_input[input_file_idx_], &next_ex);
			  bool found_new_branch = UpdateCoverage(next_ex);
			  bool prediction_failed =
				  // !CheckPrediction(ex_, next_ex, ex_.path().constraints_idx()[idx]);
				  !CheckPrediction(v_ex_[input_file_idx_], next_ex, v_ex_[input_file_idx_].path().constraints_idx()[idx]);

			  if (found_new_branch) {
				  v_count[input_file_idx_] = 1;
				  v_ex_[input_file_idx_].Swap(next_ex);
				  if (prediction_failed)
					  fprintf(stderr, "Prediction failed (but got lucky).\n");
			  } else if (!prediction_failed) {
				  v_count[input_file_idx_] = 1;
				  v_ex_[input_file_idx_].Swap(next_ex);
			  } else {
          	  		v_count[input_file_idx_] = (++v_count[input_file_idx_])%10000;
                    		  // v_count[input_file_idx_]++;
			        fprintf(stderr, "Prediction failed.\n");
			  }
	  		  UpdateInputFileIdx();
		  } else {
          	  	v_count[input_file_idx_] = (++v_count[input_file_idx_])%10000;
          	// 	v_count[input_file_idx_]++;
      		  }
	  }
  }
}

  bool RandomSearch::SolveRandomBranch(vector<value_t>* next_input, size_t* idx) {

  vector<size_t> idxs(v_ex_[input_file_idx_].path().constraints().size());
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

    if (SolveAtBranch(v_ex_[input_file_idx_], i, next_input)) {
      fprintf(stderr, "Solved %zu/%zu\n", i, idxs.size());
      *idx = i;
      return true;
    }
  }

  // We failed to solve a branch, so reset the input.
    fprintf(stderr, "input_file_idx=%d",input_file_idx_);
  fprintf(stderr, "FAIL\n");
  next_input->clear();
  return false;
}

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



////////////////////////////////////////////////////////////////////////
//// UniformRandomSearch ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

UniformRandomSearch::UniformRandomSearch(const string& program,
					 int max_iterations,
					 size_t max_depth)
  : Search(program, max_iterations), max_depth_(max_depth) { }

UniformRandomSearch::~UniformRandomSearch() { }
/*
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
*/

void UniformRandomSearch::Run() {
  // Initial execution (on empty/random inputs).
  // RunProgram(vector<value_t>(), &prev_ex_);
  // UpdateCoverage(prev_ex_);
	vector<SymbolicExecution> v_prev_ex(input_file_names_.size());
	vector<unsigned> v_count(input_file_names_.size());
	SymbolicExecution cur_ex;

	while (true) {
		vector<value_t> input;
    //fprintf(stderr, "v_prev_ex[%u].path constraint size =%d\n",input_file_idx_, v_prev_ex[input_file_idx_].path().constraints().size());

		if(v_count[input_file_idx_] == 0) {
			fprintf(stderr, "RESET input idx %u\n", input_file_idx_);
			input.clear();
			// depth = 0;
  		RunProgram(input, &v_prev_ex[input_file_idx_]);
			UpdateCoverage(v_prev_ex[input_file_idx_]);
			v_count[input_file_idx_]++;
			UpdateInputFileIdx();
		} else if ((v_count[input_file_idx_] < v_prev_ex[input_file_idx_].path().constraints().size())) {
      int i = v_count[input_file_idx_];
      // if there is an input
			if(SolveAtBranch(v_prev_ex[input_file_idx_], i, &input)) {
			  fprintf(stderr, "Solved constraint %zu/%zu.\n"
                      ,i+1
					            ,v_prev_ex[input_file_idx_].path().constraints().size());
        // toss a coin
			  if (rand() %2 == 0) {
				  RunProgram(input, &cur_ex);
					UpdateCoverage(cur_ex);
					size_t branch_idx = v_prev_ex[input_file_idx_].path().constraints_idx()[i];
					if (!CheckPrediction(v_prev_ex[input_file_idx_], cur_ex, branch_idx)) {
						fprintf(stderr, "prediction failed\n");
						// depth--;
					} else {
						cur_ex.Swap(v_prev_ex[input_file_idx_]);
					}
          v_count[input_file_idx_]++;
					UpdateInputFileIdx();
				} else {
          v_count[input_file_idx_]++;
        }
		  } else {
        v_count[input_file_idx_]++;
      }
		} else {
      v_count[input_file_idx_] = 0;
    }
  }
}
/*
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
*/

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


CfgHeuristicSearch::~CfgHeuristicSearch() { }

/*
void CfgHeuristicSearch::Run() {
  set<branch_id_t> newly_covered_;
  SymbolicExecution ex;

  while (true) {
    covered_.assign(max_branch_, false);
    num_covered_ = 0;

    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      UpdateBranchDistances();
      PrintStats();
    }

    // while (DoSearch(3, 200, 0, kInfiniteDistance+10, ex)) {
    while (DoSearch(5, 30, 0, kInfiniteDistance, ex)) {
    // while (DoSearch(3, 10000, 0, kInfiniteDistance, ex)) {
      PrintStats();
      // As long as we keep finding new branches . . . .
      UpdateBranchDistances();
      ex.Swap(success_ex_);
    }
    PrintStats();
  }
}
*/

void CfgHeuristicSearch::Run() {
  // v_ex_.resize(input_file_names_.size());
  v_context_.resize(input_file_names_.size());
  covered_.assign(max_branch_, false);
  num_covered_ = 0;
  while(true) {
    // fprintf(stderr, "while true\n");
    Context &context = v_context_[input_file_idx_];
    bool is_all_contexts_failed =true;
    for(int i = 0 ; i < v_context_.size(); i++) {
      if(!v_context_[input_file_idx_].is_do_search_failed) {
        is_all_contexts_failed = false;
        break;
      }
    }
    if(is_all_contexts_failed) {
      for(int i = 0 ; i < v_context_.size(); i++) {
        if(!v_context_[input_file_idx_].is_do_search_failed) {
          v_context_[input_file_idx_].is_reset=true;
        }
      }
    }
    if(context.is_reset) {
      // covered_.assign(max_branch_, false);
      fprintf(stderr, "RESET input idx %u\n",  input_file_idx_);
      context = v_context_[input_file_idx_] = Context();
      RunProgram(vector<value_t>(), &context.cur_ex);
      // If new coverage
      if(UpdateCoverage(context.cur_ex)) {
        UpdateBranchDistances();
      }
      // for(int i = 0 ; i < context.cur_ex.path().branches().size(); i++) {
        // fprintf(stderr,"b%d: %d\n", i, context.cur_ex.path().branches()[i]);
      // }
      context.iters=30;
      context.is_reset= false;
      UpdateInputFileIdx();
    } else {
      // fprintf(stderr, "Check Stack sub context is empty()\n");
      if(context.stack_sub_context.empty()) {
        // fprintf(stderr, "Stack sub context is empty()\n");
        if(DoSearchOnce(context)) {
          // fprintf(stderr, "DoSearchOnce Success\n");
          // new branch found!
          // 스택이 empty인 경우 더이상 Search할 게 없으니 Distance 업데이트 하고 execution 변경
          if(context.stack_sub_context.empty()) {
            UpdateBranchDistances();
            context.cur_ex.Swap(context.latest_success_ex);
            context.scoredBranches.clear();
            UpdateInputFileIdx();
            context.do_search_once_found_new_branch = false;
          } else { // 스택이 empty가 아닌 경우, SolveOnePAthAlongCfg를 실행해야 하므로 update를 보류
            context.do_search_once_found_new_branch = true;
          }
        } else {
          // fprintf(stderr, "DoSearchOnce Failed\n");
          if(context.is_reset) {
            continue;
          } else {
            UpdateInputFileIdx();
          }
        }
        // for(int i = 0 ; i < context.cur_ex.path().branches().size(); i++) {
        //   fprintf(stderr,"b%d: %d\n", i, context.cur_ex.path().branches()[i]);
        // }
        // for(int i = 0 ; i < context.latest_success_ex.path().branches().size(); i++) {
        //   fprintf(stderr,"b%d: %d\n", i, context.latest_success_ex.path().branches()[i]);
        // }
      } else {
        // fprintf(stderr, "Stack sub context is not empty()\n");
        // fprintf(stderr, "Stack size is %d\n", context.stack_sub_context.size());
        if(!SolveOnePathAlongCfg(context)) {
          // fprintf(stderr,"SolveOnePathAlongCfg False\n");
          if(!context.stack_sub_context.empty()) {
            // SolveOnePathAlongCfg ran on some input but not found new paths
            // fprintf(stderr,"stack is not empty\n");
            UpdateInputFileIdx();
          } else {
            // fprintf(stderr,"stack is empty\n");
            if(context.do_search_once_found_new_branch) {
               // fprintf(stderr,"do_search_once_found_new_branch = true ( ye sswsp)\n");
               UpdateBranchDistances();
               context.cur_ex.Swap(context.latest_success_ex);
               context.cur_idx++;
               // UpdateCoverage(context.cur_ex);
               UpdateInputFileIdx();
            } else {
              // fprintf(stderr,"do_search_once_found_new_branch = false ( no swaP)\n");
            }
            context.do_search_once_found_new_branch = false;
            //fprintf(stderr,"SolveOnePathAlongCfg False\n");
            // SolveOnePathAlongCfg didn't find any new coverage so move on
          }
        } else {
          // New Coverage
          UpdateBranchDistances();
          context.cur_ex.Swap(context.latest_success_ex);
          context.scoredBranches.clear();
          UpdateInputFileIdx();
        }
      }
      //context_[input_file_idx_].top_idx++;
      //  context_[input_file_idx_].iters--;
    }
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
/*
  for(int i = 0 ; i < dist_.size();i ++) {
    fprintf(stderr,"dist_[%d]=%d\n",i,dist_[i]);
  }
*/
}

bool CfgHeuristicSearch::DoSearchOnce(Context& context) {
  // fprintf(stderr,"DoSearchOnce!\n");
  // const SymbolicExecution& prev_ex = context.cur_ex;

  // fprintf(stderr, "DoSearchOnce(%d, %d, %d, %zu)\n",
	  // depth, pos, maxDist, prev_ex.path().branches().size());

  // if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
    // return false;

  // if (depth == 0)
    // return false;

  // if scoredBranches is empty then make one

  if(context.scoredBranches.empty()) {
    // fprintf(stderr, "scoredBranches is empty\n");
    // whatif path size is 0?

    // For each symbolic branch/constraint in the execution path, we will
    // compute a heuristic score, and then attempt to force the branches
    // in order of increasing score.
    // vector<ScoredBranch> context.scoredBranches(prev_ex.path().constraints().size());
    context.scoredBranches.resize(context.cur_ex.path().constraints().size());
    for (size_t i = 0; i < context.scoredBranches.size(); i++) {
      context.scoredBranches[i].first = i;
    }
    { // Compute (and sort by) the scores.
      random_shuffle(context.scoredBranches.begin(), context.scoredBranches.end());
      map<branch_id_t,int> seen;
      for (size_t i = 0; i < context.scoredBranches.size(); i++) {
        size_t idx = context.scoredBranches[i].first;
        size_t branch_idx = context.cur_ex.path().constraints_idx()[idx];
        branch_id_t bid = paired_branch_[context.cur_ex.path().branches()[branch_idx]];

        context.scoredBranches[i].second = dist_[bid] + seen[bid];
        seen[bid] += 1;
      }
    }
    stable_sort(context.scoredBranches.begin(), context.scoredBranches.end(), ScoredBranchComp());
    for(int i = 0 ; i < context.scoredBranches.size(); i++) {
      //  size_t branch_idx = context.cur_ex.path().constraints_idx()[i];
      // fprintf(stderr,"context.scoredBranches[%d]=%d\n", i , context.scoredBranches[i].second);
    }
  } else {
    // fprintf(stderr, "scoredBranches is not empty\n");
  }
  // fprintf(stderr, "size of scoredBranch = %u\n", context.scoredBranches.size());
  // Solve.
  SymbolicExecution new_ex;
  vector<value_t> input;
  // for (size_t i = 0; i < scoredBranches.size(); i++) {
  while(context.cur_idx < context.scoredBranches.size()) {
    // fprintf(stderr, "cur_idx = %u\n", context.cur_idx);
    if ((context.iters <= 0) || (context.scoredBranches[context.cur_idx].second > kInfiniteDistance)) {
      // fprintf(stderr, "here1\n");
          return false;
    }
    num_inner_solves_ ++;

    if (!SolveAtBranch(context.cur_ex, context.scoredBranches[context.cur_idx].first, &input)) { // Unsat
        // fprintf(stderr, "unsat\n");
      context.cur_idx++;
      continue;
    }
    RunProgram(input, &new_ex);
    context.iters--;

    size_t b_idx = context.cur_ex.path().constraints_idx()[context.scoredBranches[context.cur_idx].first];
    branch_id_t bid = paired_branch_[context.cur_ex.path().branches()[b_idx]];
    set<branch_id_t> new_branches;
    bool found_new_branch = UpdateCoverage(new_ex, &new_branches);
    bool prediction_failed = !CheckPrediction(context.cur_ex, new_ex, b_idx);



    if (found_new_branch && prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(stderr, "Found new branch by forcing at "
	              "distance %zu (%d) [lucky, pred failed].\n",
	      dist_[bid], context.scoredBranches[context.cur_idx].second);

      // We got lucky, and can't really compute any further stats
      // because prediction failed.
      num_inner_lucky_successes_ ++;
      num_inner_successes_pred_fail_ ++;
      context.latest_success_ex.Swap(new_ex);
      return true;
    }

    if (found_new_branch && !prediction_failed) {
      fprintf(stderr, "Found new branch by forcing at distance %zu (%d).\n",
	      dist_[bid], context.scoredBranches[context.cur_idx].second);
      size_t min_dist = MinCflDistance(b_idx, new_ex, new_branches);
      // Check if we were lucky.
      if (FindAlongCfg(b_idx, dist_[bid], new_ex, new_branches)) {
      	assert(min_dist <= dist_[bid]);
      	// A legitimate find -- return success.
      	if (dist_[bid] == 0) {
      	  num_inner_zero_successes_ ++;
      	} else {
      	  num_inner_nonzero_successes_ ++;
      	}
      	context.latest_success_ex.Swap(new_ex);
        // fprintf(stderr, "FindAlongCfgTrue.\n");
      	return true;
      } else {
      	// We got lucky, but as long as there were no prediction failures,
      	// we'll finish the CFG search to see if that works, too.
      	assert(min_dist > dist_[bid]);
      	assert(dist_[bid] != 0);
      	num_inner_lucky_successes_ ++;
        // fprintf(stderr, "FindAlongCfgFalse.\n");
      }
    }

    if (prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      if (!found_new_branch) {
	      num_inner_pred_fails_ ++;
        context.cur_idx++;
	      continue;
      }
    }
    // If we reached here, then scoredBranches[i].second is greater than 0.
    num_top_solves_ ++;
    if(dist_[bid] > 0) {
      num_top_solve_successes_ ++;
      // PrintStats();
      // not solve along static path but push stack

      // context.stack.push(b_idx, scoredBranches[i].second-1, cur_ex);
      // return false because there is no new branch
      // SymbolicExecution xx = new_ex;
      context.stack_sub_context.push(SubContext(b_idx, context.scoredBranches[context.cur_idx].second -1, new_ex));
      // context.stack_sub_context.pop();
      // return false;
    }

    if (found_new_branch) {
      context.latest_success_ex.Swap(new_ex);
      return true;
    } else {
      context.cur_idx++;
      return false;
    }
  }
  context.is_reset = true;
  return false;
}


/*
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
      PrintStats();
      return true;
    }

    if (found_new_branch) {
      success_ex_.Swap(cur_ex);
      return true;
    }

  }

  return false;
}
*/

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


// SubContext
// Symbolic Execution cur_ex
// constraint_index
// idxs
// branch_idx
// dist


// while stop condition (stack empty... & ? )
// Collect next branches of stack top
// if there is next Branches and found paths
//   random_shuffle
//   Add to stack
// end if
// else : there is no paths
// pop
// end else


// Search next branch to solve using subcontext stack
bool CfgHeuristicSearch::SolveOnePathAlongCfg(Context& context) {
  // fprintf(stderr, "SolveOnePathAlongCfg\n");
  stack<SubContext>&stack = context.stack_sub_context;
  vector<value_t> input;
  SymbolicExecution new_ex;
  while(!stack.empty()) {
    SubContext& sc = stack.top();
    vector<branch_id_t> path = sc.cur_ex.path().branches();
    // fprintf(stderr, "stack size : %u\n",stack.size());
    // fprintf(stderr, "constraint index(cur_idx) : %u\n",sc.cur_idx);
    // fprintf(stderr, "dist : %u\n",sc.dist);
    // fprintf(stderr, "next idxs size : %u\n",sc.idxs.size());

    if(!sc.idxs.empty()) { // idxs empty means next branches are not found
      // fprintf(stderr, "sc idx size: %u\n",sc.idxs.size());
      bool found_path = false;
      // vector<size_t> idxs;
      {
        size_t pos = sc.cur_idx + 1;
        CollectNextBranches(path, &pos, &sc.idxs);
        // fprintf(stderr, "Branches following %d:", path[i]);
        for (size_t j = 0; j < sc.idxs.size(); j++) {
          // fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
          //      dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
          if ((dist_[path[sc.idxs[j]]] <= sc.dist)
              || (dist_[paired_branch_[path[sc.idxs[j]]]] <= sc.dist))
            found_path = true;
        }
        //fprintf(stderr, "\n");
      }

      if (!found_path) {
        // num_solve_no_paths_ ++;
        // fprintf(stderr, "not found path\n");
        stack.pop();
        continue;
      }
      // bool all_concrete = true;
      // num_solve_all_concrete_ ++;

      // We will iterate through these indices in some order (random?
      // increasing order of distance? decreasing?), and try to force and
      // recurse along each one with distance no greater than max_dist.
      random_shuffle(sc.idxs.begin(), sc.idxs.end());
      sc.cur_idx = 0;

       // should set dist, current index -1,

    } else if (sc.cur_idx < sc.idxs.size()) {
      // point next index
      if((dist_[path[sc.cur_idx]] > sc.dist && (dist_[paired_branch_[path[sc.cur_idx]]] > sc.dist))) {
          sc.cur_idx++;
          continue;
      }
      if (dist_[path[sc.cur_idx]] <= sc.dist ) {
          // SubContext newSubCotext = new SubContext(sc.cur_idx, sc.dist - 1, sc.cur_ex);
          // context.stack_sub_context.push(new SubContext(b_idx, context.scoredBranches[context.cur_idx]-1, new_ex ));
          // fprintf(stderr, "dist_[path[%d]](%d) <= sc.dist(%d)", path[sc.cur_idx], dist_[path[sc.cur_idx]],sc.dist);
          stack.push(SubContext(sc.cur_idx, sc.dist -1 , sc.cur_ex));
          continue;
      }

      // Find the constraint corresponding to branch idxs[*j].
      vector<size_t>::const_iterator idx =
        lower_bound(sc.cur_ex.path().constraints_idx().begin(),
        sc.cur_ex.path().constraints_idx().end(), sc.cur_idx);
      if ((idx == sc.cur_ex.path().constraints_idx().end()) || (*idx != sc.cur_idx)) {
        continue;  // Branch is concrete.
      }
      size_t c_idx = idx - sc.cur_ex.path().constraints_idx().begin();
      if(dist_[paired_branch_[path[sc.cur_idx]]] <= sc.dist) {
        if (!SolveAtBranch(sc.cur_ex, c_idx, &input)) {
          //unsat
          sc.cur_idx++;
          continue;
        }
        RunProgram(input, &new_ex);
        // fprintf(stderr, "RunProgram\n\n");
        if(UpdateCoverage(new_ex)) {
          context.latest_success_ex.Swap(new_ex);
          // stack.clear();
          // fprintf(stderr, "new coverage, pop");
          stack=std::stack<SubContext>();
          return true;
        }

        if (!CheckPrediction(sc.cur_ex, new_ex, sc.cur_idx)) {
          num_solve_pred_fails_ ++;
          continue;
        }
        // Add To Stack
        // new SubContext subcontext //
        // stack.push( subcontext )
        // fprintf(stderr, "dist_[path[%d]](%d) <= sc.dist(%d)", path[sc.cur_idx], dist_[path[sc.cur_idx]],sc.dist);
        // SymbolicExecution exex = new_ex;
        // stack.push(SubContext(sc.cur_idx, sc.dist-1, exex));
        stack.push(SubContext(sc.cur_idx, sc.dist-1, new_ex));
        // return false because one execution ran
        return false;
      }
      // fprintf(stderr, "%d\n" , stack.top().cur_idx);
      stack.top().cur_idx++;
    } else {
      // fprintf(stderr, "stack pop start (size %u)\n", stack.size());
      stack.pop();
      // fprintf(stderr, "stack pop2\n");
    }
  } // end while
  // fprintf(stderr, "stack is empty return false(size is %u)\n", stack.size());
  return false;
}

/*
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
    // fprintf(stderr, "Branches following %d:", path[i]);
    for (size_t j = 0; j < idxs.size(); j++) {
      // fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
      //      dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
      if ((dist_[path[idxs[j]]] <= max_dist)
	  || (dist_[paired_branch_[path[idxs[j]]]] <= max_dist))
	found_path = true;
    }
    //fprintf(stderr, "\n");
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
      for(int aaa = 0 ; aaa < prev_ex.path().branches().size(); aaa++) {
        fprintf(stderr,"branch %d: %d\n",aaa, prev_ex.path().branches()[aaa]);
      }
      for(int aaa = 0 ; aaa < dist_.size(); aaa++) {
	fprintf(stderr, "dist_[%d]=%u\n",aaa, dist_[aaa]);
      }
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
*/

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

}  // namespace crest
