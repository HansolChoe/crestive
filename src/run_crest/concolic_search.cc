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
using std::random_shuffle;
using std::stable_sort;
using std::strcmp;

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
    fprintf(stderr, "Update Input File Index(%d,%d)\n", input_file_idx_, rotation_count_);
}


Search::Search(const string& program, int max_iterations)
  : program_(program), max_iters_(max_iterations), num_iters_(0) {

  start_time_ = time(NULL);
  begin_total_ = std::chrono::high_resolution_clock::now();
  summary_time_ = 0;
  time_out_ = 1500;

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
struct cmp_str
{
  bool operator()(char const *a, char const *b) const
  {
    return strcmp(a, b) < 0;
   }
};

  map<const char *, const char*, cmp_str> program_names = {
    {"input1","./grep aaaaaaaaaaa /dev/null"}, //11
    {"input10","./grep aaaaaaaaaaaa /dev/null"}, // 11
    {"input2","./grep aaaaaaaaaaaa /dev/null"}, // 12
    {"input3","./grep aaaaaaaaaa /dev/null"}, // 10
    {"input4","./grep aaaaaaaaaaaaa /dev/null"}, // 13
    {"input5","./grep aaaaaaaaaa /dev/null"},
    {"input6","./grep aaaaaaaaaaaaaaaaaaaa /dev/null"},
    {"input7","./grep aaaaaaaaaaaaaaaaaaaaaa /dev/null"},
    {"input8","./grep aaaaaaaaaaaaaaaaaaaa /dev/null"},
    {"input9","./grep aaaaaaaaaaaaaa /dev/null"} };
/*
  const char program_names[][100] = {
    "./grep aaaaaaaaaaa /dev/null", 
    "./grep aaaaaaaaaaaa /dev/null", 
    "./grep aaaaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaaaaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaaaaaaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaaaaaaaaaaaa /dev/null",
    "./grep aaaaaaaaaaaaaa /dev/null", // 14
     };
*/

  system(program_names[input_file_names_[input_file_idx_].c_str()]);
  // system(program_.c_str());
  
}


void Search::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  end_total_ = std::chrono::high_resolution_clock::now();
  elapsed_time_total_ = end_total_ - begin_total_;
 
  if (++num_iters_ > max_iters_ || elapsed_time_total_.count() >= time_out_) {
      exit(0);
  }

  // Run the program.
  LaunchProgram(inputs);

  ifstream in(("se/ex_" + input_file_names_[input_file_idx_]), ios::in | ios::binary);
  assert(in && ex->Parse(in));
  in.close();
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

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;

  FILE *f = fopen("log1", "a");
  if (!f) {
    fprintf(stderr, "Writing logging, failed to open %s. \n", "log1");
    return found_new_branch;
  }
  //fprintf(f, "%u,%.2lf,%u,%u,%u\n", total_num_covered_, time_diff, num_prediction_fail_,num_constraints_size_, num_unsat_);
    fprintf(f, "%u,%.2lf,%u\n", total_num_covered_,time_diff ,num_prediction_fail_);

  fclose(f);

  while(summary_time_ <= time_diff.count()) {
    FILE *ff = fopen("summary1", "a");
    if (!ff) {
      fprintf(stderr, "Writing summary, failed to open %s. \n", "summary1");
      return found_new_branch;
    }
    // fprintf(ff, "%u,%.2lf,%u,%u,%u\n", total_num_covered_, time_diff, num_prediction_fail_,num_constraints_size_, num_unsat_);
    fprintf(ff, "%u,%.2lf,%u\n", total_num_covered_,time_diff,num_prediction_fail_);
    end_total_ = std::chrono::high_resolution_clock::now();
    fclose(ff);
    summary_time_ += 10;
  }
  
  // auto time_diff = end_total_ - begin_total_;
  while(coverage_log_time_ <= time_diff.count()) {
    std::stringstream s;
    s << "cp coverage coverages/coverage" << coverage_log_time_;
    system(s.str().c_str());
    coverage_log_time_ += 10;
    printf("summary %ld\n",coverage_log_time_);
  }

  return found_new_branch;
}

bool CfgHeuristicESSearch::UpdateCoverage(const SymbolicExecution& ex,
                            Context &context) {
      return UpdateCoverage(ex, NULL, context);
}

bool CfgHeuristicESSearch::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches,
                            Context &context) {

  const unsigned int prev_covered_ = context.num_covered;
  const vector<branch_id_t>& branches = ex.path().branches();
  for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
    if ((*i > 0) && !context.covered[*i]) {
      context.covered[*i] = true;
      context.num_covered++;
      if (new_branches) {
	new_branches->insert(*i);
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
   //  fprintf(stderr, "found new branch \n");
    WriteCoverageToFileOrDie("coverage");
  } else {

    // fprintf(stderr, "not found new branch \n");
 }

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;

  FILE *f = fopen("log1", "a");
  if (!f) {
    fprintf(stderr, "Writing logging, failed to open %s. \n", "log1");
    return found_new_branch;
  }
  //fprintf(f, "%u,%.2lf,%u,%u,%u\n", total_num_covered_, time_diff, num_prediction_fail_,num_constraints_size_, num_unsat_);
    fprintf(f, "%u,%.2lf,%u\n", total_num_covered_, time_diff, num_prediction_fail_);

  fclose(f);

  while(summary_time_ <= time_diff.count()) {
    FILE *ff = fopen("summary1", "a");
    if (!ff) {
      fprintf(stderr, "Writing summary, failed to open %s. \n", "summary1");
      return found_new_branch;
    }
    // fprintf(ff, "%u,%.2lf,%u,%u,%u\n", total_num_covered_, time_diff, num_prediction_fail_,num_constraints_size_, num_unsat_);
    fprintf(ff, "%u,%.2lf,%u\n", total_num_covered_, time_diff, num_prediction_fail_);
    end_total_ = std::chrono::high_resolution_clock::now();
    fclose(ff);
    summary_time_ += 10;
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
    num_prediction_fail_++;
    return false;
  }

   for (size_t j = 0; j < branch_idx; j++) {
     if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
       num_prediction_fail_++;
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
//// RandomESSearch ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomESSearch::RandomESSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomESSearch::~RandomESSearch() { }

void RandomESSearch::Run() {
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
				 //  v_count[input_file_idx_] = 1;
				    v_ex_[input_file_idx_].Swap(next_ex);
         		v_count[input_file_idx_] = (++v_count[input_file_idx_])%10000;
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

  bool RandomESSearch::SolveRandomBranch(vector<value_t>* next_input, size_t* idx) {

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

void RandomESSearch::SolveUncoveredBranches(size_t i, int depth,
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
//// CfgHeuristicESSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgHeuristicESSearch::CfgHeuristicESSearch
(const string& program, int max_iterations)
  : Search(program, max_iterations),
    cfg_(max_branch_), cfg_rev_(max_branch_), dist_notusing(max_branch_) {

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


CfgHeuristicESSearch::~CfgHeuristicESSearch() { }

/*
void CfgHeuristicESSearch::Run() {
  set<branch_id_t> newly_covered_;
  SymbolicExecution ex;

  while (true) {
    covered_.assign(max_branch_, false);
    num_covered_ = 0;

    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      pdateBranchDistances();
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
/*
void Search::UpdateInputFileIdx() {
    rotation_count_ = (++rotation_count_) % 10;
    if(rotation_count_ == 0) {
      input_file_idx_ = (++input_file_idx_) % input_file_names_.size();
    }
    fprintf(stderr, "UpdateInputFileIdx: rotation count = %d, input_file_idx=%d\n", rotation_count_, input_file_idx_);
}
*/
void CfgHeuristicESSearch::Run() {
  v_context_.resize(input_file_names_.size());
  num_covered_ = 0;
  for(int i = 0 ; i < v_context_.size(); i++) {
  //   v_context_[i].covered.resize(max_branch_, false);
     v_context_[i].dist.resize(max_branch_, 0);
  }
  string names[] = {"input1", "input10", "input2", "input3", "input4", "input5", "input6", "input7", "input8", "input9"};
  while(true) {
    Context &context = v_context_[input_file_idx_];
    if(context.is_reset) {
    // fprintf(stderr, "while true3\n");
      fprintf(stderr, "RESET input idx %u\n",  input_file_idx_);
      string cmd = "cp seeds/" + names[input_file_idx_] + " inputs/";
      system(cmd.c_str());
     
      context.covered.assign(max_branch_, false);
      context.cur_idx = 0;
      context.num_covered = 0;
      context.new_branches.clear();
      context.scoredBranches.clear();
      

      RunProgram(vector<value_t>(), &context.cur_ex);

      if(UpdateCoverage(context.cur_ex, context)) {
        UpdateBranchDistances(context.covered, context.dist);
      } else {
        // fprintf(stderr, "not foudn new branch\n");
      }
      // for(int i = 0 ; i < context.cur_ex.path().branches().size(); i++) {
        // fprintf(stderr,"b%d: %d\n", i, context.cur_ex.path().branches()[i]);
      // }
      context.iters=30;
      context.is_reset= false;
      UpdateInputFileIdx();
    } else {
    // fprintf(stderr, "while true4\n");
      // fprintf(stderr, "Check Stack sub context is empty()\n");
      if(context.stack_sub_context.empty()) {
        // fprintf(stderr, "Stack sub context is empty()\n");
        if(DoSearchOnce(context)) {
          // DoSearchOnce가 성공할 때는 2가지
          //  1. 새로운 branch를 찾았고 prediction failure false
          // 2. 새로운  branch를 찾았고, prediction failure true
          // 두가지 경우 모두 execution을 Swap하면  된다.
          UpdateBranchDistances(context.covered, context.dist);
          context.cur_ex.Swap(context.latest_success_ex);
          // context.cur_ex = context.latest_success_ex;
          context.cur_idx = 0;
          // context.do_search_once_found_new_branch = false;
          context.scoredBranches.clear();
          context.iters=30;
          context.new_branches.clear();
          UpdateInputFileIdx();
          // fprintf(stderr, "here");
        } else {
      //    context.cur_idx++;
          // 1. 새로운 브랜치를 못찾고, prediction failure
          // 2. FindAlongCfg 성공후 stack에 추가
          // 3. Do search fail ( execution 종료)
        }
        // for(int i = 0 ; i < context.cur_ex.path().branches().size(); i++) {
        //   fprintf(stderr,"b%d: %d\n", i, context.cur_ex.path().branches()[i]);
        // }
        // for(int i = 0 ; i < context.latest_success_ex.path().branches().size(); i++) {
        //   fprintf(stderr,"b%d: %d\n", i, context.latest_success_ex.path().branches()[i]);
        // }
      } else {
        if(!SolveOnePathAlongCfg(context)) {
          if(!context.stack_sub_context.empty()) {
            UpdateInputFileIdx();
          } else { // stack is empty
            if(context.do_search_once_found_new_branch) {
               UpdateBranchDistances(context.covered, context.dist);
               context.new_branches.clear();
               context.cur_ex.Swap(context.latest_success_ex);
               context.scoredBranches.clear();
               context.iters=30;
               context.cur_idx = 0;
               UpdateInputFileIdx();
            } else {
              context.cur_idx++;
            }
            context.do_search_once_found_new_branch = false;
          }
        } else {
          UpdateBranchDistances(context.covered, context.dist);
          context.stack_sub_context = std::stack<SubContext>();
          context.cur_ex.Swap(context.latest_success_ex);
          // context.cur_ex = context.latest_success_ex;
          context.scoredBranches.clear();
          context.new_branches.clear();
          context.cur_idx = 0;
          context.iters=30;
          UpdateInputFileIdx();
        }
      }
      //context_[input_file_idx_].top_idx++;
      //  context_[input_file_idx_].iters--;
    }
  }
}

void CfgHeuristicESSearch::PrintStats() {
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

void CfgHeuristicESSearch::UpdateBranchDistances(vector<bool>& covered, vector<long unsigned int>& dist) {
  // We run a BFS backward, starting simultaneously at all uncovered vertices.
  // fprintf(stderr, "covered size: %u, dist size %u", covered.size(), dist.size());
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

  // for(int i = 0 ; i < dist.size();i ++) {
  //   fprintf(stderr,"context.dist[%d]=%d\n",i,dist[i]);
  // }

}

bool CfgHeuristicESSearch::DoSearchOnce(Context& context) {
  // fprintf(stderr,"DoSearchOnce\n");

  if(context.scoredBranches.empty()) {
    context.scoredBranches.resize(context.cur_ex.path().constraints().size());
    for (size_t i = 0; i < context.scoredBranches.size(); i++) {
      context.scoredBranches[i].first = i;
    }

    { // Compute (and sort by) the scores.
       // fprintf(stderr,"start computing scores\n");
      random_shuffle(context.scoredBranches.begin(), context.scoredBranches.end());
      map<branch_id_t,int> seen;
      for (size_t i = 0; i < context.scoredBranches.size(); i++) {
        size_t idx = context.scoredBranches[i].first;
        size_t branch_idx = context.cur_ex.path().constraints_idx()[idx];
        branch_id_t bid = paired_branch_[context.cur_ex.path().branches()[branch_idx]];

        context.scoredBranches[i].second = context.dist[bid] + seen[bid];
        seen[bid] += 1;
      }
    }
    stable_sort(context.scoredBranches.begin(), context.scoredBranches.end(), ScoredBranchComp());
    for(int i = 0 ; i < context.scoredBranches.size(); i++) {
      //  size_t branch_idx = context.cur_ex.path().constraints_idx()[i];
     //fprintf(stderr,"context.scoredBranches[%d]=%d\n", i , context.scoredBranches[i].second);
       // fprintf(stderr,"context.scoredBranches[%d]=%d,%d\n", i , context.scoredBranches[i].first, context.scoredBranches[i].second);
    }
  } else {
    // fprintf(stderr, "scoredBranches is not empty\n");
  }
  // fprintf(stderr, "size of scoredBranch = %u\n", context.scoredBranches.size());
     // fprintf(stderr, "cur_idx = %u\n", context.cur_idx);
  // Solve.
  SymbolicExecution new_ex;
  vector<value_t> input;
  // for (size_t i = 0; i < scoredBranches.size(); i++) {
  while(context.cur_idx < context.scoredBranches.size()) {
    // fprintf(stderr, "DoSearchOnce: cur_idx = %u/%u, iters = %u \n", context.cur_idx, context.scoredBranches.size(), context.iters);
    if ((context.iters <= 0) || (context.scoredBranches[context.cur_idx].second > kInfiniteDistance)) {
          // context.is_do_search_failed = true;
          context.is_reset = true;
          return false;
          //context.cur_idx++;
          // continue;
    }
    num_inner_solves_ ++;

    if (!SolveAtBranch(context.cur_ex, context.scoredBranches[context.cur_idx].first, &input)) { // Unsat
      // fprintf(stderr, "unsat\n");
      context.cur_idx++;
      continue;
    }
    RunProgram(input, &new_ex);
    context.iters--;
    // fprintf(stderr, "iters = %d\n", context.iters);

    size_t b_idx = context.cur_ex.path().constraints_idx()[context.scoredBranches[context.cur_idx].first];
    branch_id_t bid = paired_branch_[context.cur_ex.path().branches()[b_idx]];
    // set<branch_id_t> new_branches;
    bool found_new_branch = UpdateCoverage(new_ex, &context.new_branches, context);
    bool prediction_failed = !CheckPrediction(context.cur_ex, new_ex, b_idx);

    if (found_new_branch && prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(stderr, "Found new branch by forcing at "
	              "distance %zu (%d) [lucky, pred failed].\n",
	      context.dist[bid], context.scoredBranches[context.cur_idx].second);

      // We got lucky, and can't really compute any further stats
      // because prediction failed.
      num_inner_lucky_successes_ ++;
      num_inner_successes_pred_fail_ ++;
      context.latest_success_ex.Swap(new_ex);
      // context.latest_success_ex = new_ex;
      return true;
    }

    if (found_new_branch && !prediction_failed) {
      fprintf(stderr, "Found new branch by forcing at distance %zu (%d).\n",
	      context.dist[bid], context.scoredBranches[context.cur_idx].second);
      size_t min_dist = MinCflDistance(b_idx, new_ex, context.new_branches);
      // Check if we were lucky.
      if (FindAlongCfg(b_idx, context.dist[bid], new_ex, context.new_branches)) {
        // fprintf(stderr, "FindAlongCfg True\n");
      	assert(min_dist <= context.dist[bid]);
      	// A legitimate find -- return success.
      	if (context.dist[bid] == 0) {
      	  num_inner_zero_successes_ ++;
      	} else {
      	  num_inner_nonzero_successes_ ++;
      	}
     	context.latest_success_ex.Swap(new_ex);
    //   context.latest_success_ex = new_ex;
      	return true;
      } else {
        // fprintf(stderr, "FindAlongCfg False\n");
      	// We got lucky, but as long as there were no prediction failures,
      	// we'll finish the CFG search to see if that works, too.
      	assert(min_dist > context.dist[bid]);
      	assert(context.dist[bid] != 0);
      	num_inner_lucky_successes_ ++;
        // fprintf(stderr, "FindAlongCfgFalse.\n");
      }
    }

    if (prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      if (!found_new_branch) {
	      num_inner_pred_fails_ ++;
         context.cur_idx++;
         UpdateInputFileIdx();
         return false;
	      // continue;
      }
    }
    // If we reached here, then scoredBranches[i].second is greater than 0.
    num_top_solves_ ++;
    // fprintf(stderr, "after top solve dist_[%d]:%d\n", bid, dist_[bid]);
    if(context.dist[bid] > 0) {
      num_top_solve_successes_ ++;
      // PrintStats();
      // not solve along static path but push stack

      // context.stack.push(b_idx, scoredBranches[i].second-1, cur_ex);
      // return false because there is no new branch
      // SymbolicExecution xx = new_ex;
      // fprintf(stderr, "push scoredBranch[%d].first :%d\n", context.cur_idx, context.scoredBranches[context.cur_idx].first);
      // fprintf(stderr, "push scoredBranch[%d].second - 1 :%d\n", context.cur_idx, context.scoredBranches[context.cur_idx].second - 1);
      // fprintf(stderr, "b_idx : [%d]\n", b_idx);
      // if(context.scoredBranches[context.cur_idx].second-1 > 0) {
      // fprintf(stderr, "push sub context\n");
      context.stack_sub_context.push(SubContext(b_idx, context.scoredBranches[context.cur_idx].second -1, new_ex));
      // fprintf(stderr, "push2    \n");
      // } else {
      //fprintf(stderr, "no push    \n");
      //}
      // context.stack_sub_context.pop();
      // return false;
    }

    if (found_new_branch) {
      context.latest_success_ex.Swap(new_ex);
      // context.latest_success_ex = new_ex;
      context.do_search_once_found_new_branch = true;
      // return false;
    } else {
      context.cur_idx++;
      UpdateInputFileIdx();
      // return false;
    }
    return false;
  }
  context.is_reset = true;
  // fprintf(stderr,"set context[%d]'s is_dosearch filed true",input_file_idx_);
  return false;
}


/*
bool CfgHeuristicESSearch::DoSearch(int depth,
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

size_t CfgHeuristicESSearch::MinCflDistance
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

bool CfgHeuristicESSearch::FindAlongCfg(size_t i, unsigned int dist,
				      const SymbolicExecution& ex,
				      const set<branch_id_t>& bs) {
  const vector<branch_id_t>& path = ex.path().branches();
  // fprintf(stderr,"findalongcfg\n");

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


bool CfgHeuristicESSearch::SolveOnePathAlongCfg(Context& context) {
  // fprintf(stderr, "SolveOnePathAlongCfg\n");
  stack<SubContext>&stack = context.stack_sub_context;
  vector<value_t> input;
  while(!stack.empty()) {
    SubContext& sc = stack.top();
    vector<branch_id_t> path = sc.cur_ex.path().branches();
    // fprintf(stderr, "stack size : %u\n",stack.size());
    // fprintf(stderr, "cur_ex constraints size : %u\n", sc.cur_ex.path().constraints().size());
    // fprintf(stderr, "cur_idx : %u\n",sc.cur_idx);
    // fprintf(stderr, "next idxs size : %u\n",sc.idxs.size());
    // fprintf(stderr, "sc.b_idx : %u\n", sc.b_idx);
    // fprintf(stderr, "dist : %u\n",sc.dist);
/*
     if(sc.dist == 0) {
     fprintf(stderr, "dist : %u(pop)\n",sc.dist);
      stack.pop();
      continue;
     }
*/
  
    if(sc.idxs.empty()) { // idxs empty means next branches are not found
      bool found_path = false;
      // vector<size_t> idxs;
      {
        size_t pos = sc.cur_idx + 1;
        CollectNextBranches(path, &pos, &sc.idxs);
        // fprintf(stderr, "Branches following %d:", path[sc.cur_idx]);
        for (size_t j = 0; j < sc.idxs.size(); j++) {
          //    fprintf(stderr, " %d(%u,%u,%u)", path[sc.idxs[j]], sc.idxs[j],
          //       context.dist[path[sc.idxs[j]]], context.dist[paired_branch_[path[sc.idxs[j]]]]);
          if ((context.dist[path[sc.idxs[j]]] <= sc.dist)
              || (context.dist[paired_branch_[path[sc.idxs[j]]]] <= sc.dist))
            found_path = true;
        }
         //  fprintf(stderr, "\n");
      }

      if (!found_path) {
        // num_solve_no_paths_ ++;
        // fprintf(stderr, "not found path\n");
        stack.pop();
        if(!stack.empty()) {
          stack.top().b_idx++;
        }
        continue;
      } else {
        // fprintf(stderr, "found path\n");

     } 

      // bool all_concrete = true;
      // num_solve_all_concrete_ ++;

      // We will iterate through these indices in some order (random?
      // increasing order of distance? decreasing?), and try to force and
      // recurse along each one with distance no greater than max_dist.
      random_shuffle(sc.idxs.begin(), sc.idxs.end());
      for(int i = 0 ;i  < sc.idxs.size(); i++) {
        // fprintf(stderr,"idxs[%d]:%d\n", i, sc.idxs[i]);
      }
      // sc.b_idx = 0;

       // should set dist, current index -1,

    } else if (sc.idxs.size() > 0 && sc.b_idx < sc.idxs.size()) {
      // fprintf(stderr, "b_idx = %u\n", sc.b_idx);
      // fprintf(stderr, "dist_[%d](%u), sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);
       
      // point next index
      if((context.dist[path[sc.idxs[sc.b_idx]]] > sc.dist && (context.dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] > sc.dist))) {
          // fprintf(stderr, "dist_[%d](%u) > sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);
          sc.b_idx++;
          continue;
      }
      
      if (context.dist[path[sc.idxs[sc.b_idx]]] <= sc.dist ) {
          // fprintf(stderr, "dist_[%d](%u) <= sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);

            if(sc.seen.find(sc.b_idx)== sc.seen.end()) {
              // fprintf(stderr,"not seen %d,push \n", sc.b_idx);
              sc.seen.insert(sc.b_idx);
          //    if(sc.dist != 0) {
                // fprintf(stderr, "push sub context\n");
                stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist -1 , sc.cur_ex));
                continue;
           //   }
            } else {
              // fprintf(stderr,"already seen %d\n", sc.b_idx);
            }
            
          // sc.b_idx++;
      }

      // Find the constraint corresponding to branch idxs[*j].
      SymbolicExecution new_ex;
      // fprintf(stderr, "sc.idxs[%d]:%d\n",sc.b_idx, sc.idxs[sc.b_idx]);
      vector<size_t>::const_iterator idx =
        lower_bound(sc.cur_ex.path().constraints_idx().begin(),
        sc.cur_ex.path().constraints_idx().end(), sc.idxs[sc.b_idx]);
      for(int i = 0 ; i < sc.cur_ex.path().constraints_idx().size(); i++) {

        // fprintf(stderr, " constraint[%d] = %d\n", i, sc.cur_ex.path().constraints_idx()[i]);
      }
      if ((idx == sc.cur_ex.path().constraints_idx().end()) || (*idx != sc.idxs[sc.b_idx])) {
        // fprintf(stderr, "branch is concrete\n");
        sc.b_idx++;
        continue;  // Branch is concrete.
      }
         // fprintf(stderr, "branch is not concrete\n");
      size_t c_idx = idx - sc.cur_ex.path().constraints_idx().begin();
      if(context.dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] <= sc.dist) {
        if (!SolveAtBranch(sc.cur_ex, c_idx, &input)) {
         // fprintf(stderr, "unsat\n");
          //unsat
          sc.b_idx++;
          continue;
        }
        RunProgram(input, &new_ex);
        // fprintf(stderr, "RunProgram\n\n");
        if(UpdateCoverage(new_ex, context)) {
          context.latest_success_ex.Swap(new_ex);
      // context.latest_success_ex = new_ex;
          // stack.clear();
          // fprintf(stderr, "new coverage, pop\n");
          context.stack_sub_context = std::stack<SubContext>();
          // stack=std::stack<SubContext>();
          return true;
        }

        if (!CheckPrediction(sc.cur_ex, new_ex, sc.idxs[sc.b_idx])) {
          num_solve_pred_fails_ ++;
          fprintf(stderr, "Prediction failed\n");
          sc.b_idx++;
          // UpdateInputFileIdx();
          return false;
          // continue;
        }
        // Add To Stack
        // new SubContext subcontext //
        // stack.push( subcontext )
        // SymbolicExecution exex = new_ex;
        // stack.push(SubContext(sc.cur_idx, sc.dist-1, exex));
         // fprintf(stderr, "push newex\n");
         //if(sc.dist !=0) {
           if(sc.seen2.find(sc.b_idx)== sc.seen2.end()) {
              // fprintf(stderr,"not seen2 %d,push \n", sc.b_idx);
              sc.seen2.insert(sc.b_idx);
          //    if(sc.dist != 0) {
              // fprintf(stderr, "push sub context\n");
              stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist-1, new_ex));
              return false;
                // stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist -1 , sc.cur_ex));
                // continue;
           //   }
            } else {
              // fprintf(stderr,"already seen2 %d\n", sc.b_idx);
              sc.b_idx++;
            }
         //}
        // new_ex.Swap(sc.cur_ex);
        // return false because one execution ran
        return false;
      }
      // fprintf(stderr, "%d\n" , stack.top().cur_idx);
      sc.b_idx++;
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
bool CfgHeuristicESSearch::SolveAlongCfg(size_t i, unsigned int max_dist,
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

void CfgHeuristicESSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
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

void CfgHeuristicESSearch::CollectNextBranches
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


bool CfgHeuristicESSearch::DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex) {
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

      /*
      if (dist_[bid] == 0) {
        scoredBranches[i].second = 0;
      } else {
        scoredBranches[i].second = dist_[bid] + seen[bid];
        seen[bid] += 1;
      }
      */
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


}  // namespace crest
