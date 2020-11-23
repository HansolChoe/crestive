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

void Search::RunDirectory(const char *input_directory_name){
  fprintf(stderr, " RUn DirectorY\n");
  struct stat buffer;
  while(true){

    std::string s = std::string(input_directory_name) + "/input" + std::to_string(++num_iters_);
    if(stat(s.c_str(), &buffer) != 0) {
      fprintf(stderr, "%s does not exist\n", (std::string(input_directory_name) + "/input" + std::to_string(num_iters_)).c_str());
      break;
    }

    auto start = std::chrono::high_resolution_clock::now();
    setenv("CREST_INPUT_FILE_NAME", s.c_str(), 1);
    // c << "cp " << input_directory_name << "/input"<<num_iters_ << " input";
    // system(c.str().c_str());
    auto end = std::chrono::high_resolution_clock::now();
    elapsed_time_copy_ += (end - start);
    fprintf(stderr, "elapsed_time_copy: %.5f\n",elapsed_time_copy_.count() );
    // fprintf(stderr, " %s\n", c.str().c_str());

    start = std::chrono::high_resolution_clock::now();
    // int ret = system("./grep aaaaaaaaaaa /dev/null");
    int ret =system("./vim -m -n -Z -i NONE -u NONE");

    end = std::chrono::high_resolution_clock::now();

    // sleep 0.1 second
    usleep(10000);

    if (ret == -1 || WEXITSTATUS(ret) != 0) {
      error_count++;
    }


    fprintf(stderr, "ret = %d\n",WEXITSTATUS(ret));
    fprintf(stderr, "error_count = %u\n",error_count);

    elapsed_time_program_ += (end - start);

    std::chrono::duration<double> t = end -start;
    fprintf(stderr, "program time : %lf\n", t.count());

    // ifstream in("szd_execution", ios::in | ios::binary);

    // slepp 0.1 second
    // usleep(10000);
    // assert(in && run_ex.Parse(in));

    start = std::chrono::high_resolution_clock::now();
    ifstream in(("szd_execution"), ios::in | ios::binary);
    assert(in && run_ex.Parse(in));
    in.close();
    end = std::chrono::high_resolution_clock::now();
    elapsed_time_szd_read_ += (end - start);
    fprintf(stderr, "elapsed_time_szd_read_: %.5f\n",elapsed_time_szd_read_.count() );

    start = std::chrono::high_resolution_clock::now();
    UpdateCoverage(run_ex);
    end = std::chrono::high_resolution_clock::now();
    elapsed_time_update_ += (end - start);
    fprintf(stderr, "elapsed_time_update_: %.5f\n",elapsed_time_update_.count() );

    end_total_ = std::chrono::high_resolution_clock::now();
    elapsed_time_total_ = end_total_ - begin_total_;
    // fprintf(stderr, "Solving %2.f\n", elapsed_time_solving_);


  }
}

Search::Search(const string& program, int max_iterations)
  : program_(program), max_iters_(max_iterations), num_iters_(0) {
    error_count = 0;
  start_time_ = time(NULL);
  begin_total_ = std::chrono::high_resolution_clock::now();
  summary_time_ = 0;
  time_out_ = 600;
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
  // string file_path = std::string("inputs/") + file;
  string file_path;
  // FILE* f = fopen(file_path.c_str(), "w");
  // string file_path = "testcases/" + file;
  if(is_save_testcases_option_) {
      file_path = "testcases/input" + std::to_string(num_iters_);
  } else {
    file_path = "input";
  }
  // FILE* f = fopen("input", "w");
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

  string s;
  if(is_save_testcases_option_) {
    // std::stringstream s;
    // s << "cp input inputs/input" << num_iters_;
    // std::string s = "cp input testcases/input" + std::to_string(num_iters_);
    // system(s.str().c_str());
    s = "testcases/input" + std::to_string(num_iters_);
    fprintf(stderr, "s = %s\n", s.c_str());
  } else {
    s = "input";
  }
  setenv("CREST_INPUT_FILE_NAME", s.c_str(), 1);

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

  // map<const char *, const char*, cmp_str> program_names = {
  //   {"input1","./test"},
  //   {"input2","./test"}
  // };

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

   auto start = std::chrono::high_resolution_clock::now();
   // int ret =system("./vim -m -n -Z -i NONE -u NONE");
   int ret = system(program_.c_str());
   auto end = std::chrono::high_resolution_clock::now();
   // fprintf(stderr, "%s\n",input_file_names_[input_file_idx_].c_str());
   // fprintf(stderr, "%s\n",program_names[input_file_names_[input_file_idx_].c_str()]);
   // system(program_.c_str());
   std::chrono::duration<double> t = end -start;
   // fprintf(stderr, "program time : %lf\n", t.count());
  elapsed_time_program_ += (end - start);
  if (ret == -1 || WEXITSTATUS(ret) != 0) {
    error_count++;
  }
  // fprintf(stderr, "ret = %d\n",WEXITSTATUS(ret));
  // fprintf(stderr, "error_count = %u\n",error_count);

  // fprintf( stderr , " time program : %.2f\n", elapsed_time_program_.count());
  // system(program_.c_str());

}


void Search::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  end_total_ = std::chrono::high_resolution_clock::now();
  elapsed_time_total_ = end_total_ - begin_total_;
  // fprintf(stderr, "Solving %2.f\n", elapsed_time_solving_);
  // fprintf(stderr, "Searching %.2f\n", (elapsed_time_total_.count() - (elapsed_time_solving_.count() + elapsed_time_program_.count())));

  // fprintf(stderr, "inputs\n");
  // for(size_t i = 0 ; i < inputs.size(); i++) {
  //   fprintf(stderr, "%d\n", inputs[i]);
  // }
  if (++num_iters_ > max_iters_ || elapsed_time_total_.count() >= time_out_) {
    fprintf(stderr, "max Q size = %u\n", max_Q_size);
    fprintf(stderr, "# of all pf branches:\n");
    for (auto i : pf_count_) {
        fprintf(stderr, "%u,%u\n", i.first, i.second);
    }
    fprintf(stderr, "\n# of (pf >= 10) branches:\n");
    for (auto i : pf_count_) {
      if(i.second > 10) {
        fprintf(stderr, "%u,%u\n", i.first, i.second);
      }
    }

    fprintf(stderr, "\n# of all unsat branches:\n");
    for (auto i : unsat_count_) {
        fprintf(stderr, "%u,%u\n", i.first, i.second);
    }
    fprintf(stderr, "\n# of (unsat >= 10) branches:\n");
    for (auto i : unsat_count_) {
      if(i.second > 10) {
        fprintf(stderr, "%u,%u\n", i.first, i.second);
      }
    }
      exit(0);
  }

  // Run the program.
  LaunchProgram(inputs);

  // ifstream in(("se/ex_" + input_file_names_[input_file_idx_]), ios::in | ios::binary);
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
  // __crest_input_file_name = std::string(getenv("CREST_INPUT_FILE_NAME")).c_str();


  FILE *f = fopen("log1", "a");
  if (!f) {
    fprintf(stderr, "Writing logging, failed to open %s. \n", "log1");
    return found_new_branch;
  }



  fprintf(f, "%u,%.2lf,%u,%u\n",
          total_num_covered_,
          time_diff,
          num_prediction_fail_,
          num_unsat_
         );
    // fprintf(ff, "%u,%.2lf,%u,%u,%u,%u,%u,%u,%.2f,%.2f,%2.f\n",
    //  total_num_covered_, time_diff, num_prediction_fail_, Q.size(), current_target_branch_size,covered_branches_.size(),ex.path().constraints_idx().size(), ex.path().branches().size()
    //  ,elapsed_time_total_.count()-(elapsed_time_program_.count()+elapsed_time_solving_.count()), elapsed_time_solving_.count(), elapsed_time_program_.count()
    // );
  fclose(f);

  while(summary_time_ <= time_diff.count()) {
    FILE *ff = fopen("summary1", "a");
    if (!ff) {
      fprintf(stderr, "Writing summary, failed to open %s. \n", "summary1");
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

  // auto time_diff = end_total_ - begin_total_;
  // while(coverage_log_time_ <= time_diff.count()) {
  //   std::stringstream s;
  //   s << "cp coverage coverages/coverage" << coverage_log_time_;
  //   system(s.str().c_str());
  //   coverage_log_time_ += 10;
  //   printf("summary %ld\n",coverage_log_time_);
  // }
  // auto end = std::chrono::high_resolution_clock::now();
  // elapsed_time_searching_9_ += (end - start);
  // fprintf(stderr, "elapsed_time_searching_9(UpdateCoverage) : %.2f\n", elapsed_time_searching_9_.count() );

  return found_new_branch;
}

bool RandomCSSearch::UpdateCoverage(const SymbolicExecution& ex, EXContext &context) {
  return UpdateCoverage(ex, NULL, context);
}

bool RandomCSSearch::UpdateCoverage(const SymbolicExecution& ex,
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
  FILE *f = fopen("log1", "a");
  if (!f) {
    fprintf(stderr, "Writing logging, failed to open %s. \n", "log1");
    return found_new_branch;
  }
  //fprintf(f, "%u,%.2lf,%u,%u,%u\n", total_num_covered_, time_diff, num_prediction_fail_,num_constraints_size_, num_unsat_);

//  fprintf(f, "%u,%.2lf,%u,%u,%u\n", total_num_covered_,time_diff ,num_prediction_fail_,Q.size(),uncovered_branches_.size());
    // fprintf(f, "%u,%.2lf,%u,%u,%u\n", total_num_covered_,time_diff ,num_prediction_fail_,Q.size(),u.size());
    //
    fprintf(f, "%u,%.2lf,%u,%u,%u,%u\n",
          total_num_covered_,
          time_diff,
          num_prediction_fail_,
          num_unsat_,
          Q.size(),
          context.energy);

     max_Q_size = std::max(max_Q_size, Q.size());

     fclose(f);

  while(summary_time_ <= time_diff.count()) {
    FILE *ff = fopen("summary1", "a");
    if (!ff) {
      fprintf(stderr, "Writing summary, failed to open %s. \n", "summary1");
      return found_new_branch;
    }

 fprintf(ff, "%u,%.2lf,%u,%u,%u,%u\n",
          total_num_covered_,
          time_diff,
          num_prediction_fail_,
          num_unsat_,
          Q.size(),
          context.energy);

     max_Q_size = std::max(max_Q_size, Q.size());

    // end_total_ = std::chrono::high_resolution_clock::now();
    fclose(ff);
    summary_time_ += 10;
  }

  // auto time_diff = end_total_ - begin_total_;
  // while(coverage_log_time_ <= time_diff.count()) {
  //   std::stringstream s;
  //   s << "cp coverage coverages/coverage" << coverage_log_time_;
  //   system(s.str().c_str());
  //   coverage_log_time_ += 10;
  //   printf("summary %ld\n",coverage_log_time_);
  // }

  return found_new_branch;
}

bool CfgHeuristicCSSearch::UpdateCoverage(const SymbolicExecution& ex, Context &context) {
  return UpdateCoverage(ex, NULL, context);
}

bool CfgHeuristicCSSearch::UpdateCoverage(const SymbolicExecution& ex,
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
  // end = std::chrono::high_resolution_clock::now();
  // // auto end = std::chrono::high_resolution_clock::now();
  // elapsed_time_searching_9_ += (end - start);
  // fprintf(stderr, "elapsed_time_searching_9(UpdateCoverage) : %.5f\n", elapsed_time_searching_9_.count() );


  fprintf(stderr, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);

      // PrintPathConstraint(ex.path());
    // fprintf(stderr, "num_covered2 : %u\n", context.num_covered);
  bool found_new_branch = (context.num_covered > prev_covered_);
// start = std::chrono::high_resolution_clock::now();
  if (found_new_branch) {
     WriteCoverageToFileOrDie("coverage");
  } else {

 }

  end_total_ = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> time_diff = end_total_ - begin_total_;
  // auto start = std::chrono::high_resolution_clock::now();
  FILE *f = fopen("log1", "a");

  if (!f) {
    fprintf(stderr, "Writing logging, failed to open %s. \n", "log1");
    return found_new_branch;
  }
     fprintf(f, "%u,%.2lf,%u,%u,%u,%u\n",
          total_num_covered_,
          time_diff,
          num_prediction_fail_,
          num_unsat_,
          Q.size() - num_no_target_contexts_,
          context.energy);

     max_Q_size = std::max(max_Q_size, Q.size() - num_no_target_contexts_);
  // auto end = std::chrono::high_resolution_clock::now();
  // auto end = std::chrono::high_resolution_clock::now();
  // elapsed_time_searching_11_ += (end - start);
  // fprintf(stderr, "elapsed_time_searching_11(UpdateCoverage) : %.5f\n", elapsed_time_searching_11_.count() );

  fclose(f);




  while(summary_time_ <= time_diff.count()) {
    FILE *ff = fopen("summary1", "a");
    if (!ff) {
      fprintf(stderr, "Writing summary, failed to open %s. \n", "summary1");
      return found_new_branch;
    }
    fprintf(ff, "%u,%.2lf,%u,%u,%u,%u\n",
         total_num_covered_,
         time_diff,
         num_prediction_fail_,
         num_unsat_,
         Q.size() - num_no_target_contexts_,
         context.energy);
    // end_total_ = std::chrono::high_resolution_clock::now();
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
  auto start = std::chrono::high_resolution_clock::now();
  success = Z3Solver::IncrementalSolve(ex.inputs(), ex.vars(), cs, &soln);
  auto end = std::chrono::high_resolution_clock::now();
  elapsed_time_solving_ += (end - start);
  // fprintf(stderr, "elapsed_time_solving_ : %f\n", elapsed_time_solving_.count() );
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
    if(is_save_testcases_option_) {
      string s = "cp seeds/input1 input" + std::to_string(num_iters_ + 1);
      system(s.c_str());
    } else {
      string s = "cp seeds/input1 input";
      system(s.c_str());
    }
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
    system("cp -r seeds/input1 input");
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
  //// RandomCSSearch ////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////

  size_t RandomCSSearch::AssignEnergy(EXContext &c) {
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

// energy 1 (**not** context individual count)
void RandomCSSearch::Run2() {
    size_t idx = 0;
    while(true) {
        system("cp seeds/input1 input");
        SymbolicExecution *next_ex = new SymbolicExecution();
        vector<value_t> next_input;
        covered_.assign(max_branch_, false);
        reachable_branches_set_.clear();
        covered_branches_.clear();
        fprintf(stderr, "RESET\n");
        RunProgram(next_input, next_ex);

        set<branch_id_t> uncovered_branches;
        for (const size_t &i: next_ex->path().constraints_idx()) {
            covered_branches_.insert(next_ex->path().branches()[i]);
            uncovered_branches.insert(paired_branch_[next_ex->path().branches()[i]]);
        }
        SymbolicExecution *ex = new SymbolicExecution();
        next_ex->clone(*ex);
        Q.push_back(EXContext(ex, uncovered_branches));
        if(UpdateCoverage(*next_ex, Q.front())) {
            fprintf(stderr, "found new branch \n");
        }
        size_t count = 0;
        while (!Q.empty() && count++ < 10000) {
          fprintf(stderr,"Q size %zu\n", Q.size());
            EXContext c = Q.front();
            Q.pop_front();
            set<branch_id_t> cur_target_branches;
            set_difference(
                    c.target_branches.begin(),
                    c.target_branches.end(),
                    covered_branches_.begin(),
                    covered_branches_.end(),
                    std::inserter(cur_target_branches,cur_target_branches.end())
                    );
            // fprintf(stderr,"cur_target_branches size %zu\n", cur_target_branches.size());
            if(cur_target_branches.empty()) {
                fprintf(stderr,"Q size %zu\n", Q.size());
                delete c.ex;
                continue;
            } else {
                c.target_branches = cur_target_branches;
            }
            bool search_failed = false;
            for(size_t i = AssignEnergy(c); i > 0; i--) {
                if (SolveRandomBranch(*c.ex, &next_input, &idx)) {
                    RunProgram(next_input, next_ex);
                    // Update B
                    for (const size_t &i: next_ex->path().constraints_idx()) {
                        covered_branches_.insert(next_ex->path().branches()[i]);
                    }
                    if(UpdateCoverage(*next_ex, c)) {
                        fprintf(stderr, "found new branch \n");
                        count=0;
                    } else {
                      count++;
                    }
                    fprintf(stderr,"count : %zu\n", count);

                    if(!CheckPrediction(*c.ex, *next_ex, c.ex->path().constraints_idx()[idx]) ) {
                        // pf_count_[c.ex.path().branches()[c.ex.path().constraints_idx()[idx]]]++;
                        fprintf(stderr, "Prediction Failure!\n");
                        // fprintf(stderr, "%u\n", pf_count_[c.ex.path().branches()[c.ex.path().constraints_idx()[idx]]]++;
                    }
                    set<branch_id_t> current_uncovered_branches;
                    for (const size_t &i: next_ex->path().constraints_idx()) {
                        branch_id_t b = next_ex->path().branches()[i];
                        if(!covered_[paired_branch_[b]]) {
                            current_uncovered_branches.insert(paired_branch_[b]);
                        }
                    }
                    set<branch_id_t> u;
                    set_difference(
                            current_uncovered_branches.begin(),
                            current_uncovered_branches.end(),
                            c.target_branches.begin(),
                            c.target_branches.end(),
                            std::inserter(u,u.end())
                            );
                    for(const EXContext &cc: Q) {
                        set<branch_id_t> tmp;
                        set_difference(
                                u.begin(),
                                u.end(),
                                cc.target_branches.begin(),
                                cc.target_branches.end(),
                                std::inserter(tmp,tmp.end())
                                );
                        u = tmp;
                    }
                    if(u.size() > 0 ) {
                      fprintf(stderr ,"uncovered branches size : %zu\n", u.size());

                        SymbolicExecution *pe = new SymbolicExecution();
                        next_ex->clone(*pe);
                        Q.push_back(EXContext(pe, u));
                    }
                    SymbolicExecution *pe = c.ex;
                    c.ex = next_ex;
                    next_ex = pe;
                } else {
                    search_failed = true;
                    break;
                }
            }
            if(!search_failed
                    && !c.target_branches.empty()
                    && next_ex->path().branches() != c.ex->path().branches()) {
                Q.push_back(EXContext(c.ex, c.target_branches));
            }
            else {
                fprintf(stderr, "No enqueue again\n");
                if (search_failed) {
                    fprintf(stderr, "T1: search failed\n");
                }
                if (c.target_branches.empty()) {
                    fprintf(stderr, "T2: target branches is empty\n");
                }
                if (next_ex->path().branches() == c.ex->path().branches()) {
                    fprintf(stderr, "T3: branch is same\n");
                }
                delete c.ex;
            }
            // for (const branch_id_t &b: c.target_branches) {
            //   if(covered_[b]) {
            //     c.target_branches.remove(b);
            //   }
            // }
            // for(set<int>::iterator it=uncovered_branches_.begin(); it!=uncovered_branches_.end(); ++it) {
            //   if(covered_[*it]) {
            //     uncovered_branches_.erase(it);
            //   }
            // }
        }
        // flush all contexts
        fprintf(stderr, "Empty Q\n");
        while(!Q.empty()) {
          EXContext c = Q.front();
          Q.pop_front();
          delete c.ex;
          break;
        }

        delete next_ex;
    }
}

void RandomCSSearch::Run() {
    size_t idx = 0;
    while(true) {
        system("cp -r seeds/input1 input");
        SymbolicExecution *next_ex = new SymbolicExecution();
        vector<value_t> next_input;
        covered_.assign(max_branch_, false);
        reachable_branches_set_.clear();
        covered_branches_.clear();
        fprintf(stderr, "RESET\n");
        RunProgram(next_input, next_ex);

        set<branch_id_t> uncovered_branches;
        for (const size_t &i: next_ex->path().constraints_idx()) {
            covered_branches_.insert(next_ex->path().branches()[i]);
            uncovered_branches.insert(paired_branch_[next_ex->path().branches()[i]]);
        }
        SymbolicExecution *ex = new SymbolicExecution();
        next_ex->clone(*ex);
        Q.push_back(EXContext(ex, uncovered_branches));
        if(UpdateCoverage(*next_ex, Q.front())) {
            fprintf(stderr, "found new branch \n");
        }
        // size_t count = 0;
        // while (count++ < 10000) {
        while (Q.size()!= 0) {
          fprintf(stderr,"Q size %zu\n", Q.size());
            EXContext c = Q.front();
            Q.pop_front();
            set<branch_id_t> cur_target_branches;
            if(c.count >= 10000) {
              bool all_other_contexts_failed = true;
              for(size_t i = 0 ; i < Q.size() ; i++) {
                EXContext &ex_context = Q[i];
                if (ex_context.count < 10000) {
                  all_other_contexts_failed = false;
                  break;
                }
              }
              if (all_other_contexts_failed) {
                while(!Q.empty()) {
                  EXContext c = Q.front();
                  Q.pop_front();
                  delete c.ex;
                  break;
                }
              }
              // if(c.count >= 10) {
                  fprintf(stderr, "skip a context\n");
                  EXContext(c.ex, c.target_branches,c.count);
                  fprintf(stderr, "count : %u\n", Q.front().count);
                  continue;
              // }
            }
            set_difference(
                    c.target_branches.begin(),
                    c.target_branches.end(),
                    covered_branches_.begin(),
                    covered_branches_.end(),
                    std::inserter(cur_target_branches,cur_target_branches.end())
                    );
            // fprintf(stderr,"cur_target_branches size %zu\n", cur_target_branches.size());
            if(cur_target_branches.empty()) {
                fprintf(stderr,"Q size %zu\n", Q.size());
                delete c.ex;
                continue;
            } else {
                c.target_branches = cur_target_branches;
            }
            bool search_failed = false;
            for(size_t i = AssignEnergy(c); i > 0 && c.count < 10000; i--) {
                if (SolveRandomBranch(*c.ex, &next_input, &idx)) {
                    RunProgram(next_input, next_ex);
                    // Update B
                    for (const size_t &i: next_ex->path().constraints_idx()) {
                        covered_branches_.insert(next_ex->path().branches()[i]);
                    }
                    if(UpdateCoverage(*next_ex, c)) {
                        fprintf(stderr, "found new branch \n");
                        c.count=0;
                    } else {
                      c.count++;
                    }
                    fprintf(stderr,"c.count : %zu\n", c.count);

                    if(!CheckPrediction(*c.ex, *next_ex, c.ex->path().constraints_idx()[idx]) ) {
                        // pf_count_[c.ex.path().branches()[c.ex.path().constraints_idx()[idx]]]++;
                        fprintf(stderr, "Prediction Failure!\n");
                        // fprintf(stderr, "%u\n", pf_count_[c.ex.path().branches()[c.ex.path().constraints_idx()[idx]]]++;
                    }
                    set<branch_id_t> current_uncovered_branches;
                    for (const size_t &i: next_ex->path().constraints_idx()) {
                        branch_id_t b = next_ex->path().branches()[i];
                        if(!covered_[paired_branch_[b]]) {
                            current_uncovered_branches.insert(paired_branch_[b]);
                        }
                    }
                    set<branch_id_t> u;
                    set_difference(
                            current_uncovered_branches.begin(),
                            current_uncovered_branches.end(),
                            c.target_branches.begin(),
                            c.target_branches.end(),
                            std::inserter(u,u.end())
                            );
                    for(const EXContext &cc: Q) {
                        set<branch_id_t> tmp;
                        set_difference(
                                u.begin(),
                                u.end(),
                                cc.target_branches.begin(),
                                cc.target_branches.end(),
                                std::inserter(tmp,tmp.end())
                                );
                        u = tmp;
                    }
                    if(u.size() > 0 ) {
                      fprintf(stderr ,"uncovered branches size : %zu\n", u.size());

                        SymbolicExecution *pe = new SymbolicExecution();
                        next_ex->clone(*pe);
                        Q.push_back(EXContext(pe, u));

                       // SymbolicExecution
                       //     Q.push_back(EXContext(next_ex, u));
                    }
                    SymbolicExecution *pe = c.ex;
                    c.ex = next_ex;
                    next_ex = pe;
                } else {
                    search_failed = true;
                    break;
                }
            }
            if(!search_failed
                    && !c.target_branches.empty()
                    && next_ex->path().branches() != c.ex->path().branches()) {
                Q.push_back(EXContext(c.ex, c.target_branches,c.count));
            }
            else {
                fprintf(stderr, "No enqueue again\n");
                if (search_failed) {
                    fprintf(stderr, "T1: search failed\n");
                }
                if (c.target_branches.empty()) {
                    fprintf(stderr, "T2: target branches is empty\n");
                }
                if (next_ex->path().branches() == c.ex->path().branches()) {
                    fprintf(stderr, "T3: branch is same\n");
                }
                delete c.ex;
            }
            // for (const branch_id_t &b: c.target_branches) {
            //   if(covered_[b]) {
            //     c.target_branches.remove(b);
            //   }
            // }
            // for(set<int>::iterator it=uncovered_branches_.begin(); it!=uncovered_branches_.end(); ++it) {
            //   if(covered_[*it]) {
            //     uncovered_branches_.erase(it);
            //   }
            // }
        }

        delete next_ex;
    }
}

  bool RandomCSSearch::SolveRandomBranch(SymbolicExecution &ex, vector<value_t>* next_input, size_t* idx) {
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
  //// CfgHeuristicCSSearch //////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////

  size_t CfgHeuristicCSSearch::AssignEnergy(Context &c) {
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

  CfgHeuristicCSSearch::CfgHeuristicCSSearch(const string& program, int max_iterations) : Search(program, max_iterations),
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

  CfgHeuristicCSSearch::~CfgHeuristicCSSearch() { }

  void CfgHeuristicCSSearch::UpdateCurContext() {
    fprintf(stderr, "Size of Q : %u\n", Q.size() - num_no_target_contexts_);
    fprintf(stderr, "cur energy : %u\n", Q[context_idx_].energy);
    fprintf(stderr, "cur context : %u\n", context_idx_);
    assert(Q.size()!=0);
    if( Q[context_idx_].energy > 0) {
      --Q[context_idx_].energy;
    } else {
      // energy is 0
      // check all contexts are marked
      while (Q.size()!=0) {
        context_idx_ = (context_idx_ + 1) % Q.size();
        bool is_all_contexts_failed = true;
        for(Context &c : Q) {
          if (!c.is_do_search_failed) {
            is_all_contexts_failed = false;
            break;
          }
        }
        if(is_all_contexts_failed) {

          return;
        } else {

        }
        while (Q[context_idx_].is_do_search_failed) {
          context_idx_ = (context_idx_ + 1) % Q.size();
          fprintf(stderr, "cur context : %u\n", context_idx_);
        }

        Context &context = Q[context_idx_ % Q.size()];
        // cur_context = Q[context_idx_];
        set<branch_id_t> target_branches;
        //


        set_difference(
          context.target_branches.begin(),
          context.target_branches.end(),
          covered_branches_.begin(),
          covered_branches_.end(),
          std::inserter(target_branches,target_branches.end())
        );
        if(!target_branches.empty()) {
          // fprintf(stderr, "333\n");
          context.target_branches = target_branches;
          context.energy = AssignEnergy(context);
          // fprintf(stderr, "aaaa num_covered : %u\n", context.num_covered);
          context.num_covered = num_covered_;
          context.covered = covered_;
          UpdateBranchDistances(context.covered, context.dist);
          // fprintf(stderr, "current energy2 : %u\n", context.energy);
          // fprintf(stderr, "current energy3 : %u\n", Q[context_idx_].energy);
          // auto end = std::chrono::high_resolution_clock::now();
          // elapsed_time_searching_7_ += (end - start);
          // fprintf(stderr, "elapsed_time_searching_7 : %.5f\n", elapsed_time_searching_7_.count() );
          return;
        } else {
          fprintf(stderr, "erase %u\n", context_idx_);
          context.energy = 0;
          context.is_do_search_failed = true;
          num_no_target_contexts_++;
        }
      }
    }
  }

  void CfgHeuristicCSSearch::GetNewTargetBranches(SymbolicExecution &next_ex,set<branch_id_t> &u){
    // auto start = std::chrono::high_resolution_clock::now();
    set<branch_id_t> current_uncovered_branches;
    for (const size_t &i: next_ex.path().constraints_idx()) {
      branch_id_t b = next_ex.path().branches()[i];
      if(!covered_[paired_branch_[b]]) {
      current_uncovered_branches.insert(paired_branch_[b]);
      }
    }
    set_difference(
       current_uncovered_branches.begin(),
       current_uncovered_branches.end(),
       covered_branches_.begin(),
       covered_branches_.end(),
       std::inserter(u,u.end())
      );
      //
    for(const Context &c: Q) {
      set<branch_id_t> tmp;
      set_difference(
         u.begin(),
         u.end(),
         c.target_branches.begin(),
         c.target_branches.end(),
         std::inserter(tmp,tmp.end())
        );
        u = tmp;
    }
    // auto end = std::chrono::high_resolution_clock::now();
    // elapsed_time_searching_3_ += (end - start);
    //
  }

  void CfgHeuristicCSSearch::Run() {
    // v_context_.resize(input_file_names_.size());
    num_covered_ = 0;
    // string names[] = {"input1", "input10", "input2", "input3", "input4", "input5", "input6", "input7", "input8", "input9"};
    string names[] = {"input1", "input10", "input2", "input3", "input4", "input5", "input6", "input7", "input8", "input9"};
    // deque<Context> Q;
    // size_t context_idx = 0;
    covered_.resize(max_branch_, false);
    max_Q_size = 0;
    while(true) {
      {
        // check all contexts are marked

        bool is_all_contexts_failed = true;
        for(Context &c : Q) {
          if (!c.is_do_search_failed) {
            is_all_contexts_failed = false;
            break;
          }
        }

        // RESET Search
        if (is_all_contexts_failed) {
          fprintf(stderr, "RESET Search\n");
          // system("rm -r inputs");
          // system("cp -r seeds inputs");
          system("cp -r seeds/input1 input");
          if(is_save_testcases_option_) {
            // string s = "touch testcases/input" + std::to_string(num_iters_ + 1);
            string s = "cp seeds/input1 testcases/input" + std::to_string(num_iters_+1);
            std::cerr << s << '\n';
            system(s.c_str());
          }
          // RESET global data structures
          // Q.clear();
          num_no_target_contexts_ = 0;
          Q = deque<Context>();
          context_idx_ = 0;
          // pf_count_.clear();
          covered_branches_.clear();
          covered_.assign(max_branch_, false);
          Q.emplace_back();
          Context &new_context = Q.front();
          new_context.covered.resize(max_branch_, false);
          new_context.dist.resize(max_branch_, 0);
          RunProgram(vector<value_t>(), &new_context.cur_ex);
          for(BranchIt i = new_context.cur_ex.path().branches().begin(); i!=new_context.cur_ex.path().branches().end(); i++) {
            new_context.target_branches.insert(*i);
          }
          if (UpdateCoverage(new_context.cur_ex, new_context) ) {
            // fprintf(stderr, "found new branch\n");
          } else {
            // fprintf(stderr, "not found new branch\n");
          }

          UpdateBranchDistances(new_context.covered, new_context.dist);
          UpdateCurContext();
        }
        if(Q[context_idx_].stack_sub_context.empty()) {

          // auto start = std::chrono::high_resolution_clock::now();
          if(DoSearchOnce()) {
            // Context &cur_context = Q[context_idx_];
            Q[context_idx_].cur_ex.Swap(Q[context_idx_].latest_success_ex);
            Q[context_idx_].iters=30;
            Q[context_idx_].cur_idx = 0;
            Q[context_idx_].scoredBranches.clear();
            Q[context_idx_].do_search_once_found_new_branch = false;
            Q[context_idx_].new_branches.clear();
            Q[context_idx_].covered = covered_;

            UpdateBranchDistances(Q[context_idx_].covered, Q[context_idx_].dist);
            UpdateCurContext();

          } else {
            // 1. 새로운 브랜치를 못찾고, prediction failure
            // 2. FindAlongCfg 성공후 stack에 추가
            // 3. Do search fail ( execution 종료)
            if (Q[context_idx_].is_do_search_failed) {
              fprintf(stderr, "do search failed skip %u\n", context_idx_);
              Q[context_idx_].energy = 0;
              UpdateCurContext();
            }
          }
          // auto end = std::chrono::high_resolution_clock::now();
          // elapsed_time_searching_4_ += (end - start);
          // fprintf(stderr, "elapsed_time_searching_4(DoSearch): %.2f\n", elapsed_time_searching_4_ );
        } else {
          // fprintf(stderr,"stack is not empty\n");

          if(!SolveOnePathAlongCfg()) {
            if(!Q[context_idx_].stack_sub_context.empty()) {
                // Keep solve one path along cfg
                UpdateCurContext();
            } else { // stack is empty
              if(Q[context_idx_].do_search_once_found_new_branch) {
                 Q[context_idx_].covered = covered_;
                 UpdateBranchDistances(Q[context_idx_].covered, Q[context_idx_].dist);
                 Q[context_idx_].cur_ex.Swap(Q[context_idx_].latest_success_ex);
                 Q[context_idx_].new_branches.clear();
                 Q[context_idx_].scoredBranches.clear();
                 Q[context_idx_].iters=30;
                 Q[context_idx_].cur_idx = 0;

                 UpdateCurContext();
              } else {

                Q[context_idx_].cur_idx++;
                UpdateCurContext();
              }
              Q[context_idx_].do_search_once_found_new_branch = false;
            }
          } else {
            // Solve One Path Along Cfg Success
            // We empty the stack
            std::stack<SubContext*> &stack = Q[context_idx_].stack_sub_context;
            while(!stack.empty()) {
              delete stack.top();
              stack.pop();
            }

            UpdateBranchDistances(Q[context_idx_].covered, Q[context_idx_].dist);
            Q[context_idx_].cur_ex.Swap(Q[context_idx_].latest_success_ex);
            Q[context_idx_].scoredBranches.clear();
            Q[context_idx_].new_branches.clear();
            Q[context_idx_].cur_idx = 0;
            Q[context_idx_].iters=30;
            UpdateCurContext();
          }
        }
      }
    }
  }


  void CfgHeuristicCSSearch::UpdateBranchDistances(vector<bool>& covered, vector<long unsigned int>& dist) {
    // We run a BFS backward, starting simultaneously at all uncovered vertices.
    // fprintf(stderr, "covered size: %u, dist size %u", covered.size(), dist.size());
    // auto start = std::chrono::high_resolution_clock::now();
    queue<branch_id_t> Q;
    for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
      // if (!all_covered_[*i]) {
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

    // auto end = std::chrono::high_resolution_clock::now();
    // elapsed_time_searching_1_ += (end - start);
    // fprintf(stderr, "elapsed_time_searching_1(UpdateBranchDistances) : %.2f\n", elapsed_time_searching_1_.count() );
  }


  bool CfgHeuristicCSSearch::DoSearchOnce() {
    // Context &context = Q[context_idx_];
    if(Q[context_idx_].scoredBranches.empty()) {
      // fprintf(stderr, "scoredBranches is empty\n");
      // auto start = std::chrono::high_resolution_clock::now();
      Q[context_idx_].covered = covered_;
      Q[context_idx_].scoredBranches.resize(Q[context_idx_].cur_ex.path().constraints().size());
      for (size_t i = 0; i < Q[context_idx_].scoredBranches.size(); i++) {
        Q[context_idx_].scoredBranches[i].first = i;
      }

      { // Compute (and sort by) the scores.
         // fprintf(stderr,"start computing scores\n");
        random_shuffle(Q[context_idx_].scoredBranches.begin(), Q[context_idx_].scoredBranches.end());
        map<branch_id_t,int> seen;
        for (size_t i = 0; i < Q[context_idx_].scoredBranches.size(); i++) {
          // fprintf(stderr, "%u ", i);
          size_t idx = Q[context_idx_].scoredBranches[i].first;

          size_t branch_idx = Q[context_idx_].cur_ex.path().constraints_idx()[idx];

          branch_id_t bid = paired_branch_[Q[context_idx_].cur_ex.path().branches()[branch_idx]];
          Q[context_idx_].scoredBranches[i].second = Q[context_idx_].dist[bid] + seen[bid];
          seen[bid] += 1;
        }
      }
      // fprintf(stderr, "\n");

      stable_sort(Q[context_idx_].scoredBranches.begin(), Q[context_idx_].scoredBranches.end(), ScoredBranchComp());

      // auto end = std::chrono::high_resolution_clock::now();
      // elapsed_time_searching_6_ += (end - start);
      // fprintf(stderr, "elapsed_time_searching_6(scored branch calculate) : %.2f\n", elapsed_time_searching_6_.count() );

    } else {

    }

    // Solve.
    SymbolicExecution new_ex;
    vector<value_t> input;
    // for (size_t i = 0; i < scoredBranches.size(); i++) {
    while(Q[context_idx_].cur_idx < Q[context_idx_].scoredBranches.size()) {

      if ((Q[context_idx_].iters <= 0) ||
       (Q[context_idx_]
         .scoredBranches[Q[context_idx_]
         .cur_idx]
         .second > kInfiniteDistance)) {
            Q[context_idx_].is_do_search_failed = true;

            return false;
      }
      num_inner_solves_ ++;

      if (!SolveAtBranch(Q[context_idx_].cur_ex, Q[context_idx_].scoredBranches[Q[context_idx_].cur_idx].first, &input)) { // Unsat

        Q[context_idx_].cur_idx++;
        continue;
      }
      RunProgram(input, &new_ex);

      Q[context_idx_].iters--;

      // fprintf(stderr, "iters = %d\n", Q[context_idx_].iters);

      size_t b_idx = Q[context_idx_].cur_ex.path().constraints_idx()[Q[context_idx_].scoredBranches[Q[context_idx_].cur_idx].first];
      branch_id_t bid = paired_branch_[Q[context_idx_].cur_ex.path().branches()[b_idx]];
      bool found_new_branch = UpdateCoverage(new_ex, &(Q[context_idx_].new_branches), Q[context_idx_]);
      set<branch_id_t> new_target_branches;
      GetNewTargetBranches(new_ex, new_target_branches);
      if(!new_target_branches.empty()) {
          Context &newContext = *(Q.emplace(Q.begin() + context_idx_));
          newContext.target_branches = new_target_branches;
          Q[context_idx_ + 1].clone(newContext);
          context_idx_++;
      }
      bool prediction_failed = !CheckPrediction(Q[context_idx_].cur_ex, new_ex, b_idx);
      if (found_new_branch && prediction_failed) {
        num_inner_lucky_successes_ ++;
        num_inner_successes_pred_fail_ ++;

        Q[context_idx_].latest_success_ex.Swap(new_ex);
        return true;
      }
      if (found_new_branch && !prediction_failed) {
        size_t min_dist = MinCflDistance(b_idx, new_ex, Q[context_idx_].new_branches);
        if (FindAlongCfg(b_idx, Q[context_idx_].dist[bid], new_ex, Q[context_idx_].new_branches)) {
        	assert(min_dist <= Q[context_idx_].dist[bid]);
        	if (Q[context_idx_].dist[bid] == 0) {
        	  num_inner_zero_successes_ ++;
        	} else {
        	  num_inner_nonzero_successes_ ++;
        	}
        	Q[context_idx_].latest_success_ex.Swap(new_ex);
        	return true;
        } else {
        	// We got lucky, but as long as there were no prediction failures,
        	// we'll finish the CFG search to see if that works, too.
        	assert(min_dist > Q[context_idx_].dist[bid]);
        	assert(Q[context_idx_].dist[bid] != 0);
        	num_inner_lucky_successes_ ++;
        }
      }
      if (prediction_failed) {
        fprintf(stderr, "Prediction failed.\n");
        if (!found_new_branch) {
  	      num_inner_pred_fails_ ++;
           Q[context_idx_].cur_idx++;
           UpdateCurContext();
           return false;
        }
      }
      num_top_solves_ ++;
      num_top_solve_successes_ ++;
      // Q[context_idx_].stack_sub_context.push(SubContext(b_idx, Q[context_idx_].scoredBranches[Q[context_idx_].cur_idx].second -1));
      Q[context_idx_].stack_sub_context.push(new SubContext(b_idx, Q[context_idx_].scoredBranches[Q[context_idx_].cur_idx].second -1, &new_ex));
      // new_ex.clone((Q[context_idx_].stack_sub_context.top().cur_ex));
      if (found_new_branch) {
        Q[context_idx_].latest_success_ex.Swap(new_ex);
        Q[context_idx_].do_search_once_found_new_branch = true;
      } else {
        Q[context_idx_].do_search_once_found_new_branch = false;
      }
      return false;
    }
    // context.is_reset = true;
    // fprintf(stderr,"set context[%d]'s is_dosearch filed true",input_file_idx_);
    Q[context_idx_].is_do_search_failed = true;
    return false;
  }


  bool CfgHeuristicCSSearch::SolveOnePathAlongCfg() {
    // Context &context = Q[context_idx_];
    stack<SubContext*>&stack = Q[context_idx_].stack_sub_context;
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
        // vector<size_t> idxs;
        {
          size_t pos = sc.cur_idx + 1;
          CollectNextBranches(path, &pos, &sc.idxs);
          // fprintf(stderr, "Branches following %d:", path[sc.cur_idx]);
          for (size_t j = 0; j < sc.idxs.size(); j++) {
            //    fprintf(stderr, " %d(%u,%u,%u)", path[sc.idxs[j]], sc.idxs[j],
            //       context.dist[path[sc.idxs[j]]], context.dist[paired_branch_[path[sc.idxs[j]]]]);
            if ((Q[context_idx_].dist[path[sc.idxs[j]]] <= sc.dist)
                || (Q[context_idx_].dist[paired_branch_[path[sc.idxs[j]]]] <= sc.dist))
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
        // sc.b_idx = 0;

         // should set dist, current index -1,

      } else if (sc.idxs.size() > 0 && sc.b_idx < sc.idxs.size()) {
        // fprintf(stderr, "b_idx = %u\n", sc.b_idx);
        // fprintf(stderr, "dist_[%d](%u), sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);

        // point next index
        if((Q[context_idx_].dist[path[sc.idxs[sc.b_idx]]] > sc.dist && (Q[context_idx_].dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] > sc.dist))) {
            // fprintf(stderr, "dist_[%d](%u) > sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);
            sc.b_idx++;
            continue;
        }

        if (Q[context_idx_].dist[path[sc.idxs[sc.b_idx]]] <= sc.dist ) {
            // fprintf(stderr, "dist_[%d](%u) <= sc.dist(%u)\n", sc.idxs[sc.b_idx], dist_[path[sc.idxs[sc.b_idx]]],sc.dist);

              if(sc.seen.find(sc.b_idx)== sc.seen.end()) {
                // fprintf(stderr,"not seen %d,push \n", sc.b_idx);
                sc.seen.insert(sc.b_idx);
                  // stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist -1 ));
                  stack.push(new SubContext(sc.idxs[sc.b_idx], sc.dist -1, sc.cur_ex));
                  // sc.cur_ex.clone(stack.top().cur_ex);
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
        if(Q[context_idx_].dist[paired_branch_[path[sc.idxs[sc.b_idx]]]] <= sc.dist) {
          if (!SolveAtBranch(*sc.cur_ex, c_idx, &input)) {
            sc.b_idx++;
            continue;
          }
          RunProgram(input, &new_ex);
          bool found_new_branch = UpdateCoverage(new_ex, Q[context_idx_]);

          set<branch_id_t> new_target_branches;
          GetNewTargetBranches(new_ex, new_target_branches);
          if(!new_target_branches.empty()) {
            Context &newContext = *(Q.emplace(Q.begin() + context_idx_));
            newContext.target_branches = new_target_branches;
            Q[context_idx_ + 1].clone(newContext);
            context_idx_++;
            // std::stack<SubContext*> tmp = std::move(Q[context_idx_].stack_sub_context);
            // Context &newContext = *(Q.emplace(Q.begin() + context_idx_));
            // Q[context_idx_ + 1].clone(newContext);
            // Q[context_idx_ + 1].stack_sub_context = std::move(tmp);
            // Q[context_idx_].target_branches = new_target_branches;
            // context_idx_++;
          }

          if(found_new_branch) {
          // if(!new_target_branches.empty() && Q.size() < 5) {
            Q[context_idx_].latest_success_ex.Swap(new_ex);
            // Q[context_idx_].stack_sub_context = std::stack<SubContext>();
            return true;
          }

          if (!CheckPrediction(*sc.cur_ex, new_ex, sc.idxs[sc.b_idx])) {
            num_solve_pred_fails_ ++;
            sc.b_idx++;
            return false;
          }
             if(sc.seen2.find(sc.b_idx)== sc.seen2.end()) {
                sc.seen2.insert(sc.b_idx);
                // stack.push(new SubContext(sc.idxs[sc.b_idx], sc.dist -1, &sc.cur_ex));
                stack.push(new SubContext(sc.idxs[sc.b_idx], sc.dist-1, &new_ex));
                // stack.push(SubContext(sc.idxs[sc.b_idx], sc.dist-1, &stack.top().cur_ex));
                // new_ex.clone(stack.top().cur_ex);
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

  void CfgHeuristicCSSearch::PrintStats() {
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

  size_t CfgHeuristicCSSearch::MinCflDistance
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

  bool CfgHeuristicCSSearch::FindAlongCfg(size_t i, unsigned int dist,
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
  void CfgHeuristicCSSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
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
  void CfgHeuristicCSSearch::CollectNextBranches
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

    // Alternatively, if the sequence is followed by a return, collect the branches
    // immediately following the return.
    /*
    if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
      (*pos)++;
      CollectNextBranches(path, pos, idxs);
    }
    */
  }
  bool CfgHeuristicCSSearch::DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex) {
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
