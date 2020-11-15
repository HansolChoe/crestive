// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#ifndef RUN_CREST_CONCOLIC_SEARCH_H__
#define RUN_CREST_CONCOLIC_SEARCH_H__

#include <map>
#include <vector>
// #include <queue>
#include <deque>
#include <stack>
#include <ext/hash_map>
#include <ext/hash_set>
#include <time.h>
#include <chrono>

#include <functional>
#include <iostream>

/*
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
*/

#include "base/basic_types.h"
#include "base/symbolic_execution.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <dirent.h>

using std::map;
// using std::queue;
using std::deque;
using std::binary_function;
using std::vector;
using std::stack;
using std::pair;
using __gnu_cxx::hash_map;
using __gnu_cxx::hash_set;


namespace crest {

namespace {

  typedef pair<size_t,int> ScoredBranch;

  struct ScoredBranchComp
    : public binary_function<ScoredBranch, ScoredBranch, bool>
  {
    bool operator()(const ScoredBranch& a, const ScoredBranch& b) const {
      return (a.second < b.second);
    }
  };
}  // namespace



class SubContext {
public:
  //SubContext(size_t cur_idx_, size_t dist_, SymbolicExecution &ex_) {
  SubContext(size_t cur_idx_, size_t dist_) {
    b_idx = 0;
    cur_idx = cur_idx_;
    dist = dist_;
  //  fprintf(stderr, "sub context copy start\n");
  //  ex_.clone(cur_ex);
  //
  //  fprintf(stderr, "sub context copy end\n");
    // execution copy
    // cur_ex = ex_;
    // fprintf(stderr, "b cur_ex size = %u, ex size = %u\n", cur_ex.path().constraints().size(), ex_.path().constraints().size());
  }

  ~SubContext() {
    fprintf(stderr, "sub context destruct\n");
  }

  SymbolicExecution cur_ex;
  size_t cur_idx;
  size_t b_idx;
  vector<size_t> idxs;
  size_t dist;
  set<size_t> seen;
  set<size_t> seen2;
 };

 // class EXContext {
 // public:
 //   EXContext(SymbolicExecution _e, set<branch_id_t> _t) {
 //     ex = _e;
 //     target_branches = _t;
 //   }
 //   SymbolicExecution ex;
 //   set<branch_id_t> target_branches;
 // };
class Context {
public:

  Context() {
    fprintf(stderr, "Context constructor (no parama)\n");
    energy = 0;
    is_reset = false;
    cur_idx = 0;
    do_search_once_found_new_branch = false;
    is_do_search_failed = false;
    iters = 30;
    num_covered = 0;
  }

  void clone(Context &c) {
    c.energy = 0;
    c.is_reset = false;
    c.cur_idx = 0;
    c.iters = 30;
    c.do_search_once_found_new_branch = false;
    c.is_do_search_failed = false;
    fprintf(stderr, "Context c - clone to cur_ex\n");
    cur_ex.clone(c.cur_ex);

    // vector<bool> covered; - not need to copy here
    // c.covered.resize(covered.size(), false);
    // assign dist here
    c.dist.resize(dist.size(), 0);
    // vector<size_t> dist;
    // unsigned int num_covered;
    num_covered = 0;

    // SymbolicExecution cur_ex;

    // set<branch_id_t> new_branches; - do nothing
    // set<branch_id_t> target_branches; - do nothing
    // set<branch_id_t> searching_branches; - do nothing
    // vector<ScoredBranch> scoredBranches; - do nothing
    // stack<SubContext> stack_sub_context; - do nothing
    // SymbolicExecution latest_success_ex; - do nothing
  }

  bool is_reset;
  size_t energy;
  size_t cur_idx;
  int iters;
  bool do_search_once_found_new_branch;
  bool is_do_search_failed;
  vector<bool> covered;
  vector<size_t> dist;
  unsigned int num_covered;
  set<branch_id_t> new_branches;

  set<branch_id_t> target_branches;
  set<branch_id_t> searching_branches;
  vector<ScoredBranch> scoredBranches;
  stack<SubContext> stack_sub_context;

  SymbolicExecution cur_ex;
  SymbolicExecution latest_success_ex;

  ~Context()  {
    fprintf(stderr, "destruct Context\n");
  }

  // Context& operator=(Context &&other) noexcept {
  //   fprintf(stderr, "move~\n");
  //   if (this != &other) {
  //     fprintf(stderr, "here\n");
  //   }
  //   return *this;
  // }


  // void PrintPathConstraint(const SymbolicPath &sym_path) {
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

  // Context(SymbolicExecution &_e, set<branch_id_t> _target_branches) {
  //   fprintf(stderr, " Context constructor start\n");
  //   cur_ex = _e;
  //   fprintf(stderr, " Context constructor end\n");
  //
  //
  //   // PrintPathConstraint(cur_ex.path());
  //   target_branches = _target_branches;
  //   is_reset = false;
  //   cur_idx = 0;
  //   is_do_search_failed = false;
  //   do_search_once_found_new_branch = false;
  //   energy = 0;
  //   iters = 30;
  //   num_covered = 0;
  //   // fprintf(stderr, " Context constructor end\n");
  // }
  //
  // Context& operator=(const Context &m) {
  //   fprintf(stderr, "se operator=\n");
  //   if ( this != &m) {
  //     // cur_ex = std::move(m.cur_ex);
  //     cur_ex = std::move(m.cur_ex);
  //     latest_success_ex = std::move(m.latest_success_ex);
  //
  //     stack_sub_context = std::move(m.stack_sub_context);
  //
  //     covered = std::move(m.covered);
  //     dist = std::move(m.dist);
  //     // fprintf(stderr, "dist size : %zu %n", dist.size());
  //     new_branches = std::move(m.new_branches);
  //     target_branches = std::move(m.target_branches);
  //     target_branches = std::move(m.searching_branches);
  //     scoredBranches = std::move(m.scoredBranches);
  //
  //     num_covered = m.num_covered;
  //     iters = m.iters;
  //     energy = m.energy;
  //     cur_idx = m.cur_idx;
  //     is_do_search_failed = m.is_do_search_failed;
  //
  //
  //     // context_idx_ = m.context_idx_;
  //     fprintf(stderr, "m.iters = %u\n", m.iters);
  //     fprintf(stderr, "iters = %u\n", iters);
  //     // m.iters = 0;
  //     // m.num_covered = 0;
  //     // m.energy = 0;
  //     // m.cur_idx = 0;
  //   }
  //   return *this;
  // }

  //
  //
  // Context(Context &&m)  {
  //
  //   fprintf(stderr, "move Context\n");
  //   cur_ex = std::move(m.cur_ex);
  //   latest_success_ex = std::move(m.latest_success_ex);
  //
  //   stack_sub_context = std::move(m.stack_sub_context);
  //
  //   covered = std::move(m.covered);
  //   dist = std::move(m.dist);
  //   // fprintf(stderr, "dist size : %zu %n", dist.size());
  //   new_branches = std::move(m.new_branches);
  //   target_branches = std::move(m.target_branches);
  //   target_branches = std::move(m.searching_branches);
  //   scoredBranches = std::move(m.scoredBranches);
  //
  //   num_covered = m.num_covered;
  //   iters = m.iters;
  //   energy = m.energy;
  //   cur_idx = m.cur_idx;
  //   is_do_search_failed = m.is_do_search_failed;
  //
  //
  //   // context_idx_ = m.context_idx_;
  //   fprintf(stderr, "m.iters = %u\n", m.iters);
  //   fprintf(stderr, "iters = %u\n", iters);
  //   m.iters = 0;
  //   m.num_covered = 0;
  //   m.energy = 0;
  //   m.cur_idx = 0;
  // }
  //



  //
  // Context(const Context &m) {
  //   fprintf(stderr, "context copy\n");
  //   cur_ex = m.cur_ex;
  //   latest_success_ex = m.latest_success_ex;
  //
  //   stack_sub_context = m.stack_sub_context;
  //
  //   covered = m.covered;
  //   dist = m.dist;
  //   fprintf(stderr, "dist size : %zu , %zu\n", dist.size(), m.dist.size());
  //   new_branches = m.new_branches;
  //   target_branches = m.target_branches;
  //   searching_branches = m.searching_branches;
  //   scoredBranches = m.scoredBranches;
  //
  //   num_covered = m.num_covered;
  //   iters = m.iters;
  //   energy = m.energy;
  //   cur_idx = m.cur_idx;
  //   is_do_search_failed = m.is_do_search_failed;
  //   fprintf(stderr, "context copy finished\n");
  //   fprintf(stderr, "scored_branches size : %zu , %zu\n", scoredBranches.size(), m.scoredBranches.size());
  //   // fprintf(stderr, "scored_branches size : %u\n");
  // }

 };

class Search {
 public:
  Search(const string& program, int max_iterations);
  virtual ~Search();

  virtual void Run() = 0;

  void SetIsSaveTestcasesOption(bool is_save_testcases_option) {
    is_save_testcases_option_ = is_save_testcases_option;
  }
    void RunDirectory(const char *input_directory_name);
    void PrintPathConstraint(const SymbolicPath &symbolic_path);
 protected:
  double t1;
  double t2;
  double t3;

  size_t error_count;
  vector<branch_id_t> branches_;
  vector<branch_id_t> paired_branch_;
  vector<function_id_t> branch_function_;
  vector<bool> covered_;
  vector<bool> total_covered_;
  branch_id_t max_branch_;
  unsigned int num_covered_;
  unsigned int total_num_covered_;
  bool is_save_testcases_option_;

  vector<bool> reached_;
  vector<unsigned int> branch_count_;
  function_id_t max_function_;
  unsigned int reachable_functions_;
  unsigned int reachable_branches_;

  time_t start_time_;
  time_t summary_time_;
  time_t coverage_log_time_;

  std::chrono::high_resolution_clock::time_point begin_total_;
  std::chrono::high_resolution_clock::time_point end_total_;
  std::chrono::duration<double> elapsed_time_total_;
  std::chrono::duration<double> elapsed_time_searching_1_;
  std::chrono::duration<double> elapsed_time_searching_2_;
  std::chrono::duration<double> elapsed_time_searching_3_;
  std::chrono::duration<double> elapsed_time_searching_4_;
  std::chrono::duration<double> elapsed_time_searching_5_;
  std::chrono::duration<double> elapsed_time_searching_6_;
  std::chrono::duration<double> elapsed_time_searching_7_;
  std::chrono::duration<double> elapsed_time_searching_8_;
  std::chrono::duration<double> elapsed_time_searching_9_;
  std::chrono::duration<double> elapsed_time_searching_10_;
  std::chrono::duration<double> elapsed_time_searching_11_;
  std::chrono::duration<double> elapsed_time_solving_;
  std::chrono::duration<double> elapsed_time_program_;
  std::chrono::duration<double> elapsed_time_copy_;
  std::chrono::duration<double> elapsed_time_update_;
  std::chrono::duration<double> elapsed_time_szd_read_;
  typedef vector<branch_id_t>::const_iterator BranchIt;

  bool SolveAtBranch(const SymbolicExecution& ex,
		     size_t branch_idx,
		     vector<value_t>* input);

  bool CheckPrediction(const SymbolicExecution& old_ex,
		       const SymbolicExecution& new_ex,
		       size_t branch_idx);

  void RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex);
  bool UpdateCoverage(const SymbolicExecution& ex);
  bool UpdateCoverage(const SymbolicExecution& ex,
		      set<branch_id_t>* new_branches);

  void RandomInput(const map<var_t,type_t>& vars, vector<value_t>* input);


  int input_file_idx_;
  int rotation_count_;

  vector<string> input_file_names_;
  void read_directory(const std::string& name, vector<string>& v);
  void UpdateInputFileIdx();


  void WriteInputToFileOrDie(const string& file, const vector<value_t>& input);
  int num_iters_;
  void WriteCoverageToFileOrDie(const string& file);
  void LaunchProgram(const vector<value_t>& inputs);
  const int max_iters_;
  const string program_;
  int num_prediction_fail_;
 private:
  int time_out_;
SymbolicExecution run_ex;
  /*
  struct sockaddr_un sock_;
  int sockd_;
  */

  // void WriteCoverageToFileOrDie(const string& file);
  // void LaunchProgram(const vector<value_t>& inputs);
};

class EXContext {
public:
  EXContext(SymbolicExecution _e, set<branch_id_t> _t) {
    ex = _e;
    target_branches = _t;
  }
  SymbolicExecution ex;
  set<branch_id_t> target_branches;
};

// class CSSearch : public Search {
// public:
//     CSSearch(const string& program, int max_iterations);
//     virtual ~CSSearch();
//
//   protected:
//     // virtual size_t AssignEnergy(EXContext &c);
//
//
// };

class RandomCSSearch : public Search {
 public:
   RandomCSSearch(const string& program, int max_iterations)
     : Search(program, max_iterations) { }

  ~RandomCSSearch() {}
  // virtual ~RandomCSSearch();
  virtual void Run();
  // size_t AssignEnergy(EXContext &c);
  size_t AssignEnergy(EXContext c);
  // set<branch_id_t> uncovered_branches_;
protected:
  map<size_t, size_t> pf_count_;
  set<branch_id_t> covered_branches_;
  set<branch_id_t> reachable_branches_set_;
  bool UpdateCoverage(const SymbolicExecution& ex);
  bool UpdateCoverage(const SymbolicExecution& ex, set<branch_id_t>* new_branches);
 private:
  deque<EXContext> Q;
  // bool SolveRandomBranch(vector<value_t>* next_input, size_t* idx);
  bool SolveRandomBranch(SymbolicExecution &ex, vector<value_t>* next_input, size_t* idx);
};




class BoundedDepthFirstSearch : public Search {
 public:
  explicit BoundedDepthFirstSearch(const string& program,
				   int max_iterations,
				   int max_depth);
  virtual ~BoundedDepthFirstSearch();

  virtual void Run();

 private:
  int max_depth_;

  void DFS(size_t pos, int depth, SymbolicExecution& prev_ex);
};


class RandomInputSearch : public Search {
 public:
  RandomInputSearch(const string& program, int max_iterations);
  virtual ~RandomInputSearch();

  virtual void Run();

 private:
  SymbolicExecution ex_;
};


class RandomESSearch : public Search {
 public:
  RandomESSearch(const string& program, int max_iterations);
  virtual ~RandomESSearch();

  virtual void Run();

 private:
  //SymbolicExecution ex_;
  vector<SymbolicExecution> v_ex_;

  void SolveUncoveredBranches(size_t i, int depth,
                              const SymbolicExecution& prev_ex);

  bool SolveRandomBranch(vector<value_t>* next_input, size_t* idx);
};





class UniformRandomSearch : public Search {
 public:
  UniformRandomSearch(const string& program, int max_iterations, size_t max_depth);
  virtual ~UniformRandomSearch();

  virtual void Run();

 private:
  // SymbolicExecution prev_ex_;
  // SymbolicExecution cur_ex_;

  size_t max_depth_;

  // void DoUniformRandomPath();
};


// Search looks like:
//  (1) Do random inputs for some amount of time.
//  (2) Do a local search repeatedly in some area, then continue the random search.
class HybridSearch : public Search {
 public:
  HybridSearch(const string& program, int max_iterations, int step_size);
  virtual ~HybridSearch();

  virtual void Run();

 private:
  void RandomLocalSearch(SymbolicExecution* ex, size_t start, size_t end);
  bool RandomStep(SymbolicExecution* ex, size_t start, size_t end);

  int step_size_;
};


/*
class LeastRunSearch : public Search {
 public:
  LeastRunSearch(const string& program, int max_iterations);
  virtual ~LeastRunSearch();

  virtual void Run();

 private:
  vector<size_t> run_count_;

  bool DoSearch(int depth, int iters, int pos, const SymbolicExecution& prev_ex);
};
*/


class CfgBaselineSearch : public Search {
 public:
  CfgBaselineSearch(const string& program, int max_iterations);
  virtual ~CfgBaselineSearch();

  virtual void Run();

 private:
  SymbolicExecution success_ex_;
  bool DoSearch(int depth, int iters, int pos, const SymbolicExecution& prev_ex);
};



 // class EXContext {
 // public:
 //   EXContext(SymbolicExecution _e, set<branch_id_t> _t) {
 //     ex = _e;
 //     target_branches = _t;
 //     energy = 0;
 //   }
 //   SymbolicExecution ex;
 //   set<branch_id_t> target_branches;
 // };


class CfgHeuristicESSearch : public Search {
 public:
  CfgHeuristicESSearch(const string& program, int max_iterations);
  virtual ~CfgHeuristicESSearch();

  virtual void Run();
protected:
  bool UpdateCoverage(const SymbolicExecution& ex, Context &context);
  bool UpdateCoverage(const SymbolicExecution& ex,
		      set<branch_id_t>* new_branches, Context &context);


 private:
  // vector<SymbolicExecution> v_ex_;
  void GetSearchingBranches(branch_id_t b, vector<bool> &covered, vector<size_t>& dist, size_t depth, set<branch_id_t> &t);
  vector<Context> v_context_;
  set<branch_id_t> all_new_branches;

  typedef vector<branch_id_t> nbhr_list_t;
  vector<nbhr_list_t> cfg_;
  vector<nbhr_list_t> cfg_rev_;
  vector<size_t> dist_notusing;

  static const size_t kInfiniteDistance = 10000;

  int iters_left_;

  SymbolicExecution success_ex_;

  // Stats.
  unsigned num_inner_solves_;
  unsigned num_inner_successes_pred_fail_;
  unsigned num_inner_lucky_successes_;
  unsigned num_inner_zero_successes_;
  unsigned num_inner_nonzero_successes_;
  unsigned num_inner_recursive_successes_;
  unsigned num_inner_unsats_;
  unsigned num_inner_pred_fails_;

  unsigned num_top_solves_;
  unsigned num_top_solve_successes_;

  unsigned num_solves_;
  unsigned num_solve_successes_;
  unsigned num_solve_sat_attempts_;
  unsigned num_solve_unsats_;
  unsigned num_solve_recurses_;
  unsigned num_solve_pred_fails_;
  unsigned num_solve_all_concrete_;
  unsigned num_solve_no_paths_;

  // void UpdateBranchDistances();
  // void UpdateBranchDist ances(vector<size_t>& dist);
  void UpdateBranchDistances(vector<bool>& covered, vector<long unsigned int>& dist);
  void PrintStats();
  // bool DoSearch(int depth, int iters, int pos, int maxDist, const SymbolicExecution& prev_ex);
  // bool DoSearchOnce(int depth, int iters, int pos, int maxDist, const SymbolicExecution& prev_ex);
  bool DoSearchOnce(Context& context);
  bool SolveOnePathAlongCfg(Context& context);

  bool DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex);
  void SkipUntilReturn(const vector<branch_id_t> path, size_t* pos);

  bool FindAlongCfg(size_t i, unsigned int dist,
		    const SymbolicExecution& ex,
		    const set<branch_id_t>& bs);

  // bool SolveAlongCfg(size_t i, unsigned int max_dist,
	// 	     const SymbolicExecution& prev_ex);

  void CollectNextBranches(const vector<branch_id_t>& path,
			   size_t* pos, vector<size_t>* idxs);

  size_t MinCflDistance(size_t i,
			const SymbolicExecution& ex,
			const set<branch_id_t>& bs);
};

class RandomSearch : public Search {
 public:
  RandomSearch(const string& program, int max_iterations);
  virtual ~RandomSearch();

  virtual void Run();

 private:
  SymbolicExecution ex_;

  void SolveUncoveredBranches(size_t i, int depth,
                              const SymbolicExecution& prev_ex);

  bool SolveRandomBranch(vector<value_t>* next_input, size_t* idx);
};

class CfgHeuristicSearch : public Search {
 public:
  CfgHeuristicSearch(const string& program, int max_iterations);
  virtual ~CfgHeuristicSearch();

  virtual void Run();

 private:
  // void GetSearchingBranches(branch_id_t b, vector<bool> &covered, size_t dist, set<branch_id_t> &t);
  typedef vector<branch_id_t> nbhr_list_t;
  vector<nbhr_list_t> cfg_;
  vector<nbhr_list_t> cfg_rev_;
  vector<size_t> dist_;

  static const size_t kInfiniteDistance = 10000;

  int iters_left_;

  SymbolicExecution success_ex_;

  // Stats.
  unsigned num_inner_solves_;
  unsigned num_inner_successes_pred_fail_;
  unsigned num_inner_lucky_successes_;
  unsigned num_inner_zero_successes_;
  unsigned num_inner_nonzero_successes_;
  unsigned num_inner_recursive_successes_;
  unsigned num_inner_unsats_;
  unsigned num_inner_pred_fails_;

  unsigned num_top_solves_;
  unsigned num_top_solve_successes_;

  unsigned num_solves_;
  unsigned num_solve_successes_;
  unsigned num_solve_sat_attempts_;
  unsigned num_solve_unsats_;
  unsigned num_solve_recurses_;
  unsigned num_solve_pred_fails_;
  unsigned num_solve_all_concrete_;
  unsigned num_solve_no_paths_;

  void UpdateBranchDistances();
  void PrintStats();
  bool DoSearch(int depth, int iters, int pos, int maxDist, const SymbolicExecution& prev_ex);
  bool DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex);
  void SkipUntilReturn(const vector<branch_id_t> path, size_t* pos);

  bool FindAlongCfg(size_t i, unsigned int dist,
		    const SymbolicExecution& ex,
		    const set<branch_id_t>& bs);

  bool SolveAlongCfg(size_t i, unsigned int max_dist,
		     const SymbolicExecution& prev_ex);

  void CollectNextBranches(const vector<branch_id_t>& path,
			   size_t* pos, vector<size_t>* idxs);

  size_t MinCflDistance(size_t i,
			const SymbolicExecution& ex,
			const set<branch_id_t>& bs);
};



class CfgHeuristicCSSearch : public Search {
 public:
  CfgHeuristicCSSearch(const string& program, int max_iterations);
  virtual ~CfgHeuristicCSSearch();
  virtual void Run();
protected:

  set<branch_id_t> covered_branches_;
  bool UpdateCoverage(const SymbolicExecution& ex, set<branch_id_t> *new_branches, Context &context);
  bool UpdateCoverage(const SymbolicExecution& ex, Context &context);
  size_t AssignEnergy(Context &c);
  void UpdateCurContext();
  // void UpdateCurContext();
  // void GetNewTargetBranches(SymbolicExecution &next_ex,set<branch_id_t> &u);
  void GetNewTargetBranches(SymbolicExecution &next_ex,set<branch_id_t> &u);
  void GetSearchingBranches(branch_id_t b, vector<bool> &covered, vector<size_t>& dist, size_t depth, set<branch_id_t> &t);

 private:
   deque<Context> Q;
   size_t context_idx_;
  // vector<Context> v_context_;
  // set<branch_id_t> all_new_branches;
  // set<branch_id_t> all_target_branches;

  // Context cur_context_;
  typedef vector<branch_id_t> nbhr_list_t;
  vector<nbhr_list_t> cfg_;
  vector<nbhr_list_t> cfg_rev_;
  vector<size_t> dist_notusing;
  map<size_t, size_t> pf_count_;
  static const size_t kInfiniteDistance = 10000;

  int iters_left_;

  SymbolicExecution success_ex_;

  // Stats.
  unsigned num_inner_solves_;
  unsigned num_inner_successes_pred_fail_;
  unsigned num_inner_lucky_successes_;
  unsigned num_inner_zero_successes_;
  unsigned num_inner_nonzero_successes_;
  unsigned num_inner_recursive_successes_;
  unsigned num_inner_unsats_;
  unsigned num_inner_pred_fails_;

  unsigned num_top_solves_;
  unsigned num_top_solve_successes_;

  unsigned num_solves_;
  unsigned num_solve_successes_;
  unsigned num_solve_sat_attempts_;
  unsigned num_solve_unsats_;
  unsigned num_solve_recurses_;
  unsigned num_solve_pred_fails_;
  unsigned num_solve_all_concrete_;
  unsigned num_solve_no_paths_;

  // void UpdateBranchDistances();
  // void UpdateBranchDist ances(vector<size_t>& dist);
  void UpdateBranchDistances(vector<bool>& covered, vector<long unsigned int>& dist);
  void PrintStats();
  // bool DoSearch(int depth, int iters, int pos, int maxDist, const SymbolicExecution& prev_ex);
  // bool DoSearchOnce(int depth, int iters, int pos, int maxDist, const SymbolicExecution& prev_ex);
  // bool DoSearchOnce(Context& context);
  // bool SolveOnePathAlongCfg(Context& context);
  bool DoSearchOnce();
  bool SolveOnePathAlongCfg();
  bool DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex);
  void SkipUntilReturn(const vector<branch_id_t> path, size_t* pos);

  bool FindAlongCfg(size_t i, unsigned int dist,
		    const SymbolicExecution& ex,
		    const set<branch_id_t>& bs);

  // bool SolveAlongCfg(size_t i, unsigned int max_dist,
	// 	     const SymbolicExecution& prev_ex);

  void CollectNextBranches(const vector<branch_id_t>& path,
			   size_t* pos, vector<size_t>* idxs);

  size_t MinCflDistance(size_t i,
			const SymbolicExecution& ex,
			const set<branch_id_t>& bs);
};

class Runner : public Search {
 public:
  Runner(const string& program, int max_iterations);
  virtual ~Runner();
  virtual void Run();
};

}  // namespace crest
#endif  // RUN_CREST_CONCOLIC_SEARCH_H__
