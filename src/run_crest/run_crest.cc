// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <assert.h>
#include <stdio.h>
#include <sys/time.h>

#include "run_crest/concolic_search.h"

int main(int argc, char* argv[]) {
  if (argc < 3) {
    fprintf(stderr,
            "Syntax: run_crest <program> "
            "<number of iterations> "
            "-<strategy> [strategy options]\n");
    fprintf(stderr,
            "  Strategies include: "
            "dfs, cfg, random, uniform_random, random_input \n");
    return 1;
  }
  char *time_out = "10000000";

  string prog = argv[1];
  int num_iters = atoi(argv[2]);
  string search_type = argv[3];
  int execution_time = 600;
  if(argc==5) {
   execution_time = atoi(argv[4]);
  }
  string command = argv[2];

  // Initialize the random number generator.
  struct timeval tv;
  gettimeofday(&tv, NULL);
  srand((tv.tv_sec * 1000000) + tv.tv_usec);
  // srand(20201109);
string input_directory_name ="";
  crest::Search* strategy;
  system("rm -r inputs");
  system("cp -r seeds inputs");
  system("cp seeds/input1 input");
  system("rm -r se");
  system("mkdir se");
  system("rm summary* log*");
  system("rm -r coverages");
  system("mkdir coverages");
  // system("rm si_time");


  bool is_run_directory_option = false;

  if (search_type == "-random") {
    strategy = new crest::RandomSearch(prog, num_iters);
  } else if (search_type == "-es_random") {
    strategy = new crest::RandomESSearch(prog, num_iters);
  } else if (search_type == "-cs_random") {
    strategy = new crest::RandomCSSearch(prog, num_iters);
  } else if (search_type == "-cs_random2") {
    strategy = new crest::RandomCSSearch(prog, num_iters);
  } else if (search_type == "-random_input") {
    strategy = new crest::RandomInputSearch(prog, num_iters);
  } else if (search_type == "-dfs") {
    if (argc == 4) {
      strategy = new crest::BoundedDepthFirstSearch(prog, num_iters, 1000000);
    } else {
      strategy = new crest::BoundedDepthFirstSearch(prog, num_iters, atoi(argv[4]));
    }
  } else if (search_type == "-cs_cfg") {
    strategy = new crest::CfgHeuristicCSSearch(prog, num_iters);
  } else if (search_type == "-cfg") {
    strategy = new crest::CfgHeuristicSearch(prog, num_iters);
  } else if (search_type == "-cfg_baseline") {
    strategy = new crest::CfgBaselineSearch(prog, num_iters);
  } else if (search_type == "-hybrid") {
    strategy = new crest::HybridSearch(prog, num_iters, 100);
  } else if (search_type == "-uniform_random") {
    if (argc == 4) {
      strategy = new crest::UniformRandomSearch(prog, num_iters, 100000000);
    } else {
      strategy = new crest::UniformRandomSearch(prog, num_iters, atoi(argv[4]));
    }
  } else if (command == "-r") {
    is_run_directory_option = true;
    strategy = new crest::Runner(prog, num_iters);
    fprintf(stderr, "Unknown search strategy: %s\n", search_type.c_str());
    input_directory_name = argv[3];
  } else {
    fprintf(stderr, "Unknown search strategy: %s\n", search_type.c_str());
    return 1;
  }
  strategy->SetTimeOut(execution_time);

  if (is_run_directory_option) {
    strategy -> RunDirectory(input_directory_name.c_str());
  } else {
    strategy->SetIsSaveTestcasesOption(false);
    // system("touch testcases/input1");

    if( search_type == "-cs_random2") {
      strategy-> Run2();
    } else {
      strategy->Run();
    }
  }

  delete strategy;
  return 0;
}
