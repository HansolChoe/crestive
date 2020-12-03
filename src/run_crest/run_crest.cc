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
#include <getopt.h>
#include <unistd.h>

#include "run_crest/concolic_search.h"

void print_help() {
  fprintf(stderr,
    "Syntax: run_crest <program> "
    "<number of iterations> "
    "-<strategy> [strategy options]\n");
    fprintf(stderr,
      "  Strategies include: "
      "dfs, cfg, md_cfg, random, md_random, uniform_random, random_input \n");
}


struct option long_options[] =
{
    {"random_input", no_argument, 0, 0},
    {"dfs", optional_argument, 0, 0},
    {"cfg", no_argument, 0, 0},
    {"md_cfg", optional_argument, 0, 0},
    {"random", no_argument, 0, 0},
    {"md_random", optional_argument, 0, 0},
    {"cfg_baseline", no_argument, 0, 0},
    {"hybrid", no_argument, 0, 0},
    {"uniform_random", optional_argument, 0, 0},
    {0,0,0,0}
};

int main(int argc, char* argv[]) {
  int opt;
  int option_index = 0;
  // Initialize the random number generator.
  struct timeval tv;
  gettimeofday(&tv, NULL);
  srand((tv.tv_sec * 1000000) + tv.tv_usec);

  const char *time_out = "1000000";

  string search_type = "";
  char* log_file_name = 0;
  char* summary_file_name = 0;

  if (argc < 4) {
    print_help();
    return 1;
  }

  while ((opt = getopt_long_only(argc,
                                 argv,
                                 "l:s:t:d:",
                                  long_options,
                                  &option_index)) != EOF) {
    switch(opt) {
      case 0: // with short options
        if(search_type!="") {
          print_help();
          return 1;
        }
        search_type = long_options[option_index].name;
        break;
      case 's': // s for summury
        if (optarg) {
            fprintf(stderr, "summary : %s\n", optarg);
            summary_file_name = optarg;
        } else {
            fprintf(stderr, "Enter summary file name\n");
            return 1;
        }
        break;
      case 'l': // l for log
        if (optarg) {
          fprintf(stderr, "log : %s\n", optarg);
          log_file_name = optarg;
        } else {
          return 1;
        }
        break;
      case 't':
        if (optarg) {
            time_out = optarg;
        } else {
            return 1;
        }
        break;
      default: // not correct inputs
        print_help();
        return 1;
    }
  }
  char *prog = argv[optind++];
  int num_iters = atoi(argv[optind++]);

  crest::Search* strategy;


  fprintf(stderr, "program : [%s]\n", prog);
  fprintf(stderr, "search_type : [%s]\n", search_type.c_str());
  fprintf(stderr, "max testcase number : [%d]\n", num_iters);
  fprintf(stderr, "timeout : %s\n", time_out);
  fprintf(stderr, "write log to '%s'\n",log_file_name);
  fprintf(stderr, "write summary to '%s'\n",summary_file_name);


  // set initial input
  struct stat buffer;
  if(stat("initial_input", &buffer) != 0) {
    fprintf(stderr, "initial_input file does not exist! exit.");
    return 1;
  }

  system("cp initial_input input");

  // remove all summaries and logs ( for conveinence...)
  system("rm summary* log*");

  if (search_type == "random") {
    strategy = new crest::RandomSearch(prog, num_iters);
  } else if (search_type == "md_random") {
    strategy = new crest::RandomMDSearch(prog, num_iters);
  } else if (search_type == "dfs") {
    if (argc == 4) {
      strategy = new crest::BoundedDepthFirstSearch(prog, num_iters, 1000000);
    } else {
      strategy = new crest::BoundedDepthFirstSearch(prog, num_iters, atoi(argv[4]));
    }
  } else if (search_type == "md_cfg") {
    strategy = new crest::CfgHeuristicMDSearch(prog, num_iters);
  } else if (search_type == "cfg") {
    strategy = new crest::CfgHeuristicSearch(prog, num_iters);
  } else if (search_type == "cfg_baseline") {
    strategy = new crest::CfgBaselineSearch(prog, num_iters);
  } else if (search_type == "random_input") {
    strategy = new crest::RandomInputSearch(prog, num_iters);
  } else if (search_type == "hybrid") {
    strategy = new crest::HybridSearch(prog, num_iters, 100);
  } else if (search_type == "uniform_random") {
    if (argc == 4) {
      strategy = new crest::UniformRandomSearch(prog, num_iters, 100000000);
    } else {
      strategy = new crest::UniformRandomSearch(prog, num_iters, atoi(argv[4]));
    }
  } else {
    fprintf(stderr, "There is no search strategy : %s\n", search_type.c_str());
    exit(1);
  }

  strategy->SetSummaryFileName(summary_file_name);
  strategy->SetLogFileName(log_file_name);
  strategy->SetTimeOut(atoi(time_out));
  strategy->Run();

  delete strategy;
  return 0;
}
