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
#include <fstream>
#include <iostream>
#include <string>
#include <sys/time.h>
#include <vector>

#include <chrono>

#include <stdlib.h>

#include "base/symbolic_interpreter.h"
#include "libcrest/crest.h"

using std::vector;
using namespace crest;

// The symbolic interpreter. */
static SymbolicInterpreter* SI;


// Have we read an input yet?  Until we have, generate only the
// minimal instrumentation necessary to track which branches were
// reached by the execution path.
static int pre_symbolic;

// Tables for converting from operators defined in libcrest/crest.h to
// those defined in base/basic_types.h.
static const int kOpTable[] =
  { // binary arithmetic
    ops::ADD, ops::SUBTRACT, ops::MULTIPLY, ops::CONCRETE, ops::CONCRETE,
    // binary bitwise operators
    ops::CONCRETE, ops::CONCRETE, ops::CONCRETE, ops::SHIFT_L, ops::CONCRETE,
    // binary logical operators
    ops::CONCRETE, ops::CONCRETE,
    // binary comparison
    ops::EQ, ops::NEQ, ops::GT, ops::LE, ops::LT, ops::GE,
    // unhandled binary operators
    ops::CONCRETE,
    // unary operators
    ops::NEGATE, ops::BITWISE_NOT, ops::LOGICAL_NOT
  };


string __crest_input_file_name;

static void __CrestAtExit();

std::chrono::time_point<std::chrono::high_resolution_clock> start;
std::chrono::time_point<std::chrono::high_resolution_clock> end;
std::chrono::duration<double> time_init;
std::chrono::duration<double> time_exit;
std::chrono::duration<double> time_atexit;


void myatexit() {
  end = std::chrono::high_resolution_clock::now();
  time_atexit = (end - start);
  // setenv("CREST_TIME_3", std::to_string(time_atexit.count()).c_str() , 1);
  fprintf(stderr, "time_atexit: %.5f\n",time_atexit.count() );

  FILE *f = fopen("time", "w");

  fprintf(f , "%lf\n", time_init.count());
  fprintf(f , "%lf\n", time_exit.count());
  fprintf(f , "%lf\n", time_atexit.count());

  fclose(f);
}
void __CrestInit() {
  start = std::chrono::high_resolution_clock::now();
  // Initialize the random number generator.
  struct timeval tv;
  gettimeofday(&tv, NULL);
  srand((tv.tv_sec * 1000000) + tv.tv_usec);

  __crest_input_file_name = std::string(getenv("CREST_INPUT_FILE_NAME")).c_str();
  if(__crest_input_file_name.empty()) {
     fprintf(stderr, "libcrest: An input file is not specified\n");
     exit(1);
  }
  fprintf(stderr, "input file : %s \n", __crest_input_file_name.c_str());
  vector<value_t> input;
  std::ifstream in(__crest_input_file_name.c_str());
  value_t val;
  while (in >> val) {
    // fprintf(stderr, "%lld ", val);
    input.push_back(val);
  }
  // fprintf(stderr, "\n", val);
  in.close();
  end = std::chrono::high_resolution_clock::now();
  time_init = (end - start);
  fprintf(stderr, "time_init: %.5f\n",time_init.count() );
  // setenv("CREST_TIME_1", std::to_string(time_init.count()).c_str() , 1);

  start = std::chrono::high_resolution_clock::now();
  SI = new SymbolicInterpreter(input);


  pre_symbolic = 1;

  atexit(myatexit);
  assert(!atexit(__CrestAtExit));
}


void __CrestAtExit() {
  end = std::chrono::high_resolution_clock::now();
  time_exit = (end - start);
  // setenv("CREST_TIME_2", std::to_string(time_exit.count()).c_str() , 1);
  // fprintf(stderr,"CREST_TIME_2 : %s\n", std::to_string(time_exit.count()).c_str());
  fprintf(stderr, "time_exit: %.5f\n",time_exit.count() );


  start = std::chrono::high_resolution_clock::now();
  const SymbolicExecution& ex = SI->execution();
  // Write the execution out to file 'szd_execution'.
  string buff;
  buff.reserve(1<<26);
  ex.Serialize(&buff);
  delete SI;
  // std::string szd_execution_name = std::string("se/ex_") + __crest_input_file_name;
  // std::ofstream out("szd_execution", std::ios::out | std::ios::binary);
  // printf("write %s\n", szd_execution_name.c_str());
  // std::ofstream out(szd_execution_name, std::ios::out | std::ios::binary);

  std::ofstream out("szd_execution", std::ios::out | std::ios::binary);
  out.write(buff.data(), buff.size());
  assert(!out.fail());
  out.close();




}


//
// Instrumentation functions.
//

void __CrestLoad(__CREST_ID id, __CREST_ADDR addr, __CREST_VALUE val) {
  if (!pre_symbolic)
    SI->Load(id, addr, val);
}


void __CrestStore(__CREST_ID id, __CREST_ADDR addr) {
  if (!pre_symbolic)
    SI->Store(id, addr);
}


void __CrestClearStack(__CREST_ID id) {
  if (!pre_symbolic)
    SI->ClearStack(id);
}


void __CrestApply1(__CREST_ID id, __CREST_OP op, __CREST_VALUE val) {
  assert((op >= __CREST_NEGATE) && (op <= __CREST_L_NOT));

  if (!pre_symbolic)
    SI->ApplyUnaryOp(id, static_cast<unary_op_t>(kOpTable[op]), val);
}


void __CrestApply2(__CREST_ID id, __CREST_OP op, __CREST_VALUE val) {
  assert((op >= __CREST_ADD) && (op <= __CREST_CONCRETE));

  if (pre_symbolic)
    return;

  if ((op >= __CREST_ADD) && (op <= __CREST_L_OR)) {
    SI->ApplyBinaryOp(id, static_cast<binary_op_t>(kOpTable[op]), val);
  } else {
    SI->ApplyCompareOp(id, static_cast<compare_op_t>(kOpTable[op]), val);
  }
}


void __CrestBranch(__CREST_ID id, __CREST_BRANCH_ID bid, __CREST_BOOL b) {
  if (pre_symbolic) {
    // Precede the branch with a fake (concrete) load.
    SI->Load(id, 0, b);
  }

  SI->Branch(id, bid, static_cast<bool>(b));
}


void __CrestCall(__CREST_ID id, __CREST_FUNCTION_ID fid) {
  SI->Call(id, fid);
}


void __CrestReturn(__CREST_ID id) {
  SI->Return(id);
}


void __CrestHandleReturn(__CREST_ID id, __CREST_VALUE val) {
  if (!pre_symbolic)
    SI->HandleReturn(id, val);
}


//
// Symbolic input functions.
//

void __CrestUChar(unsigned char* x) {
  pre_symbolic = 0;
  *x = (unsigned char)SI->NewInput(types::U_CHAR, (addr_t)x);
}

void __CrestUShort(unsigned short* x) {
  pre_symbolic = 0;
  *x = (unsigned short)SI->NewInput(types::U_SHORT, (addr_t)x);
}

void __CrestUInt(unsigned int* x) {
  pre_symbolic = 0;
  *x = (unsigned int)SI->NewInput(types::U_INT, (addr_t)x);
}

void __CrestChar(char* x) {
  pre_symbolic = 0;
  *x = (char)SI->NewInput(types::CHAR, (addr_t)x);
}

void __CrestShort(short* x) {
  pre_symbolic = 0;
  *x = (short)SI->NewInput(types::SHORT, (addr_t)x);
}

void __CrestInt(int* x) {
  pre_symbolic = 0;
  *x = (int)SI->NewInput(types::INT, (addr_t)x);
}
