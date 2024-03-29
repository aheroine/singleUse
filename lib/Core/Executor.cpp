//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Common.h"
#include "Executor.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExternalDispatcher.h"
#include "ImpliedValue.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"
#include "ExecutorTimerInfo.h"

#include "../Solver/SolverStats.h"

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/CommandLine.h"
#include "klee/Common.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/FloatEvaluation.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/System/MemoryUsage.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#else
#include "llvm/Attributes.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#include "llvm/TypeBuilder.h"
#endif
#endif
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/raw_ostream.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include <cassert>
#include <algorithm>
#include <iomanip>
#include <iosfwd>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

#include <sys/mman.h>

#include <errno.h>
#include <cxxabi.h>

using namespace llvm;
using namespace klee;


#ifdef SUPPORT_METASMT

#include <metaSMT/frontend/Array.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/backend/Boolector.hpp>
#include <metaSMT/backend/MiniSAT.hpp>
#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/support/run_algorithm.hpp>
#include <metaSMT/API/Stack.hpp>
#include <metaSMT/API/Group.hpp>

#define Expr VCExpr
#define Type VCType
#define STP STP_Backend
#include <metaSMT/backend/STP.hpp>
#undef Expr
#undef Type
#undef STP

using namespace metaSMT;
using namespace metaSMT::solver;

#endif /* SUPPORT_METASMT */
//bupt use
bool BuptShadow;
std::map<std::string, int> concernFunction;
std::map<std::string, int> dataDivInCF;
std::vector<char*> buf_for_argv;
bool is_print;
std::string printfunc;


#include "llvm/Support/CFG.h"

unsigned debug=0;
unsigned debug_internal=0;
unsigned debug_call=0;
unsigned debug_func=0;
unsigned debug_constraint=0;
unsigned debug_mem=0;
unsigned debug_addconst=0;
unsigned debug_pointer=0;
unsigned debug_cef=0;
#define DEBUG_KCALL 0
namespace {
  cl::opt<bool>
  DumpStatesOnHalt("dump-states-on-halt",
                   cl::init(true),
           cl::desc("Dump test cases for all active states on exit (default=on)"));

  cl::opt<bool>
  RandomizeFork("randomize-fork",
                cl::init(false),
        cl::desc("Randomly swap the true and false states on a fork (default=off)"));

  cl::opt<bool>
  AllowExternalSymCalls("allow-external-sym-calls",
                        cl::init(false),
            cl::desc("Allow calls with symbolic arguments to external functions.  This concretizes the symbolic arguments.  (default=off)"));

  cl::opt<bool>
  DebugPrintInstructions("debug-print-instructions",
                         cl::desc("Print instructions during execution."));

  cl::opt<bool>
  DebugCheckForImpliedValues("debug-check-for-implied-values");


  cl::opt<bool>
  SimplifySymIndices("simplify-sym-indices",
                     cl::init(false));

  cl::opt<bool>
  EqualitySubstitution("equality-substitution",
                     cl::init(true),
                     cl::desc("Simplify equality expressions before querying the solver (default=on)."));

  cl::opt<unsigned>
  MaxSymArraySize("max-sym-array-size",
                  cl::init(0));

  cl::opt<bool>
  SuppressExternalWarnings("suppress-external-warnings");

  cl::opt<bool>
  AllExternalWarnings("all-external-warnings");

  cl::opt<bool>
  OnlyOutputStatesCoveringNew("only-output-states-covering-new",
                              cl::init(false),
                  cl::desc("Only output test cases covering new code."));

  cl::opt<bool>
  EmitAllErrors("emit-all-errors",
                cl::init(false),
                cl::desc("Generate tests cases for all errors "
                         "(default=off, i.e. one per (error,instruction) pair)"));

  cl::opt<bool>
  NoExternals("no-externals",
           cl::desc("Do not allow external function calls (default=off)"));

  cl::opt<bool>
  AlwaysOutputSeeds("always-output-seeds",
            cl::init(true));

  cl::opt<bool>
  OnlyReplaySeeds("only-replay-seeds",
                  cl::desc("Discard states that do not have a seed."));

  cl::opt<bool>
  OnlySeed("only-seed",
           cl::desc("Stop execution after seeding is done without doing regular search."));

  cl::opt<bool>
  AllowSeedExtension("allow-seed-extension",
                     cl::desc("Allow extra (unbound) values to become symbolic during seeding."));

  cl::opt<bool>
  ZeroSeedExtension("zero-seed-extension");

  cl::opt<bool>
  AllowSeedTruncation("allow-seed-truncation",
                      cl::desc("Allow smaller buffers than in seeds."));

  cl::opt<bool>
  NamedSeedMatching("named-seed-matching",
                    cl::desc("Use names to match symbolic objects to inputs."));

  cl::opt<double>
  MaxStaticForkPct("max-static-fork-pct", cl::init(1.));
  cl::opt<double>
  MaxStaticSolvePct("max-static-solve-pct", cl::init(1.));
  cl::opt<double>
  MaxStaticCPForkPct("max-static-cpfork-pct", cl::init(1.));
  cl::opt<double>
  MaxStaticCPSolvePct("max-static-cpsolve-pct", cl::init(1.));

  cl::opt<double>
  MaxInstructionTime("max-instruction-time",
                     cl::desc("Only allow a single instruction to take this much time (default=0s (off)). Enables --use-forked-solver"),
                     cl::init(0));

  cl::opt<double>
  SeedTime("seed-time",
           cl::desc("Amount of time to dedicate to seeds, before normal search (default=0 (off))"),
           cl::init(0));

  cl::opt<unsigned int>
  StopAfterNInstructions("stop-after-n-instructions",
                         cl::desc("Stop execution after specified number of instructions (default=0 (off))"),
                         cl::init(0));

  cl::opt<unsigned>
  MaxForks("max-forks",
           cl::desc("Only fork this many times (default=-1 (off))"),
           cl::init(~0u));

  cl::opt<unsigned>
  MaxDepth("max-depth",
           cl::desc("Only allow this many symbolic branches (default=0 (off))"),
           cl::init(0));

  cl::opt<unsigned>
  MaxMemory("max-memory",
            cl::desc("Refuse to fork when above this amount of memory (in MB, default=2000)"),
            cl::init(2000));

  cl::opt<bool>
  MaxMemoryInhibit("max-memory-inhibit",
            cl::desc("Inhibit forking at memory cap (vs. random terminate) (default=on)"),
            cl::init(true));
    //bupt use
  static cl::opt<bool,true>
    _BuptShadow("use",
                cl::location(BuptShadow),
                cl::init(false));
}


namespace klee {
  RNG theRNG;
}


Executor::Executor(const InterpreterOptions &opts,
                   InterpreterHandler *ih)
  : Interpreter(opts),
    kmodule(0),
    interpreterHandler(ih),
    searcher(0),
    externalDispatcher(new ExternalDispatcher()),
    statsTracker(0),
    pathWriter(0),
    symPathWriter(0),
    specialFunctionHandler(0),
    processTree(0),
    replayOut(0),
    replayPath(0),
    usingSeeds(0),
    atMemoryLimit(false),
    inhibitForking(false),
    haltExecution(false),
    ivcEnabled(false),
//bupt use
    coreSolverTimeout(MaxCoreSolverTime != 0 && MaxInstructionTime != 0
      ? std::min(MaxCoreSolverTime,MaxInstructionTime)
      : std::max(MaxCoreSolverTime,MaxInstructionTime)) {

  if (coreSolverTimeout) UseForkedCoreSolver = true;

  Solver *coreSolver = NULL;

#ifdef SUPPORT_METASMT
  if (UseMetaSMT != METASMT_BACKEND_NONE) {

    std::string backend;

    switch (UseMetaSMT) {
          case METASMT_BACKEND_STP:
              backend = "STP";
              coreSolver = new MetaSMTSolver< DirectSolver_Context < STP_Backend > >(UseForkedCoreSolver, CoreSolverOptimizeDivides);
              break;
          case METASMT_BACKEND_Z3:
              backend = "Z3";
              coreSolver = new MetaSMTSolver< DirectSolver_Context < Z3_Backend > >(UseForkedCoreSolver, CoreSolverOptimizeDivides);
              break;
          case METASMT_BACKEND_BOOLECTOR:
              backend = "Boolector";
              coreSolver = new MetaSMTSolver< DirectSolver_Context < Boolector > >(UseForkedCoreSolver, CoreSolverOptimizeDivides);
              break;
          default:
              assert(false);
              break;
    };
    llvm::errs() << "Starting MetaSMTSolver(" << backend << ") ...\n";
  }
  else {
    coreSolver = new STPSolver(UseForkedCoreSolver, CoreSolverOptimizeDivides);
  }
#else
  coreSolver = new STPSolver(UseForkedCoreSolver, CoreSolverOptimizeDivides);
#endif /* SUPPORT_METASMT */


  Solver *solver =
    constructSolverChain(coreSolver,
                         interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
                         interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
                         interpreterHandler->getOutputFilename(ALL_QUERIES_PC_FILE_NAME),
                         interpreterHandler->getOutputFilename(SOLVER_QUERIES_PC_FILE_NAME));

  if(!BuptShadow){
    this->solver = new TimingSolver(solver, EqualitySubstitution);
  } else {
    this->solver = new TimingSolver(solver, EqualitySubstitution, &seedMap);
  }

  memory = new MemoryManager();
}


const Module *Executor::setModule(llvm::Module *module,
                                  const ModuleOptions &opts) {
  assert(!kmodule && module && "can only register one module"); // XXX gross

  kmodule = new KModule(module);

  // Initialize the context.
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  TargetData *TD = kmodule->targetData;
#else
  DataLayout *TD = kmodule->targetData;
#endif
  Context::initialize(TD->isLittleEndian(),
                      (Expr::Width) TD->getPointerSizeInBits());

  specialFunctionHandler = new SpecialFunctionHandler(*this);

  specialFunctionHandler->prepare();
  kmodule->prepare(opts, interpreterHandler);
  specialFunctionHandler->bind();

  if (StatsTracker::useStatistics()) {
    statsTracker =
      new StatsTracker(*this,
                       interpreterHandler->getOutputFilename("assembly.ll"),
                       userSearcherRequiresMD2U());
  }

  return module;
}

Executor::~Executor() {
  delete memory;
  delete externalDispatcher;
  if (processTree)
    delete processTree;
  if (specialFunctionHandler)
    delete specialFunctionHandler;
  if (statsTracker)
    delete statsTracker;
  delete solver;
  delete kmodule;
  while(!timers.empty()) {
    delete timers.back();
    timers.pop_back();
  }
}

/***/

void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
                                      const Constant *c,
                                      unsigned offset) {
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
  TargetData *targetData = kmodule->targetData;
#else
  DataLayout *targetData = kmodule->targetData;
#endif
  if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cp->getType()->getElementType());
    for (unsigned i=0, e=cp->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cp->getOperand(i),
                 offset + i*elementSize);
  } else if (isa<ConstantAggregateZero>(c)) {
    unsigned i, size = targetData->getTypeStoreSize(c->getType());
    for (i=0; i<size; i++)
      os->write8(offset+i, (uint8_t) 0);
  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(ca->getType()->getElementType());
    for (unsigned i=0, e=ca->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, ca->getOperand(i),
                 offset + i*elementSize);
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
    const StructLayout *sl =
      targetData->getStructLayout(cast<StructType>(cs->getType()));
    for (unsigned i=0, e=cs->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cs->getOperand(i),
                 offset + sl->getElementOffset(i));
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
  } else if (const ConstantDataSequential *cds =
               dyn_cast<ConstantDataSequential>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cds->getElementType());
    for (unsigned i=0, e=cds->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, cds->getElementAsConstant(i),
                             offset + i*elementSize);
#endif
  } else if (!isa<UndefValue>(c)) {
    unsigned StoreBits = targetData->getTypeStoreSizeInBits(c->getType());
    ref<ConstantExpr> C = evalConstant(c);

    // Extend the constant if necessary;
    assert(StoreBits >= C->getWidth() && "Invalid store size!");
    if (StoreBits > C->getWidth())
      C = C->ZExt(StoreBits);

    os->write(offset, C);
  }
}

MemoryObject * Executor::addExternalObject(ExecutionState &state,
                                           void *addr, unsigned size,
                                           bool isReadOnly) {
  MemoryObject *mo = memory->allocateFixed((uint64_t) (unsigned long) addr,
                                           size, 0);
  ObjectState *os = bindObjectInState(state, mo, false);
  for(unsigned i = 0; i < size; i++)
    os->write8(i, ((uint8_t*)addr)[i]);
  if(isReadOnly)
    os->setReadOnly(true);
  return mo;
}


extern void *__dso_handle __attribute__ ((__weak__));

void Executor::initializeGlobals(ExecutionState &state) {
  Module *m = kmodule->module;

  if (m->getModuleInlineAsm() != "")
    klee_warning("executable has module level assembly (ignoring)");
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 3)
  assert(m->lib_begin() == m->lib_end() &&
         "XXX do not support dependent libraries");
#endif
  // represent function globals using the address of the actual llvm function
  // object. given that we use malloc to allocate memory in states this also
  // ensures that we won't conflict. we don't need to allocate a memory object
  // since reading/writing via a function pointer is unsupported anyway.
  for (Module::iterator i = m->begin(), ie = m->end(); i != ie; ++i) {
    Function *f = i;
    ref<ConstantExpr> addr(0);

    // If the symbol has external weak linkage then it is implicitly
    // not defined in this module; if it isn't resolvable then it
    // should be null.
    if (f->hasExternalWeakLinkage() &&
        !externalDispatcher->resolveSymbol(f->getName())) {
      addr = Expr::createPointer(0);
    } else {
      addr = Expr::createPointer((unsigned long) (void*) f);
      legalFunctions.insert((uint64_t) (unsigned long) (void*) f);
    }

    globalAddresses.insert(std::make_pair(f, addr));
  }

  // Disabled, we don't want to promote use of live externals.
#ifdef HAVE_CTYPE_EXTERNALS
#ifndef WINDOWS
#ifndef DARWIN
  /* From /usr/include/errno.h: it [errno] is a per-thread variable. */
  int *errno_addr = __errno_location();
  addExternalObject(state, (void *)errno_addr, sizeof *errno_addr, false);

  /* from /usr/include/ctype.h:
       These point into arrays of 384, so they can be indexed by any `unsigned
       char' value [0,255]; by EOF (-1); or by any `signed char' value
       [-128,-1).  ISO C requires that the ctype functions work for `unsigned */
  const uint16_t **addr = __ctype_b_loc();
  addExternalObject(state, const_cast<uint16_t*>(*addr-128),
                    384 * sizeof **addr, true);
  addExternalObject(state, addr, sizeof(*addr), true);

  const int32_t **lower_addr = __ctype_tolower_loc();
  addExternalObject(state, const_cast<int32_t*>(*lower_addr-128),
                    384 * sizeof **lower_addr, true);
  addExternalObject(state, lower_addr, sizeof(*lower_addr), true);

  const int32_t **upper_addr = __ctype_toupper_loc();
  addExternalObject(state, const_cast<int32_t*>(*upper_addr-128),
                    384 * sizeof **upper_addr, true);
  addExternalObject(state, upper_addr, sizeof(*upper_addr), true);
#endif
#endif
#endif

  // allocate and initialize globals, done in two passes since we may
  // need address of a global in order to initialize some other one.

  // allocate memory objects for all globals
  for (Module::const_global_iterator i = m->global_begin(),
         e = m->global_end();
       i != e; ++i) {
    if (i->isDeclaration()) {
      // FIXME: We have no general way of handling unknown external
      // symbols. If we really cared about making external stuff work
      // better we could support user definition, or use the EXE style
      // hack where we check the object file information.

      LLVM_TYPE_Q Type *ty = i->getType()->getElementType();
      uint64_t size = kmodule->targetData->getTypeStoreSize(ty);

      // XXX - DWD - hardcode some things until we decide how to fix.
#ifndef WINDOWS
      if (i->getName() == "_ZTVN10__cxxabiv117__class_type_infoE") {
        size = 0x2C;
      } else if (i->getName() == "_ZTVN10__cxxabiv120__si_class_type_infoE") {
        size = 0x2C;
      } else if (i->getName() == "_ZTVN10__cxxabiv121__vmi_class_type_infoE") {
        size = 0x2C;
      }
#endif

      if (size == 0) {
        llvm::errs() << "Unable to find size for global variable: "
                     << i->getName()
                     << " (use will result in out of bounds access)\n";
      }

      MemoryObject *mo = memory->allocate(size, false, true, i);
      ObjectState *os = bindObjectInState(state, mo, false);
      globalObjects.insert(std::make_pair(i, mo));
      globalAddresses.insert(std::make_pair(i, mo->getBaseExpr()));

      // Program already running = object already initialized.  Read
      // concrete value and write it to our copy.
      if (size) {
        void *addr;
        if (i->getName() == "__dso_handle") {
          addr = &__dso_handle; // wtf ?
        } else {
          addr = externalDispatcher->resolveSymbol(i->getName());
        }
        if (!addr)
          klee_error("unable to load symbol(%s) while initializing globals.",
                     i->getName().data());

        for (unsigned offset=0; offset<mo->size; offset++)
          os->write8(offset, ((unsigned char*)addr)[offset]);
      }
    } else {
      LLVM_TYPE_Q Type *ty = i->getType()->getElementType();
      uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
      MemoryObject *mo = memory->allocate(size, false, true, &*i);
      if (!mo)
        llvm::report_fatal_error("out of memory");
      ObjectState *os = bindObjectInState(state, mo, false);
      globalObjects.insert(std::make_pair(i, mo));
      globalAddresses.insert(std::make_pair(i, mo->getBaseExpr()));

      if (!i->hasInitializer())
          os->initializeToRandom();
    }
  }

  // link aliases to their definitions (if bound)
  for (Module::alias_iterator i = m->alias_begin(), ie = m->alias_end();
       i != ie; ++i) {
    // Map the alias to its aliasee's address. This works because we have
    // addresses for everything, even undefined functions.
    globalAddresses.insert(std::make_pair(i, evalConstant(i->getAliasee())));
  }

  // once all objects are allocated, do the actual initialization
  for (Module::const_global_iterator i = m->global_begin(),
         e = m->global_end();
       i != e; ++i) {
    if (i->hasInitializer()) {
      MemoryObject *mo = globalObjects.find(i)->second;
      const ObjectState *os = state.addressSpace.findObject(mo);
      assert(os);
      ObjectState *wos = state.addressSpace.getWriteable(mo, os);

      initializeGlobalObject(state, wos, i->getInitializer(), 0);
      // if(i->isConstant()) os->setReadOnly(true);
    }
  }
}

void Executor::branch(ExecutionState &state,
                      const std::vector< ref<Expr> > &conditions,
                      std::vector<ExecutionState*> &result) {
  TimerStatIncrementer timer(stats::forkTime);
  unsigned N = conditions.size();
  assert(N);

  if (MaxForks!=~0u && stats::forks >= MaxForks) {
    unsigned next = theRNG.getInt32() % N;
    for (unsigned i=0; i<N; ++i) {
      if (i == next) {
        result.push_back(&state);
      } else {
        result.push_back(NULL);
      }
    }
  } else {
    stats::forks += N-1;

    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i=1; i<N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(es);
      if(it!=seedMap.end()){
          std::vector<SeedInfo> seeds = it->second;
          seedMap[ns]=seeds;
      }
      addedStates.insert(ns);
      result.push_back(ns);
      es->ptreeNode->data = 0;
      std::pair<PTree::Node*,PTree::Node*> res =
        processTree->split(es->ptreeNode, ns, es);
      ns->ptreeNode = res.first;
      es->ptreeNode = res.second;


    //bupt use
    if(ns->isSPEO())
    {
        ExecutionState *new_parent=*(es->splitStates.begin());
        ExecutionState *new_state=new_parent->branch();
        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(new_parent);
        if(it!=seedMap.end()){
            std::vector<SeedInfo> seeds = it->second;
            seedMap[new_state]=seeds;
        }
        new_parent->ptreeNode->data=0;
        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(new_parent->ptreeNode, new_state, new_parent);
        new_state->ptreeNode=res.first;
        new_parent->ptreeNode=res.second;
        // For each new forked/branched state in SPEO mode,
        // initial its splitStates from parent state splitStates.begin()
        // new_state is the root state in SPEN matched with state in SPEO
        ns->splitStates.push_back(new_state);
        new_state->splitStates.push_back(ns);
    }
    else if(ns->isSPEN())
        ns->splitStates=es->splitStates;
    }
  }

  // If necessary redistribute seeds to match conditions, killing
  // states if necessary due to OnlyReplaySeeds (inefficient but
  // simple).

  if(!BuptShadow){
      std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
        seedMap.find(&state);
      if (it != seedMap.end()) {
        std::vector<SeedInfo> seeds = it->second;
        seedMap.erase(it);

        // Assume each seed only satisfies one condition (necessarily true
        // when conditions are mutually exclusive and their conjunction is
        // a tautology).
        for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
               siie = seeds.end(); siit != siie; ++siit) {
          unsigned i;
          for (i=0; i<N; ++i) {
            ref<ConstantExpr> res;
            bool success =
              solver->getValue(state, siit->assignment.evaluate(conditions[i]),
                               res);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            if (res->isTrue())
              break;
          }

          // If we didn't find a satisfying condition randomly pick one
          // (the seed will be patched).
          if (i==N)
            i = theRNG.getInt32() % N;

          // Extra check in case we're replaying seeds with a max-fork
          if (result[i])
            seedMap[result[i]].push_back(*siit);
        }

        if (OnlyReplaySeeds) {
          for (unsigned i=0; i<N; ++i) {
            if (result[i] && !seedMap.count(result[i])) {
              terminateState(*result[i]);
              result[i] = NULL;
            }
          }
        }
      }
  }

  for (unsigned i=0; i<N; ++i)
    if (result[i])
      addConstraint(*result[i], conditions[i]);
}

Executor::StatePair
Executor::fork(ExecutionState &current, ref<Expr> condition, bool isInternal) {
    if(debug==1){
        errs()<<"fork condition:\n"<<condition<<"\n";
    }
  Solver::Validity res;
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
    seedMap.find(&current);
  bool isSeeding = it != seedMap.end();

  if (!isSeeding && !isa<ConstantExpr>(condition) &&
      (MaxStaticForkPct!=1. || MaxStaticSolvePct != 1. ||
       MaxStaticCPForkPct!=1. || MaxStaticCPSolvePct != 1.) &&
      statsTracker->elapsed() > 60.) {
    StatisticManager &sm = *theStatisticManager;
    CallPathNode *cpn = current.stack.back().callPathNode;
    if ((MaxStaticForkPct<1. &&
         sm.getIndexedValue(stats::forks, sm.getIndex()) >
         stats::forks*MaxStaticForkPct) ||
        (MaxStaticCPForkPct<1. &&
         cpn && (cpn->statistics.getValue(stats::forks) >
                 stats::forks*MaxStaticCPForkPct)) ||
        (MaxStaticSolvePct<1 &&
         sm.getIndexedValue(stats::solverTime, sm.getIndex()) >
         stats::solverTime*MaxStaticSolvePct) ||
        (MaxStaticCPForkPct<1. &&
         cpn && (cpn->statistics.getValue(stats::solverTime) >
                 stats::solverTime*MaxStaticCPSolvePct))) {
      ref<ConstantExpr> value;
      bool success = solver->getValue(current, condition, value);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      addConstraint(current, EqExpr::create(value, condition));
      condition = value;
    }
  }

  double timeout = coreSolverTimeout;
  if (isSeeding)
    timeout *= it->second.size();
  solver->setTimeout(timeout);
  bool success = solver->evaluate(current, condition, res, !current.hasChangedBefore());
  solver->setTimeout(0);
  if (!success) {
    current.pc = current.prevPC;
    terminateStateEarly(current, "Query timed out (fork).");
    return StatePair(0, 0);
  }

  if(res == Solver::Conflict){
    removedStates.insert(&current);
    updateStates(&current);
    return StatePair(0, 0);
  }

  if (!isSeeding) {
    if (replayPath && !isInternal) {
      assert(replayPosition<replayPath->size() &&
             "ran out of branches in replay path mode");
      bool branch = (*replayPath)[replayPosition++];

      if (res==Solver::True) {
        assert(branch && "hit invalid branch in replay path mode");
      } else if (res==Solver::False) {
        assert(!branch && "hit invalid branch in replay path mode");
      } else {
        // add constraints
        if(branch) {
          res = Solver::True;
          addConstraint(current, condition);
        } else  {
          res = Solver::False;
          addConstraint(current, Expr::createIsZero(condition));
        }
      }
    } else if (res==Solver::Unknown) {
      assert(!replayOut && "in replay mode, only one branch can be true.");

      if ((MaxMemoryInhibit && atMemoryLimit) ||
          current.forkDisabled ||
          inhibitForking ||
          (MaxForks!=~0u && stats::forks >= MaxForks)) {

    if (MaxMemoryInhibit && atMemoryLimit)
      klee_warning_once(0, "skipping fork (memory cap exceeded)");
    else if (current.forkDisabled)
      klee_warning_once(0, "skipping fork (fork disabled on current path)");
    else if (inhibitForking)
      klee_warning_once(0, "skipping fork (fork disabled globally)");
    else
      klee_warning_once(0, "skipping fork (max-forks reached)");

        TimerStatIncrementer timer(stats::forkTime);
        if (theRNG.getBool()) {
          addConstraint(current, condition);
          res = Solver::True;
        } else {
          addConstraint(current, Expr::createIsZero(condition));
          res = Solver::False;
        }
      }
    }
  }

  // Fix branch in only-replay-seed mode, if we don't have both true
  // and false seeds.
  if (!BuptShadow && isSeeding &&
      (current.forkDisabled || OnlyReplaySeeds) &&
      res == Solver::Unknown) {
    bool trueSeed=false, falseSeed=false;
    // Is seed extension still ok here?
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
           siie = it->second.end(); siit != siie; ++siit) {
      ref<ConstantExpr> res;
      bool success =
        solver->getValue(current, siit->assignment.evaluate(condition), res);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res->isTrue()) {
        trueSeed = true;
      } else {
        falseSeed = true;
      }
      if (trueSeed && falseSeed)
        break;
    }
    if (!(trueSeed && falseSeed)) {
      assert(trueSeed || falseSeed);

      res = trueSeed ? Solver::True : Solver::False;
      addConstraint(current, trueSeed ? condition : Expr::createIsZero(condition));
    }
  }


  // XXX - even if the constraint is provable one way or the other we
  // can probably benefit by adding this constraint and allowing it to
  // reduce the other constraints. For example, if we do a binary
  // search on a particular value, and then see a comparison against
  // the value it has been fixed at, we should take this as a nice
  // hint to just use the single constraint instead of all the binary
  // search ones. If that makes sense.
  if (res==Solver::True) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "1";
      }
    }
    if(BuptShadow)
        addConstraint(current,condition);
    return StatePair(&current, 0);
  } else if (res==Solver::False) {
    if (!isInternal) {
      if (pathWriter) {
        current.pathOS << "0";
      }
    }
    if(BuptShadow)
    addConstraint(current,Expr::createIsZero(condition));
    return StatePair(0, &current);
  } else {
    TimerStatIncrementer timer(stats::forkTime);
    ExecutionState *falseState, *trueState = &current;

    ++stats::forks;

    falseState = trueState->branch();
    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&current);
    if(it!=seedMap.end()){
        std::vector<SeedInfo> seeds = it->second;
        seedMap[falseState]=seeds;
        seedMap[trueState]=seeds;
    }
    addedStates.insert(falseState);


    //bupt use
    if(falseState->isSPEO())
    {
        ExecutionState *new_parent=*(trueState->splitStates.begin());
        ExecutionState *new_state=new_parent->branch();
        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(new_parent); // XXX:select seedInfo from new_parent?
        if(it!=seedMap.end()){
            std::vector<SeedInfo> seeds = it->second;
            seedMap[new_state]=seeds;
        }
        new_parent->ptreeNode->data=0;
        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(new_parent->ptreeNode, new_state, new_parent);
        new_state->ptreeNode=res.first;
        new_parent->ptreeNode=res.second;
        falseState->splitStates.push_back(new_state);
        new_state->splitStates.push_back(falseState);
    }
    else if(falseState->isSPEN()){
        ExecutionState *old_parent=*(trueState->splitStates.begin());
        old_parent->splitStates.push_back(falseState);
        falseState->splitStates.push_back(old_parent);
    }

    if (RandomizeFork && theRNG.getBool())
      std::swap(trueState, falseState);

    if (!BuptShadow && it != seedMap.end()) {
      std::vector<SeedInfo> seeds = it->second;
      it->second.clear();
      std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
      std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
      for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
             siie = seeds.end(); siit != siie; ++siit) {
        ref<ConstantExpr> res;
        bool success =
          solver->getValue(current, siit->assignment.evaluate(condition), res);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (res->isTrue()) {
          trueSeeds.push_back(*siit);
        } else {
          falseSeeds.push_back(*siit);
        }
      }

      bool swapInfo = false;
      if (trueSeeds.empty()) {
        if (&current == trueState) swapInfo = true;
        seedMap.erase(trueState);
      }
      if (falseSeeds.empty()) {
        if (&current == falseState) swapInfo = true;
        seedMap.erase(falseState);
      }
      if (swapInfo) {
        std::swap(trueState->coveredNew, falseState->coveredNew);
        std::swap(trueState->coveredLines, falseState->coveredLines);
      }
    }

    current.ptreeNode->data = 0;
    std::pair<PTree::Node*, PTree::Node*> res =
      processTree->split(current.ptreeNode, falseState, trueState);
    falseState->ptreeNode = res.first;
    trueState->ptreeNode = res.second;

    if (!isInternal) {
      if (pathWriter) {
        falseState->pathOS = pathWriter->open(current.pathOS);
        trueState->pathOS << "1";
        falseState->pathOS << "0";
      }
      if (symPathWriter) {
        falseState->symPathOS = symPathWriter->open(current.symPathOS);
        trueState->symPathOS << "1";
        falseState->symPathOS << "0";
      }
    }

    addConstraint(*trueState, condition);
    addConstraint(*falseState, Expr::createIsZero(condition));

    // Kinda gross, do we even really still want this option?
    if (MaxDepth && MaxDepth<=trueState->depth) {
      terminateStateEarly(*trueState, "max-depth exceeded.");
      terminateStateEarly(*falseState, "max-depth exceeded.");
      return StatePair(0, 0);
    }
    if(debug==1){
        errs()<<"fork and remain two states\n";
        errs()<<"true state: "<<trueState <<"\n"
            <<"false state: "<<falseState<< "\n";
    }

    return StatePair(trueState, falseState);
  }
}

void Executor::addConstraint(ExecutionState &state, ref<Expr> condition) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }

  // Check to see if this constraint violates seeds.
  if(!BuptShadow){
      std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
        seedMap.find(&state);
      if (it != seedMap.end()) {
        bool warn = false;
        for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
               siie = it->second.end(); siit != siie; ++siit) {
          bool res;
          bool success =
            solver->mustBeFalse(state, siit->assignment.evaluate(condition), res);
          assert(success && "FIXME: Unhandled solver failure");
          (void) success;
          if (res) {
            siit->patchSeed(state, condition, solver);
            warn = true;
          }
        }
        if (warn)
          klee_warning("seeds patched for violating constraint");
      }
  }
  if(debug_addconst==1){
      if(state.isSPEO()){
          errs()<<"old state "<<&state<<" add condition: \n"<<condition<<"\n";
      } else if (state.isSPEN()){
          errs()<<"new state "<<&state<<" add condition: \n"<<condition<<"\n";
      } else {
          errs()<<"uni state "<<&state<<" add condition: \n"<<condition<<"\n";
      }
  }

  state.addConstraint(condition);
  if (ivcEnabled)
    doImpliedValueConcretization(state, condition,
                                 ConstantExpr::alloc(1, Expr::Bool));
  if(debug_constraint==1){
      klee_message("state %d added constraint %d:",&state,state.pcId);
      state.constraints.back()->dump();
  }
  state.pcId++;
}

ref<klee::ConstantExpr> Executor::evalConstant(const Constant *c) {
  if (const llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
    return evalConstantExpr(ce);
  } else {
    if (const ConstantInt *ci = dyn_cast<ConstantInt>(c)) {
      return ConstantExpr::alloc(ci->getValue());
    } else if (const ConstantFP *cf = dyn_cast<ConstantFP>(c)) {
      return ConstantExpr::alloc(cf->getValueAPF().bitcastToAPInt());
    } else if (const GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      return globalAddresses.find(gv)->second;
    } else if (isa<ConstantPointerNull>(c)) {
      return Expr::createPointer(0);
    } else if (isa<UndefValue>(c) || isa<ConstantAggregateZero>(c)) {
      return ConstantExpr::create(0, getWidthForLLVMType(c->getType()));
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
    } else if (const ConstantDataSequential *cds =
                 dyn_cast<ConstantDataSequential>(c)) {
      std::vector<ref<Expr> > kids;
      for (unsigned i = 0, e = cds->getNumElements(); i != e; ++i) {
        ref<Expr> kid = evalConstant(cds->getElementAsConstant(i));
        kids.push_back(kid);
      }
      ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
      return cast<ConstantExpr>(res);
#endif
    } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
      const StructLayout *sl = kmodule->targetData->getStructLayout(cs->getType());
      llvm::SmallVector<ref<Expr>, 4> kids;
      for (unsigned i = cs->getNumOperands(); i != 0; --i) {
        unsigned op = i-1;
        ref<Expr> kid = evalConstant(cs->getOperand(op));

        uint64_t thisOffset = sl->getElementOffsetInBits(op),
                 nextOffset = (op == cs->getNumOperands() - 1)
                              ? sl->getSizeInBits()
                              : sl->getElementOffsetInBits(op+1);
        if (nextOffset-thisOffset > kid->getWidth()) {
          uint64_t paddingWidth = nextOffset-thisOffset-kid->getWidth();
          kids.push_back(ConstantExpr::create(0, paddingWidth));
        }

        kids.push_back(kid);
      }
      ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
      return cast<ConstantExpr>(res);
    } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)){
      llvm::SmallVector<ref<Expr>, 4> kids;
      for (unsigned i = ca->getNumOperands(); i != 0; --i) {
        unsigned op = i-1;
        ref<Expr> kid = evalConstant(ca->getOperand(op));
        kids.push_back(kid);
      }
      ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
      return cast<ConstantExpr>(res);
    } else {
      // Constant{Vector}
      llvm::report_fatal_error("invalid argument to evalConstant()");
    }
  }
}

const Cell& Executor::eval(KInstruction *ki, unsigned index,
                           ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  assert(vnumber != -1 &&
         "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  if (vnumber < 0) {
    unsigned index = -vnumber - 2;
    return kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    StackFrame &sf = state.stack.back();
    return sf.locals[index];
  }
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state,
                         ref<Expr> value) {
  getDestCell(state, target).value = value;
}

void Executor::bindArgument(KFunction *kf, unsigned index,
                            ExecutionState &state, ref<Expr> value) {
  getArgumentCell(state, kf, index).value = value;
}

ref<Expr> Executor::toUnique(const ExecutionState &state,
                             ref<Expr> &e) {
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;
    ExecutionState buf=state;
    bool changedFlag=buf.hasChangedBefore();
    solver->setTimeout(coreSolverTimeout);
    if (solver->getValue(state, e, value, !changedFlag) &&
        solver->mustBeTrue(state, EqExpr::create(e, value), isTrue, !changedFlag) &&
        isTrue)
      result = value;
    solver->setTimeout(0);
  }

  return result;
}


/* Concretize the given expression, and return a possible constant value.
   'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr>
Executor::toConstant(ExecutionState &state,
                     ref<Expr> e,
                     const char *reason) {
  e = state.constraints.simplifyExpr(e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  ref<ConstantExpr> value;
  bool success;
  if(BuptShadow)
       success = solver->getValue(state, e, value,!state.hasChangedBefore());
  else
       success = solver->getValue(state, e, value);
  assert(success && "FIXME: Unhandled solver failure");
  (void) success;

  std::string str;
  llvm::raw_string_ostream os(str);
  os << "silently concretizing (reason: " << reason << ") expression " << e
     << " to value " << value << " (" << (*(state.pc)).info->file << ":"
     << (*(state.pc)).info->line << ")";

  if (AllExternalWarnings)
    klee_warning(reason, os.str().c_str());
  else
    klee_warning_once(reason, "%s", os.str().c_str());

  addConstraint(state, EqExpr::create(e, value));

  return value;
}

void Executor::executeGetValue(ExecutionState &state,
                               ref<Expr> e,
                               KInstruction *target) {
//bupt use
    if(debug==1){
        errs()<<"getValue input expr: "<<e;
        if(e->isPointer())
            errs()<<" is PointerTy\n";
        else
            errs()<<" is not PointerTy\n";
    }
    if(debug_constraint==2){
        errs() <<"constraints size: "<<state.constraints.size()<<"\n";
        for(ConstraintManager::constraint_iterator pcit=state.constraints.begin(),pcie=state.constraints.end();pcit!=pcie;pcit++){
            (*pcit)->dump();
        }
    }
  if(e->isContainShadow())
  {
    if(state.isUE())
    {
        ref<Expr> old_e=e->findShadowExpr(0);
        ref<Expr> new_e=e->findShadowExpr(1);
        old_e = state.constraints.simplifyExpr(old_e);
        new_e = state.constraints.simplifyExpr(new_e);
        ref<ConstantExpr> new_value,old_value;
        bool success;
        success = solver->getValue(state, old_e, old_value,false);
        if(debug==1){
            errs()<<"getValue get old value: "<<old_value;
            if(old_value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        assert(success && "FIXME: Unhandled solver failure in old version");
        (void) success;
        success = solver->getValue(state, new_e, new_value,false);
        if(debug==1){
            errs()<<"getValue get new value: "<<new_value;
            if(new_value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        assert(success && "FIXME: Unhandled solver failure in new version");
        (void) success;
        ref<Expr> shadowExpr=ShadowExpr::alloc(old_value,new_value);
        bindLocal(target, state, shadowExpr);
    }
    else
    {
        if(state.isSPEO())
            e=e->findShadowExpr(0);
        else if(state.isSPEN())
            e=e->findShadowExpr(1);
        e = state.constraints.simplifyExpr(e);
        ref<ConstantExpr> value;
        bool success;
        success = solver->getValue(state, e, value,false);
        if(debug==1){
            errs()<<"getValue get value: "<<value;
            if(value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        bindLocal(target, state, value);
    }
  }
  else
  {
      e = state.constraints.simplifyExpr(e);
      std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
        seedMap.find(&state);
      if (it==seedMap.end() || isa<ConstantExpr>(e)||BuptShadow) {
        ref<ConstantExpr> value;
        bool success;
        if(state.hasChangedBefore())
            success = solver->getValue(state, e, value, false);
        else
            success = solver->getValue(state, e, value,true);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if(debug==1){
            errs()<<"getValue get value: "<<value;
            if(value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        bindLocal(target, state, value);
      } else {
        std::set< ref<Expr> > values;
        for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
           siie = it->second.end(); siit != siie; ++siit) {
          ref<ConstantExpr> value;
          bool success =
        solver->getValue(state, siit->assignment.evaluate(e), value);
          assert(success && "FIXME: Unhandled solver failure");
          (void) success;
          values.insert(value);
        }

        std::vector< ref<Expr> > conditions;
        for (std::set< ref<Expr> >::iterator vit = values.begin(),
           vie = values.end(); vit != vie; ++vit)
          conditions.push_back(EqExpr::create(e, *vit));

        std::vector<ExecutionState*> branches;
        branch(state, conditions, branches);

        std::vector<ExecutionState*>::iterator bit = branches.begin();
        for (std::set< ref<Expr> >::iterator vit = values.begin(),
           vie = values.end(); vit != vie; ++vit) {
          ExecutionState *es = *bit;
          if (es)
        bindLocal(target, *es, *vit);
          ++bit;
        }
      }
  }
}

void Executor::stepInstruction(ExecutionState &state) {
  if (DebugPrintInstructions) {
    printFileLine(state, state.pc);
    llvm::errs().indent(10) << stats::instructions << " ";
    llvm::errs() << *(state.pc->inst) << '\n';
  }

  if (statsTracker)
    statsTracker->stepInstruction(state);

  ++stats::instructions;
  state.prevPC = state.pc;
  ++state.pc;

  if (stats::instructions==StopAfterNInstructions)
    haltExecution = true;
}

void Executor::executeCall(ExecutionState &state,
                           KInstruction *ki,
                           Function *f,
                           std::vector< ref<Expr> > &arguments) {
  Instruction *i = ki->inst;
  if (f && f->isDeclaration()) {
    switch(f->getIntrinsicID()) {
    case Intrinsic::not_intrinsic:
      // state may be destroyed by this call, cannot touch
      callExternalFunction(state, ki, f, arguments);
      break;

      // va_arg is handled by caller and intrinsic lowering, see comment for
      // ExecutionState::varargs
    case Intrinsic::vastart:  {
      StackFrame &sf = state.stack.back();
      assert(sf.varargs &&
             "vastart called in function with no vararg object");

      // FIXME: This is really specific to the architecture, not the pointer
      // size. This happens to work fir x86-32 and x86-64, however.
      Expr::Width WordSize = Context::get().getPointerWidth();
      //bupt use
      ObjectPair op;
      ObjectPair shadow_op;
      bool success=false;
      bool shadow_success=false;
      bool shadow_addr=false;
      ref<Expr> old_arg,new_arg;
      if(arguments[0]->isContainShadow()){
          if(state.isSPEO()){
            old_arg=arguments[0]->findShadowExpr(0);
            new_arg=old_arg;
          }
            //arguments[0]=arguments[0]->findShadowExpr(0);
          else if(state.isSPEN()){
            new_arg=arguments[0]->findShadowExpr(1);
            old_arg=new_arg;
          }
            //arguments[0]=arguments[0]->findShadowExpr(1);
        else {
            shadow_addr=true;
            old_arg=arguments[0]->findShadowExpr(0);
            new_arg=arguments[0]->findShadowExpr(1);
        }
      } else {
          old_arg=arguments[0];
      }

      //bool result=state.addressSpace.resolveOne(state,solver,arguments[0],op,success);
      bool result=state.addressSpace.resolveOne(state,solver,old_arg,op,success);
      bool shadow_result=false;

      if(result && success)
      {
        MemoryObject *mo=const_cast<MemoryObject*>(op.first);
        mo->isStoreVararg=true;
      }

      if(shadow_addr){
          //shadow_addr == true represent that the two version's vararg stored in different memoryObject
          //XXX: rare happened
          //XXX: supposed to discard
          shadow_result=state.addressSpace.resolveOne(state,solver,new_arg,shadow_op,shadow_success);
          if(shadow_result && shadow_success)
          {
            MemoryObject *shadow_mo=const_cast<MemoryObject*>(shadow_op.first);
            shadow_mo->isStoreVararg=true;
          }
          if (WordSize == Expr::Int32) {
            if(sf.argShadow)
            {
                ref<Expr> old_valist=sf.addrOfShadow->findShadowExpr(0);
                ref<Expr> new_valist=sf.addrOfShadow->findShadowExpr(1);
                executeMemoryOperation(state, true, old_arg,
                                   old_valist, 0);
                executeMemoryOperation(state, true, new_arg,
                                   new_valist, 0);
            }
            else
            {
                executeMemoryOperation(state, true, old_arg,
                                   sf.varargs->getBaseExpr(), 0);
                executeMemoryOperation(state, true, new_arg,
                                   sf.varargs->getBaseExpr(), 0);
            }
          } else {
            assert(WordSize == Expr::Int64 && "Unknown word size!");

            // X86-64 has quite complicated calling convention. However,
            // instead of implementing it, we can do a simple hack: just
            // make a function believe that all varargs are on stack.
            executeMemoryOperation(state, true, old_arg,
                                   ConstantExpr::create(48, 32), 0); // gp_offset
            executeMemoryOperation(state, true, new_arg,
                                   ConstantExpr::create(48, 32), 0); // gp_offset

            executeMemoryOperation(state, true,
                                   AddExpr::create(old_arg,
                                                   ConstantExpr::create(4, 64)),
                                   ConstantExpr::create(304, 32), 0); // fp_offset
            executeMemoryOperation(state, true,
                                   AddExpr::create(new_arg,
                                                   ConstantExpr::create(4, 64)),
                                   ConstantExpr::create(304, 32), 0); // fp_offset
            if(sf.argShadow)
            {
                ref<Expr> old_valist=sf.addrOfShadow->findShadowExpr(0);
                ref<Expr> new_valist=sf.addrOfShadow->findShadowExpr(1);
                executeMemoryOperation(state, true,
                                   AddExpr::create(old_arg,
                                                   ConstantExpr::create(8, 64)),
                                   old_valist, 0); // overflow_arg_area
                executeMemoryOperation(state, true,
                                   AddExpr::create(new_arg,
                                                   ConstantExpr::create(8, 64)),
                                   new_valist, 0); // overflow_arg_area
            }
            else
            {
                executeMemoryOperation(state, true,
                                       AddExpr::create(old_arg,
                                                       ConstantExpr::create(8, 64)),
                                       sf.varargs->getBaseExpr(), 0); // overflow_arg_area
                executeMemoryOperation(state, true,
                                       AddExpr::create(new_arg,
                                                       ConstantExpr::create(8, 64)),
                                       sf.varargs->getBaseExpr(), 0); // overflow_arg_area
            }
            executeMemoryOperation(state, true,
                                   AddExpr::create(old_arg,
                                                   ConstantExpr::create(16, 64)),
                                   ConstantExpr::create(0, 64), 0); // reg_save_area
            executeMemoryOperation(state, true,
                                   AddExpr::create(new_arg,
                                                   ConstantExpr::create(16, 64)),
                                   ConstantExpr::create(0, 64), 0); // reg_save_area
          }
      } else {
          if (WordSize == Expr::Int32) {
            if(sf.argShadow)
            {
                executeMemoryOperation(state, true, arguments[0],
                                   sf.addrOfShadow, 0);
            }
            else
            {
                executeMemoryOperation(state, true, arguments[0],
                                   sf.varargs->getBaseExpr(), 0);
            }
          } else {
            assert(WordSize == Expr::Int64 && "Unknown word size!");

            // X86-64 has quite complicated calling convention. However,
            // instead of implementing it, we can do a simple hack: just
            // make a function believe that all varargs are on stack.
            executeMemoryOperation(state, true, arguments[0],
                                   ConstantExpr::create(48, 32), 0); // gp_offset
            executeMemoryOperation(state, true,
                                   AddExpr::create(arguments[0],
                                                   ConstantExpr::create(4, 64)),
                                   ConstantExpr::create(304, 32), 0); // fp_offset
            if(sf.argShadow)
            {
                    executeMemoryOperation(state, true,
                                       AddExpr::create(arguments[0],
                                                       ConstantExpr::create(8, 64)),
                                       sf.addrOfShadow, 0); // overflow_arg_area
            }
            else
            {
                executeMemoryOperation(state, true,
                                       AddExpr::create(arguments[0],
                                                       ConstantExpr::create(8, 64)),
                                       sf.varargs->getBaseExpr(), 0); // overflow_arg_area
            }
            executeMemoryOperation(state, true,
                                   AddExpr::create(arguments[0],
                                                   ConstantExpr::create(16, 64)),
                                   ConstantExpr::create(0, 64), 0); // reg_save_area
          }
      }
      break;
    }
    case Intrinsic::vaend:
      // va_end is a noop for the interpreter.
      //
      // FIXME: We should validate that the target didn't do something bad
      // with vaeend, however (like call it twice).
      break;

    case Intrinsic::vacopy:
      // va_copy should have been lowered.
      //
      // FIXME: It would be nice to check for errors in the usage of this as
      // well.
    default:
      klee_error("unknown intrinsic: %s", f->getName().data());
    }

    if (InvokeInst *ii = dyn_cast<InvokeInst>(i))
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
  } else {
    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = kmodule->functionMap[f];
    state.pushFrame(state.prevPC, kf);
    state.pc = kf->instructions;

    if (statsTracker)
      statsTracker->framePushed(state, &state.stack[state.stack.size()-2]);

     // TODO: support "byval" parameter attribute
     // TODO: support zeroext, signext, sret attributes

    unsigned callingArgs = arguments.size();
    unsigned funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs) {
        klee_warning_once(f, "calling %s with extra arguments.",
                          f->getName().data());
      } else if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              "user.err");
        return;
      }
    } else {
      Expr::Width WordSize = Context::get().getPointerWidth();

      if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              "user.err");
        return;
      }

      StackFrame &sf = state.stack.back();
      unsigned size = 0;
      for (unsigned i = funcArgs; i < callingArgs; i++) {
        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work fir x86-32 and x86-64, however.
        if (WordSize == Expr::Int32) {
          size += Expr::getMinBytesForWidth(arguments[i]->getWidth());
        } else {
          Expr::Width argWidth = arguments[i]->getWidth();
          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a 16
          // byte boundary if alignment needed by type exceeds 8 byte boundary.
          //
          // Alignment requirements for scalar types is the same as their size
          if (argWidth > Expr::Int64) {
             size = llvm::RoundUpToAlignment(size, 16);
          }
          size += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
        }
      }

      MemoryObject *mo = sf.varargs = memory->allocate(size, true, false,
                                                       state.prevPC->inst);
      mo->isVararg=true;
      if (!mo) {
        terminateStateOnExecError(state, "out of memory (varargs)");
        return;
      }

      if ((WordSize == Expr::Int64) && (mo->address & 15)) {
        // Both 64bit Linux/Glibc and 64bit MacOSX should align to 16 bytes.
        klee_warning_once(0, "While allocating varargs: malloc did not align to 16 bytes.");
      }

      ObjectState *os = bindObjectInState(state, mo, true);
      unsigned offset = 0;
//bupt use
      if(state.isUE())
      {
          for (unsigned i = funcArgs; i < callingArgs; i++) {
          // FIXME: This is really specific to the architecture, not the pointer
          // size. This happens to work fir x86-32 and x86-64, however.
              if(arguments[i]->isContainShadow())
              {
                  sf.argShadow=true;
                  break;
              }
          }
          MemoryObject *double_mo;
          ObjectState *double_os;
          if(sf.argShadow)
          {
              double_mo = memory->allocate(size, true, false, state.prevPC->inst);
              double_mo->isVararg=true;
              if (!double_mo) {
                terminateStateOnExecError(state, "out of memory (varargs)");
                return;
              }
              double_os = bindObjectInState(state, double_mo, true);
          }
              for (unsigned i = funcArgs; i < callingArgs; i++) {
          // FIXME: This is really specific to the architecture, not the pointer
          // size. This happens to work fir x86-32 and x86-64, however.
              if(sf.argShadow)
              {

                  if(arguments[i]->isContainShadow()){
                      ref<Expr> left=arguments[i]->findShadowExpr(0);
                      ref<Expr> right=arguments[i]->findShadowExpr(1);
                      Expr::Width WordSize = Context::get().getPointerWidth();
                      if (WordSize == Expr::Int32) {
                        os->write(offset, left);
                        double_os->write(offset, right);
                        sf.varargsMap[offset]=arguments[i]->getWidth();
                        offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
                      } else {
                        assert(WordSize == Expr::Int64 && "Unknown word size!");
                        Expr::Width argWidth = arguments[i]->getWidth();
                        if (argWidth > Expr::Int64) {
                           offset = llvm::RoundUpToAlignment(offset, 16);
                        }
                        os->write(offset, left);
                        double_os->write(offset, right);
                        sf.varargsMap[offset]=argWidth;
                        offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
                      }
                  } else {
                      if (WordSize == Expr::Int32) {
                        os->write(offset, arguments[i]);
                        offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
                      } else {
                        assert(WordSize == Expr::Int64 && "Unknown word size!");

                        Expr::Width argWidth = arguments[i]->getWidth();
                        if (argWidth > Expr::Int64) {
                           offset = llvm::RoundUpToAlignment(offset, 16);
                        }
                        os->write(offset, arguments[i]);
                        offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
                      }
                  }
              }
              else
              {
                  if (WordSize == Expr::Int32) {
                    os->write(offset, arguments[i]);
                    offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
                  } else {
                    assert(WordSize == Expr::Int64 && "Unknown word size!");

                    Expr::Width argWidth = arguments[i]->getWidth();
                    if (argWidth > Expr::Int64) {
                       offset = llvm::RoundUpToAlignment(offset, 16);
                    }
                    os->write(offset, arguments[i]);
                    offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
                  }
              }
          }
          if(sf.argShadow)
          {
              sf.addrOfShadow=ShadowExpr::create(mo->getBaseExpr(),double_mo->getBaseExpr());
          }
      }
      else
      {
          for (unsigned i = funcArgs; i < callingArgs; i++) {
              if(arguments[i]->isContainShadow())
              {
                  if(state.isSPEO())
                      arguments[i]=arguments[i]->findShadowExpr(0);
                  else if(state.isSPEN())
                      arguments[i]=arguments[i]->findShadowExpr(1);
              }
              if (WordSize == Expr::Int32) {
                os->write(offset, arguments[i]);
                offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
              } else {
                assert(WordSize == Expr::Int64 && "Unknown word size!");

                Expr::Width argWidth = arguments[i]->getWidth();
                if (argWidth > Expr::Int64) {
                   offset = llvm::RoundUpToAlignment(offset, 16);
                }
                os->write(offset, arguments[i]);
                offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
              }
          }
      }
    }
    unsigned numFormals = f->arg_size();
    for (unsigned i=0; i<numFormals; ++i)
        bindArgument(kf, i, state, arguments[i]);
  }
  std::string funcName=f->getName().str();
  const FunctionType *fType =
      dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
  StackFrame &current_stack=state.stack.back();
  std::map<std::string,int>::iterator it=concernFunction.find(funcName);
  if(it!=concernFunction.end() && current_stack.kf->function->getName().str()==funcName)
     current_stack.concernFlag=true;

  //collect EDS target
  if(it!=concernFunction.end() && current_stack.concernFlag && current_stack.kf->function->getName().str()==funcName){
        int i=0;
        for(std::vector< ref<Expr> >::iterator ai=arguments.begin(),ae=arguments.end();ai!=ae;++ai,++i){
            if(i<f->arg_size() && fType->getParamType(i)->isPointerTy()){
                if(state.isUE())
                {
                    ref<Expr> addr=(*ai);
                    bool success;
                    ObjectPair op;
                    if(addr->isContainShadow())
                    {
                        ref<Expr> old_addr=(*ai)->findShadowExpr(0);
                        ref<Expr> new_addr=(*ai)->findShadowExpr(1);
                        ref<Expr> dif_a=EqExpr::create(old_addr,new_addr);
                        bool mustBeTrue;
                        success = solver->mustBeTrue(state,dif_a,mustBeTrue,false);
                        assert(success && "FIXME: Unhandled solver failure");
                        (void) success;
                        if(!mustBeTrue){
                            current_stack.concernArgsAndGVals[old_addr]=false;
                            current_stack.concernArgsAndGVals[new_addr]=false;
                        }
                        else{
                            current_stack.concernArgsAndGVals[old_addr]=false;
                        }
                    }
                    else
                    {
                        current_stack.concernArgsAndGVals[addr]=false;
                    }
                } else {
                    ref<Expr> addr=(*ai);
                    bool success;
                    ObjectPair op;
                    if(addr->isContainShadow())
                    {
                        if(state.isSPEO())
                            addr=addr->findShadowExpr(0);
                        else if(state.isSPEN())
                            addr=addr->findShadowExpr(1);
                    }
                    current_stack.concernArgsAndGVals[addr]=false;
                }
            }
        }
    }
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src,
                                    ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the eval() result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.

  // XXX this lookup has to go ?
  KFunction *kf = state.stack.back().kf;
  unsigned entry = kf->basicBlockEntry[dst];
  state.pc = &kf->instructions[entry];
  if (state.pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode*>(state.pc->inst);
    state.incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

void Executor::printFileLine(ExecutionState &state, KInstruction *ki) {
  const InstructionInfo &ii = *ki->info;
  if (ii.file != "")
    llvm::errs() << "     " << ii.file << ":" << ii.line << "@"<<ii.assemblyLine;
  else
    llvm::errs() << "     [no debug info]:";
}

/// Compute the true target of a function call, resolving LLVM and KLEE aliases
/// and bitcasts.
Function* Executor::getTargetFunction(Value *calledVal, ExecutionState &state) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv))
        return 0;

      std::string alias = state.getFnAlias(gv->getName());
      if (alias != "") {
        llvm::Module* currModule = kmodule->module;
        GlobalValue *old_gv = gv;
        gv = currModule->getNamedValue(alias);
        if (!gv) {
          llvm::errs() << "Function " << alias << "(), alias for "
                       << old_gv->getName() << " not found!\n";
          assert(0 && "function alias not found");
        }
      }

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

/// TODO remove?
static bool isDebugIntrinsic(const Function *f, KModule *KM) {
  return false;
}

static inline const llvm::fltSemantics * fpWidthToSemantics(unsigned width) {
  switch(width) {
  case Expr::Int32:
    return &llvm::APFloat::IEEEsingle;
  case Expr::Int64:
    return &llvm::APFloat::IEEEdouble;
  case Expr::Fl80:
    return &llvm::APFloat::x87DoubleExtended;
  default:
    return 0;
  }
}

void Executor::executeInstruction(ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
    // Control flow
  case Instruction::Ret: {
    ReturnInst *ri = cast<ReturnInst>(i);
    KInstIterator kcaller = state.stack.back().caller;
    Instruction *caller = kcaller ? kcaller->inst : 0;
    StringRef fnNameRef=state.stack.back().kf->function->getName();
    std::string curr_funcName;
    if(fnNameRef.data()){
    	curr_funcName=fnNameRef.str();
    }
    int cur_level=-1;
    std::map<std::string, int>::iterator cf=concernFunction.find(curr_funcName);
    if(cf!=concernFunction.end())
        cur_level=cf->second;

    //bupt use
    // For concerned function's arguments and global varibales
    if(state.isUE())
    {
        if(state.stack.back().concernFlag || curr_funcName == "__user_main")
        {
            for(std::map<ref<Expr>,bool>::iterator it=state.stack.back().concernArgsAndGVals.begin(),ie=state.stack.back().concernArgsAndGVals.end();it!=ie;it++,i++){
                bool isChanged=it->second;
                if(isChanged){
                        Expr::Width bytes=state.stack.back().concernArgsAndGValsExpr[it->first];
			detectDataDiv(state,it->first,bytes);
		}
            }
        }
    }
    bool isVoidReturn = (ri->getNumOperands() == 0);
    ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);

    if (!isVoidReturn) {
      result = eval(ki, 0, state).value;
    //bupt use
    if(state.isSPEO())
        result=result->findShadowExpr(0);
    else if(state.isSPEN())
        result=result->findShadowExpr(1);
    }

    if (state.stack.size() <= 1) {
          assert(!caller && "caller set on initial stack frame");
        //bupt use
        // For return value in UE
        if(state.isUE() && !isVoidReturn)
        {
            if(result->isContainShadow()){
                ref<Expr> old_result=result->findShadowExpr(0);
                ref<Expr> new_result=result->findShadowExpr(1);
                ref<Expr> dif_result=NeExpr::create(old_result,new_result);
                bool res;
                bool success=solver->mustBeFalse(state,dif_result,res,false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                if(!res){
                    state.needTestCase=true;
                    state.ctlordata=true;
                    if(old_result->isCtrlAffected() || new_result->isCtrlAffected())
                        state.ctlAffected=true;
                }
            }
            if(state.needTestCase)
                terminateStateOnExit(state);
            else
                terminateState(state);

        }
        terminateStateOnExit(state);
    } else {
        if(state.isUE() && !isVoidReturn)
        {
            if(result->isContainShadow()){
                ref<Expr> old_result=result->findShadowExpr(0);
                ref<Expr> new_result=result->findShadowExpr(1);
                ref<Expr> dif_result=NeExpr::create(old_result,new_result);
                bool res;
                bool success=solver->mustBeFalse(state,dif_result,res,false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                if(!res){
                    state.needTestCase=true;
                    state.ctlordata=true;
                    if(old_result->isCtrlAffected() || new_result->isCtrlAffected())
                        state.ctlAffected=true;
                }
            }
            if("__user_main"==curr_funcName)
            {
                terminateStateOnExit(state);
                break;
            }
            else if(state.needTestCase){
                std::string MsgString;
                llvm::raw_string_ostream msg(MsgString);
                msg << "Data Divergence Founded in Function-ret: "<<curr_funcName<<" level: "<<cur_level<<"\n";
                if (ki->info) {
                  msg << "Value: "<< result <<"\n";
                  msg << "File: " << ki->info->file << "\n";
                  msg << "Line: " << ki->info->line << "\n";
                  msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                }
		msg << "Stack: \n";
	    	state.dumpStack(msg);
                state.divmsg=msg.str();
                createTestCaseButNoTerminate(state);
            }
        }

        state.popFrame();

        if (statsTracker)
          statsTracker->framePopped(state);

        if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
          transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
        } else {
          state.pc = kcaller;
          ++state.pc;
        }

        if (!isVoidReturn) {
            LLVM_TYPE_Q Type *t = caller->getType();
            if (t != Type::getVoidTy(getGlobalContext())) {
                // may need to do coercion due to bitcasts
                Expr::Width from = result->getWidth();
                Expr::Width to = getWidthForLLVMType(t);

                if (from != to) {
                    CallSite cs = (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) :
                                 CallSite(cast<CallInst>(caller)));

                    // XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
                    bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
                    bool isSExt = cs.paramHasAttr(0, llvm::Attributes::SExt);
#else
                    bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
#endif
                    if (isSExt) {
                      result = SExtExpr::create(result, to);
                    } else {
                      result = ZExtExpr::create(result, to);
                    }
                }
                bindLocal(kcaller, state, result);
            }
        } else {
            // We check that the return value has no users instead of
            // checking the type, since C defaults to returning int for
            // undeclared functions.
            if (!caller->use_empty()) {
              terminateStateOnExecError(state, "return void when caller expected a result");
            }
        }
    }
    break;
  }
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 1)
  case Instruction::Unwind: {
    for (;;) {
      KInstruction *kcaller = state.stack.back().caller;
      state.popFrame();

      if (statsTracker)
        statsTracker->framePopped(state);

      if (state.stack.empty()) {
        terminateStateOnExecError(state, "unwind from initial stack frame");
        break;
      } else {
        Instruction *caller = kcaller->inst;
        if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
          transferToBasicBlock(ii->getUnwindDest(), caller->getParent(), state);
          break;
        }
      }
    }
    break;
  }
#endif
  case Instruction::Br: {
    BranchInst *bi = cast<BranchInst>(i);
    if (bi->isUnconditional()) {
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
    } else {
      // FIXME: Find a way that we don't have this hidden dependency.
      assert(bi->getCondition() == bi->getOperand(0) &&
             "Wrong operand index!");
      ref<Expr> cond = eval(ki, 0, state).value;
    //bupt use
    if(cond->isContainShadow())
    {
        if(state.isSPEO())
            cond=cond->findShadowExpr(0);
        else if(state.isSPEN())
            cond=cond->findShadowExpr(1);
    }
    //bupt use
    if(state.isUE() && cond->isContainShadow())
    {
        ref<Expr> left, right;
        left=cond->findShadowExpr(0);
        right=cond->findShadowExpr(1);
        /*
        ExecutionState *origin=state.branch();
        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(&state);
        if(siit!=seedMap.end()){
            std::vector<SeedInfo> seeds = siit->second;
            seedMap[origin]=seeds;
        }
        addedStates.insert(origin);
        state.ptreeNode->data=0;
        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(state.ptreeNode, origin,&state);
        origin->ptreeNode=res.first;
        state.ptreeNode=res.second;
        if(debug==1){
            errs()<<"origin_state is "<<origin<<"\n";
            errs()<<"condition is "<<cond<<"\n";
            errs()<<"right is "<<right<<"\n";
        }
        Executor::StatePair branches_new=fork(state,right,false);
        if (statsTracker && state.stack.back().kf->trackCoverage)
            statsTracker->markBranchVisited(branches_new.first, branches_new.second);
        if(branches_new.first)
        {
            if(debug==1){
                errs()<<"left is  "<<left<<"\n";
            }
            Executor::StatePair branches_new1=fork(*branches_new.first,left,false);
            if(branches_new1.first){
                transferToBasicBlock(bi->getSuccessor(0),bi->getParent(),*branches_new1.first);
            }
            if(branches_new1.second)//old->false new->true
            {
                //create test case for control divergence
                branches_new1.second->needTestCase=true;
                std::string MsgString;
                llvm::raw_string_ostream msg(MsgString);
                msg << "Control Divergence\n";
                if (ki->info->file !="") {
                      msg << "Condition: "<< cond <<"\n";
                      msg << "File: " << ki->info->file << "\n";
                      msg << "Line: " << ki->info->line << "\n";
                      msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                }
                branches_new1.second->divmsg=msg.str();
                interpreterHandler->processTestCase(*branches_new1.second, 0, 0);
                branches_new1.second->needTestCase=false;
                //compute merge points and feasible paths
                BasicBlock *leftbb=bi->getSuccessor(0);
                BasicBlock *rightbb=bi->getSuccessor(1);
                bool optiMG=computeMerge(*branches_new1.second, rightbb, leftbb);
                if(optiMG)
                {
                    //create origin pair for each merge point
                    for(std::map<BasicBlock*, bool>::iterator it=branches_new1.second->mergeSet.begin(), ie=branches_new1.second->mergeSet.end();it!=ie;it++)
                    {
                        //record
                        //old state
                        ExecutionState *old_state=origin->branch();
                        ExecutionState *new_state=old_state->branch();
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(origin);
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[old_state]=seeds;
                            seedMap[new_state]=seeds;
                        }
                        addedStates.insert(old_state);
                        origin->ptreeNode->data=0;
                        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(origin->ptreeNode, old_state, origin);
                        old_state->ptreeNode=res.first;
                        origin->ptreeNode=res.second;
                        //new state
                        old_state->ptreeNode->data=0;
                        res=processTree->split(old_state->ptreeNode, new_state, old_state);
                        new_state->ptreeNode=res.first;
                        old_state->ptreeNode=res.second;
                        addConstraint(*old_state, Expr::createIsZero(left));
                        addConstraint(*new_state, right);
                        //record infos
                        old_state->splitfunc=i->getParent()->getParent()->getName().str();
                        old_state->splitframe=old_state->stack.size();
                        old_state->mergePoint=it->first;
                        old_state->intoSPEO();
                        old_state->splitStatus=false;
                        transferToBasicBlock(rightbb,bi->getParent(),*old_state);
                        new_state->splitfunc=i->getParent()->getParent()->getName().str();
                        new_state->splitframe=new_state->stack.size();
                        new_state->mergePoint=it->first;
                        new_state->intoSPEN();
                        new_state->splitStatus=false;
                        transferToBasicBlock(leftbb,bi->getParent(),*new_state);
                        old_state->splitStates.push_back(new_state);
                        new_state->splitStates.push_back(old_state);
                        if(debug==1){
                            errs()<<"old_state is "<<old_state<<", new_state is "<<new_state<<"\n";
                        }
                    }
                }
                else
                {
                    //record
                    //old state
                    ExecutionState *old_state=origin->branch();
                    ExecutionState *new_state=old_state->branch();
                    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(origin);
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[old_state]=seeds;
                        seedMap[new_state]=seeds;
                    }
                    addedStates.insert(old_state);
                    origin->ptreeNode->data=0;
                    std::pair< PTree::Node*, PTree::Node* > res=processTree->split(origin->ptreeNode, old_state, origin);
                    old_state->ptreeNode=res.first;
                    origin->ptreeNode=res.second;
                    //new state
                    old_state->ptreeNode->data=0;
                    res=processTree->split(old_state->ptreeNode, new_state, old_state);
                    new_state->ptreeNode=res.first;
                    old_state->ptreeNode=res.second;
                    addConstraint(*old_state, Expr::createIsZero(left));
                    addConstraint(*new_state, right);
                    //record infos
                    old_state->splitfunc=i->getParent()->getParent()->getName().str();
                    old_state->splitframe=old_state->stack.size();
                    old_state->mergePoint=branches_new1.second->retPoint;
                    old_state->intoSPEO();
                    old_state->splitStatus=false;
                    transferToBasicBlock(rightbb,bi->getParent(),*old_state);
                    new_state->splitfunc=i->getParent()->getParent()->getName().str();
                    new_state->splitframe=new_state->stack.size();
                    new_state->mergePoint=branches_new1.second->retPoint;
                    new_state->intoSPEN();
                    new_state->splitStatus=false;
                    transferToBasicBlock(leftbb,bi->getParent(),*new_state);
                    old_state->splitStates.push_back(new_state);
                    new_state->splitStates.push_back(old_state);
                    if(debug==1){
                        errs()<<"old_state is "<<old_state<<", new_state is "<<new_state<<"\n";
                    }
                }
                removedStates.insert(branches_new1.second);
            }
            if (statsTracker && state.stack.back().kf->trackCoverage)
                statsTracker->markBranchVisited(branches_new1.first, branches_new1.second);
        }
        if(branches_new.second)
        {
            if(debug==1){
                errs()<<"left is  "<<left<<"\n";
            }
            Executor::StatePair branches_new2=fork(*branches_new.second,left,false);
            if(branches_new2.first)//old->true new->false
            {
                //create test case for control divergence
                branches_new2.first->needTestCase=true;
                std::string MsgString;
                llvm::raw_string_ostream msg(MsgString);
                msg << "Control Divergence\n";
                if (ki->info->file !="") {
                      msg << "Condition: "<< cond <<"\n";
                      msg << "File: " << ki->info->file << "\n";
                      msg << "Line: " << ki->info->line << "\n";
                      msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                }
                branches_new2.first->divmsg=msg.str();
                interpreterHandler->processTestCase(*branches_new2.first, 0, 0);
                branches_new2.first->needTestCase=false;
                //compute merge points and feasible paths
                BasicBlock *leftbb=bi->getSuccessor(0);
                BasicBlock *rightbb=bi->getSuccessor(1);
                bool optiMG=computeMerge(*branches_new2.first, rightbb, leftbb);
                if(optiMG)
                {
                    //create origin pair for each merge point
                    for(std::map<BasicBlock*, bool>::iterator it=branches_new2.first->mergeSet.begin(), ie=branches_new2.first->mergeSet.end();it!=ie;it++)
                    {
                        //record
                        //old state
                        ExecutionState *old_state=origin->branch();
                        ExecutionState *new_state=old_state->branch();
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(origin);
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[old_state]=seeds;
                            seedMap[new_state]=seeds;
                        }
                        addedStates.insert(old_state);
                        origin->ptreeNode->data=0;
                        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(origin->ptreeNode, old_state, origin);
                        old_state->ptreeNode=res.first;
                        origin->ptreeNode=res.second;
                        //new state
                        old_state->ptreeNode->data=0;
                        res=processTree->split(old_state->ptreeNode, new_state, old_state);
                        new_state->ptreeNode=res.first;
                        old_state->ptreeNode=res.second;
                        addConstraint(*old_state, left);
                        addConstraint(*new_state, Expr::createIsZero(right));
                        //record infos
                        old_state->splitfunc=i->getParent()->getParent()->getName().str();
                        old_state->splitframe=old_state->stack.size();
                        old_state->mergePoint=it->first;
                        old_state->intoSPEO();
                        old_state->splitStatus=false;
                        transferToBasicBlock(leftbb,bi->getParent(),*old_state);
                        new_state->splitfunc=i->getParent()->getParent()->getName().str();
                        new_state->splitframe=new_state->stack.size();
                        new_state->mergePoint=it->first;
                        new_state->intoSPEN();
                        new_state->splitStatus=false;
                        transferToBasicBlock(rightbb,bi->getParent(),*new_state);
                        old_state->splitStates.push_back(new_state);
                        new_state->splitStates.push_back(old_state);
                    }
                }
                else
                {
                    //record
                    //old state
                    ExecutionState *old_state=origin->branch();
                    ExecutionState *new_state=old_state->branch();
                    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(origin);
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[old_state]=seeds;
                        seedMap[new_state]=seeds;
                    }
                    addedStates.insert(old_state);
                    origin->ptreeNode->data=0;
                    std::pair< PTree::Node*, PTree::Node* > res=processTree->split(origin->ptreeNode, old_state, origin);
                    old_state->ptreeNode=res.first;
                    origin->ptreeNode=res.second;
                    //new state
                    old_state->ptreeNode->data=0;
                    res=processTree->split(old_state->ptreeNode, new_state, old_state);
                    new_state->ptreeNode=res.first;
                    old_state->ptreeNode=res.second;
                    addConstraint(*old_state, left);
                    addConstraint(*new_state, Expr::createIsZero(right));
                    //record infos
                    old_state->splitfunc=i->getParent()->getParent()->getName().str();
                    old_state->splitframe=old_state->stack.size();
                    old_state->mergePoint=branches_new2.first->retPoint;
                    old_state->intoSPEO();
                    old_state->splitStatus=false;
                    transferToBasicBlock(leftbb,bi->getParent(),*old_state);
                    new_state->splitfunc=i->getParent()->getParent()->getName().str();
                    new_state->splitframe=new_state->stack.size();
                    new_state->mergePoint=branches_new2.first->retPoint;
                    new_state->intoSPEN();
                    new_state->splitStatus=false;
                    transferToBasicBlock(rightbb,bi->getParent(),*new_state);
                    old_state->splitStates.push_back(new_state);
                    new_state->splitStates.push_back(old_state);
                }
                removedStates.insert(branches_new2.first);
            }
            if(branches_new2.second){
                transferToBasicBlock(bi->getSuccessor(1),bi->getParent(),*branches_new2.second);
                addConstraint(*branches_new2.second, Expr::createIsZero(left));
                addConstraint(*branches_new2.second, Expr::createIsZero(right));
            }
            if (statsTracker && state.stack.back().kf->trackCoverage)
                statsTracker->markBranchVisited(branches_new2.first, branches_new2.second);
        }
        removedStates.insert(origin);
        */
        Executor::StatePair branches_new=fork(state,right,false);
        if (statsTracker && state.stack.back().kf->trackCoverage)
            statsTracker->markBranchVisited(branches_new.first, branches_new.second);
        if(branches_new.first)
        {
            if(debug==1){
                errs()<<"left is  "<<left<<"\n";
            }
            Executor::StatePair branches_new1=fork(*branches_new.first,left,false);
            if(branches_new1.first){
                transferToBasicBlock(bi->getSuccessor(0),bi->getParent(),*branches_new1.first);
            }
            if(branches_new1.second)//old->false new->true
            {
                //create test case for control divergence
                branches_new1.second->needTestCase=true;
                std::string MsgString;
                llvm::raw_string_ostream msg(MsgString);
                msg << "Control Divergence\n";
                if (ki->info->file !="") {
                      msg << "Condition: "<< cond <<"\n";
                      msg << "File: " << ki->info->file << "\n";
                      msg << "Line: " << ki->info->line << "\n";
                      msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                }
                msg << "Stack: \n";
		state.dumpStack(msg);
                branches_new1.second->divmsg=msg.str();
                interpreterHandler->processTestCase(*branches_new1.second, 0, 0);
                branches_new1.second->needTestCase=false;
                //compute merge points and feasible paths
                BasicBlock *leftbb=bi->getSuccessor(0);
                BasicBlock *rightbb=bi->getSuccessor(1);
                bool optiMG=computeMerge(*branches_new1.second, rightbb, leftbb);
                if(optiMG)
                {
                    //create origin pair for each merge point
                    for(std::map<BasicBlock*, bool>::iterator it=branches_new1.second->mergeSet.begin(), ie=branches_new1.second->mergeSet.end();it!=ie;it++)
                    {
                        //record
                        //old state
                        ExecutionState *old_state=branches_new1.second->branch();
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(branches_new1.second);
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[old_state]=seeds;
                        }
                        addedStates.insert(old_state);
                        branches_new1.second->ptreeNode->data=0;
                        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(branches_new1.second->ptreeNode, old_state, branches_new1.second);
                        old_state->ptreeNode=res.first;
                        branches_new1.second->ptreeNode=res.second;
                        //new state
                        ExecutionState *new_state=old_state->branch();
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[new_state]=seeds;
                        }
                        old_state->ptreeNode->data=0;
                        res=processTree->split(old_state->ptreeNode, new_state, old_state);
                        new_state->ptreeNode=res.first;
                        old_state->ptreeNode=res.second;
                      //addConstraint(*old_state, Expr::createIsZero(left));
                      //addConstraint(*new_state, right);
                        //record infos
                        old_state->splitfunc=i->getParent()->getParent()->getName().str();
                        old_state->splitframe=old_state->stack.size();
                        old_state->mergePoint=it->first;
                        old_state->intoSPEO();
                        old_state->splitStatus=false;
                        transferToBasicBlock(rightbb,bi->getParent(),*old_state);
                        new_state->splitfunc=i->getParent()->getParent()->getName().str();
                        new_state->splitframe=new_state->stack.size();
                        new_state->mergePoint=it->first;
                        new_state->intoSPEN();
                        new_state->splitStatus=false;
                        transferToBasicBlock(leftbb,bi->getParent(),*new_state);
                        old_state->splitStates.push_back(new_state);
                        new_state->splitStates.push_back(old_state);
                        if(debug==1){
                            errs()<<"old_state is "<<old_state<<", new_state is "<<new_state<<"\n";
                        }
                    }
                    removedStates.insert(branches_new1.second);
                }
                else
                {
                    //record
                    //old state
                    ExecutionState *old_state=branches_new1.second;
                    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(branches_new1.second);
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[old_state]=seeds;
                    }
                    addedStates.insert(old_state);
                    //new state
                    ExecutionState *new_state=old_state->branch();
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[new_state]=seeds;
                    }
                    old_state->ptreeNode->data=0;
                    std::pair< PTree::Node*, PTree::Node* > res=processTree->split(old_state->ptreeNode, new_state, old_state);
                    new_state->ptreeNode=res.first;
                    old_state->ptreeNode=res.second;
                  //addConstraint(*old_state, Expr::createIsZero(left));
                  //addConstraint(*new_state, right);
                    //record infos
                    old_state->splitfunc=i->getParent()->getParent()->getName().str();
                    old_state->splitframe=old_state->stack.size();
                    old_state->mergePoint=branches_new1.second->retPoint;
                    old_state->intoSPEO();
                    old_state->splitStatus=false;
                    transferToBasicBlock(rightbb,bi->getParent(),*old_state);
                    new_state->splitfunc=i->getParent()->getParent()->getName().str();
                    new_state->splitframe=new_state->stack.size();
                    new_state->mergePoint=branches_new1.second->retPoint;
                    new_state->intoSPEN();
                    new_state->splitStatus=false;
                    transferToBasicBlock(leftbb,bi->getParent(),*new_state);
                    old_state->splitStates.push_back(new_state);
                    new_state->splitStates.push_back(old_state);
                    if(debug==1){
                        errs()<<"old_state is "<<old_state<<", new_state is "<<new_state<<"\n";
                    }
                }
            }
            if (statsTracker && state.stack.back().kf->trackCoverage)
                statsTracker->markBranchVisited(branches_new1.first, branches_new1.second);
        }
        if(branches_new.second)
        {
            if(debug==1){
                errs()<<"left is  "<<left<<"\n";
            }
            Executor::StatePair branches_new2=fork(*branches_new.second,left,false);
            if(branches_new2.first)//old->true new->false
            {
                //create test case for control divergence
                branches_new2.first->needTestCase=true;
                std::string MsgString;
                llvm::raw_string_ostream msg(MsgString);
                msg << "Control Divergence\n";
                if (ki->info->file !="") {
                      msg << "Condition: "<< cond <<"\n";
                      msg << "File: " << ki->info->file << "\n";
                      msg << "Line: " << ki->info->line << "\n";
                      msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                }
                msg << "Stack: \n";
		state.dumpStack(msg);
                branches_new2.first->divmsg=msg.str();
                interpreterHandler->processTestCase(*branches_new2.first, 0, 0);
                branches_new2.first->needTestCase=false;
                //compute merge points and feasible paths
                BasicBlock *leftbb=bi->getSuccessor(0);
                BasicBlock *rightbb=bi->getSuccessor(1);
                bool optiMG=computeMerge(*branches_new2.first, rightbb, leftbb);
                if(optiMG)
                {
                    //create origin pair for each merge point
                    for(std::map<BasicBlock*, bool>::iterator it=branches_new2.first->mergeSet.begin(), ie=branches_new2.first->mergeSet.end();it!=ie;it++)
                    {
                        //record
                        //old state
                        ExecutionState *old_state=branches_new2.first->branch();
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(branches_new2.first);
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[old_state]=seeds;
                        }
                        addedStates.insert(old_state);
                        branches_new2.first->ptreeNode->data=0;
                        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(branches_new2.first->ptreeNode, old_state, branches_new2.first);
                        old_state->ptreeNode=res.first;
                        branches_new2.first->ptreeNode=res.second;
                        //new state
                        ExecutionState *new_state=old_state->branch();
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[new_state]=seeds;
                        }
                        old_state->ptreeNode->data=0;
                        res=processTree->split(old_state->ptreeNode, new_state, old_state);
                        new_state->ptreeNode=res.first;
                        old_state->ptreeNode=res.second;
                        addConstraint(*old_state, left);
                        addConstraint(*new_state, Expr::createIsZero(right));
                        //record infos
                        old_state->splitfunc=i->getParent()->getParent()->getName().str();
                        old_state->splitframe=old_state->stack.size();
                        old_state->mergePoint=it->first;
                        old_state->intoSPEO();
                        old_state->splitStatus=false;
                        transferToBasicBlock(leftbb,bi->getParent(),*old_state);
                        new_state->splitfunc=i->getParent()->getParent()->getName().str();
                        new_state->splitframe=new_state->stack.size();
                        new_state->mergePoint=it->first;
                        new_state->intoSPEN();
                        new_state->splitStatus=false;
                        transferToBasicBlock(rightbb,bi->getParent(),*new_state);
                        old_state->splitStates.push_back(new_state);
                        new_state->splitStates.push_back(old_state);
                    }
                    removedStates.insert(branches_new2.first);
                }
                else
                {
                    //record
                    //old state
                    ExecutionState *old_state=branches_new2.first;
                    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(branches_new2.first);
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[old_state]=seeds;
                    }
                    addedStates.insert(old_state);
                    //new state
                    ExecutionState *new_state=old_state->branch();
                    if(siit!=seedMap.end()){
                        std::vector<SeedInfo> seeds = siit->second;
                        seedMap[new_state]=seeds;
                    }
                    old_state->ptreeNode->data=0;
                    std::pair< PTree::Node*, PTree::Node* > res=processTree->split(old_state->ptreeNode, new_state, old_state);
                    new_state->ptreeNode=res.first;
                    old_state->ptreeNode=res.second;
                    addConstraint(*old_state, left);
                    addConstraint(*new_state, Expr::createIsZero(right));
                    //record infos
                    old_state->splitfunc=i->getParent()->getParent()->getName().str();
                    old_state->splitframe=old_state->stack.size();
                    old_state->mergePoint=branches_new2.first->retPoint;
                    old_state->intoSPEO();
                    old_state->splitStatus=false;
                    transferToBasicBlock(leftbb,bi->getParent(),*old_state);
                    new_state->splitfunc=i->getParent()->getParent()->getName().str();
                    new_state->splitframe=new_state->stack.size();
                    new_state->mergePoint=branches_new2.first->retPoint;
                    new_state->intoSPEN();
                    new_state->splitStatus=false;
                    transferToBasicBlock(rightbb,bi->getParent(),*new_state);
                    old_state->splitStates.push_back(new_state);
                    new_state->splitStates.push_back(old_state);
                }
            }
            if(branches_new2.second){
                transferToBasicBlock(bi->getSuccessor(1),bi->getParent(),*branches_new2.second);
              //addConstraint(*branches_new2.second, Expr::createIsZero(left));
              //addConstraint(*branches_new2.second, Expr::createIsZero(right));
            }
            if (statsTracker && state.stack.back().kf->trackCoverage)
                statsTracker->markBranchVisited(branches_new2.first, branches_new2.second);
        }
    }
    else
    {
        Executor::StatePair branches = fork(state, cond, false);

        // NOTE: There is a hidden dependency here, markBranchVisited
        // requires that we still be in the context of the branch
        // instruction (it reuses its statistic id). Should be cleaned
        // up with convenient instruction specific data.
        if (statsTracker && state.stack.back().kf->trackCoverage)
            statsTracker->markBranchVisited(branches.first, branches.second);

        if (branches.first)
        {
            if(branches.first->stack.size()==branches.first->splitframe && branches.first->mergePoint != branches.first->retPoint && branches.first->isSPEN())
            {
                BasicBlock *ParentBB=bi->getParent();
                BasicBlock *succ=bi->getSuccessor(0);
                ExecutionState::condsWithMG newMap=branches.first->new_pathSequential[branches.first->mergePoint];
    ////        if(!newMap[std::make_pair(ParentBB,succ)])
    ////            removedStates.insert(branches.first);
    ////        else
                    transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
            }
            else
                transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
        }
        if (branches.second)
        {
            if(branches.second->stack.size()==branches.second->splitframe && branches.second->mergePoint != branches.second->retPoint && branches.second->isSPEN())
            {
                BasicBlock *ParentBB=bi->getParent();
                BasicBlock *succ=bi->getSuccessor(1);
                ExecutionState::condsWithMG newMap=branches.second->new_pathSequential[branches.second->mergePoint];
    ////////    if(!newMap[std::make_pair(ParentBB,succ)])
    ////////        removedStates.insert(branches.second);
    ////        else
                    transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);
            }
            else
                transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);
        }
    }
    }
    break;
  }
  case Instruction::Switch: {
    SwitchInst *si = cast<SwitchInst>(i);
    ref<Expr> cond = eval(ki, 0, state).value;
    BasicBlock *bb = si->getParent();
    //bupt use
    ref<Expr> ocond, ocond_old, ocond_new;
    if(BuptShadow && !state.hasChangedBefore())
    {
        ocond=cond;
            cond = toUnique(state, cond);
        ConstantExpr *CE = dyn_cast<ConstantExpr>(cond);
        assert(CE &&
             "non-constant switch condition in Zest mode or concolic execution of shadow");
          // Somewhat gross to create these all the time, but fine till we
          // switch to an internal rep.
          LLVM_TYPE_Q llvm::IntegerType *Ty =
            cast<IntegerType>(si->getCondition()->getType());
          ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
          unsigned index = si->findCaseValue(ci).getSuccessorIndex();
    #else
          unsigned index = si->findCaseValue(ci);
    #endif
          if(index)
            addConstraint(state, EqExpr::create(ocond, cond));
          else
          {
              ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
              for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
               i != e; ++i) {
            ref<Expr> value = evalConstant(i.getCaseValue());
    #else
              for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
            ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif
            ref<Expr> match = EqExpr::create(ocond, value);
            isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
              }
              addConstraint(state, isDefault);
          }
          transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
    }
       else if(state.isUE() && cond->isContainShadow())
    {
        ref<Expr> oldcond, newcond;
        oldcond=cond->findShadowExpr(0);
        ocond_old=oldcond;
        newcond=cond->findShadowExpr(1);
        ocond_new=newcond;
        oldcond=toUnique(state,oldcond);
        newcond=toUnique(state,newcond);
        ocond=ocond_new;
        cond=newcond;
        std::map<BasicBlock*, ref<Expr> > old_targets;
        std::map<BasicBlock*, ref<Expr> > new_targets;
        //check possible branches for new version
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(newcond)) {
              LLVM_TYPE_Q llvm::IntegerType *Ty =
            cast<IntegerType>(si->getCondition()->getType());
              ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
              unsigned index = si->findCaseValue(ci).getSuccessorIndex();
    #else
              unsigned index = si->findCaseValue(ci);
    #endif
              if(index)
                new_targets.insert(std::make_pair(si->getSuccessor(index), EqExpr::create(ocond_new, newcond)));
              else
              {

                ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
                for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
                   i != e; ++i) {
                ref<Expr> value = evalConstant(i.getCaseValue());
    #else
                for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
                ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif
                ref<Expr> match = EqExpr::create(ocond_new, value);
                isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
                }
                new_targets.insert(std::make_pair(si->getDefaultDest(), isDefault));
              }
        }
        else
        {
            ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
            for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
               i != e; ++i) {
            ref<Expr> value = evalConstant(i.getCaseValue());
    #else
            for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
            ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif

            ref<Expr> match = EqExpr::create(ocond_new, value);
            isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
            bool result;
            bool success = solver->mayBeTrue(state, match, result, false);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            if (result) {
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
                  BasicBlock *caseSuccessor = i.getCaseSuccessor();
    #else
                  BasicBlock *caseSuccessor = si->getSuccessor(i);
    #endif
                  std::map<BasicBlock*, ref<Expr> >::iterator it =
                new_targets.insert(std::make_pair(caseSuccessor,
                           ConstantExpr::alloc(0, Expr::Bool))).first;

                  it->second = OrExpr::create(match, it->second);
            }
            }
            bool res;
            bool success = solver->mayBeTrue(state, isDefault, res, false);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            if (res)
            {
            new_targets.insert(std::make_pair(si->getDefaultDest(), isDefault));
            }
        }
        //check possible branches for old version

        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(oldcond)) {
              LLVM_TYPE_Q llvm::IntegerType *Ty =
            cast<IntegerType>(si->getCondition()->getType());
              ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
              unsigned index = si->findCaseValue(ci).getSuccessorIndex();
    #else
              unsigned index = si->findCaseValue(ci);
    #endif
            //bupt use
              if(index)
                old_targets.insert(std::make_pair(si->getSuccessor(index), EqExpr::create(ocond_old, oldcond)));
              else
              {

                ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
                for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
                   i != e; ++i) {
                ref<Expr> value = evalConstant(i.getCaseValue());
    #else
                for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
                ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif
                ref<Expr> match = EqExpr::create(ocond_old, value);
                isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
                }
                old_targets.insert(std::make_pair(si->getDefaultDest(), isDefault));
              }
        }
        else
        {
            ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
            for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
               i != e; ++i) {
            ref<Expr> value = evalConstant(i.getCaseValue());
    #else
            for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
            ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif

            ref<Expr> match = EqExpr::create(ocond_old, value);
            isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
            bool result;
            bool success = solver->mayBeTrue(state, match, result, false);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            if (result) {
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
                  BasicBlock *caseSuccessor = i.getCaseSuccessor();
    #else
                  BasicBlock *caseSuccessor = si->getSuccessor(i);
    #endif
                  std::map<BasicBlock*, ref<Expr> >::iterator it =
                old_targets.insert(std::make_pair(caseSuccessor,
                           ConstantExpr::alloc(0, Expr::Bool))).first;

                  it->second = OrExpr::create(match, it->second);
            }
            }
            bool res;
            bool success = solver->mayBeTrue(state, isDefault, res, false);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            if (res)
            {
            old_targets.insert(std::make_pair(si->getDefaultDest(), isDefault));
            }
        }
        //combine possible branches stored in old_targets and new_targets
        std::vector< ref<Expr> > new_conditions;
        for (std::map<BasicBlock*, ref<Expr> >::iterator it =
             new_targets.begin(), ie = new_targets.end();
               it != ie; ++it)
            new_conditions.push_back(it->second);

        std::vector< ref<Expr> > old_conditions;
        for (std::map<BasicBlock*, ref<Expr> >::iterator it =
             old_targets.begin(), ie = new_targets.end();
               it != ie; ++it)
            old_conditions.push_back(it->second);
        //control divergence detection

        //first fork on new version
        std::vector<ExecutionState*> new_branches;
        branch(state, new_conditions, new_branches);
        std::vector<ExecutionState*>::iterator bit = new_branches.begin();
        for (std::map<BasicBlock*, ref<Expr> >::iterator it =
               new_targets.begin(), ie = new_targets.end();
             it != ie; ++it) {
            ExecutionState *es = *bit;
            if (es)
            {
            //second fork on old version
            std::vector<ExecutionState*> old_branches;
            branch(*es, old_conditions, old_branches);

            std::vector<ExecutionState*>::iterator obit = old_branches.begin();
            for (std::map<BasicBlock*, ref<Expr> >::iterator oit =
                   old_targets.begin(), oie = old_targets.end();
                 oit != oie; ++oit) {
                ExecutionState *oes = *obit;
                if (oes)
                {
                if(it->first==oit->first)//same control flow
                {
                    transferToBasicBlock(it->first, si->getParent(), *oes);
                }
                else//divergent control flow
                {
                    //process test case
                    oes->needTestCase=true;
                    std::string MsgString;
                    llvm::raw_string_ostream msg(MsgString);
                    msg << "Control Divergence in Switch\n";
                    if (ki->info->file !="") {
                          msg << "File: " << ki->info->file << "\n";
                          msg << "Line: " << ki->info->line << "\n";
                          msg << "assembly.ll line: " << ki->info->assemblyLine << "\n";
                    }
                    msg << "Stack: \n";
		    state.dumpStack(msg);
                    oes->divmsg=msg.str();
                    interpreterHandler->processTestCase(*oes,0,0);
                    oes->needTestCase=false;

                    BasicBlock *leftbb=oit->first;//old basicblock
                    BasicBlock *rightbb=it->first;//new basicblock
                    bool optiMG=computeMerge(*oes, rightbb, leftbb);
                    if(optiMG)
                    {
                        oes->constraints.pop_back();
                        oes->constraints.pop_back();
                        //create origin pair for each merge point
                        for(std::map<BasicBlock*, bool>::iterator mit=oes->mergeSet.begin(), mie=oes->mergeSet.end();mit!=mie;mit++)
                        {
                            //record
                            //old state
                            ExecutionState *old_state=oes->branch();
                            ExecutionState *new_state=old_state->branch();
                            std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(oes);
                            if(siit!=seedMap.end()){
                                std::vector<SeedInfo> seeds = siit->second;
                                seedMap[old_state]=seeds;
                                seedMap[new_state]=seeds;
                            }
                            addedStates.insert(old_state);
                            oes->ptreeNode->data=0;
                            std::pair< PTree::Node*, PTree::Node* > res=processTree->split(oes->ptreeNode, old_state, oes);
                            old_state->ptreeNode=res.first;
                            oes->ptreeNode=res.second;
                            old_state->ptreeNode->data=0;
                            res=processTree->split(old_state->ptreeNode, new_state, old_state);
                            new_state->ptreeNode=res.first;
                            old_state->ptreeNode=res.second;
                            addConstraint(*old_state, oit->second);
                            addConstraint(*new_state, it->second);                            //record
                            old_state->splitfunc=i->getParent()->getParent()->getName().str();
                            old_state->splitframe=old_state->stack.size();
                            old_state->mergePoint=mit->first;
                            old_state->intoSPEO();
                            old_state->splitStatus=false;
                            transferToBasicBlock(leftbb,si->getParent(),*old_state);
                            new_state->splitfunc=i->getParent()->getParent()->getName().str();
                            new_state->splitframe=new_state->stack.size();
                            new_state->mergePoint=mit->first;
                            new_state->intoSPEN();
                            new_state->splitStatus=false;
                            transferToBasicBlock(rightbb,si->getParent(),*new_state);
                            old_state->splitStates.push_back(new_state);
                            new_state->splitStates.push_back(old_state);
                        }
                        removedStates.insert(oes);
                    }
                    else
                    {

                        oes->constraints.pop_back();
                        oes->constraints.pop_back();
                        //record
                        //old state
                        ExecutionState *old_state=oes;
                        //new state
                        ExecutionState *new_state=old_state->branch();
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator siit = seedMap.find(oes);
                        if(siit!=seedMap.end()){
                            std::vector<SeedInfo> seeds = siit->second;
                            seedMap[old_state]=seeds;
                            seedMap[new_state]=seeds;
                        }
                        old_state->ptreeNode->data=0;
                        std::pair< PTree::Node*, PTree::Node* > res=processTree->split(old_state->ptreeNode, new_state, old_state);
                        new_state->ptreeNode=res.first;
                        old_state->ptreeNode=res.second;
                        addConstraint(*old_state, oit->second);
                        addConstraint(*new_state, it->second);
                        //record
                        old_state->splitfunc=i->getParent()->getParent()->getName().str();
                        old_state->splitframe=old_state->stack.size();
                        old_state->mergePoint=old_state->retPoint;
                        old_state->intoSPEO();
                        old_state->splitStatus=false;
                        transferToBasicBlock(leftbb,si->getParent(),*old_state);
                        new_state->splitfunc=i->getParent()->getParent()->getName().str();
                        new_state->splitframe=new_state->stack.size();
                        new_state->mergePoint=new_state->retPoint;
                        new_state->intoSPEN();
                        new_state->splitStatus=false;
                        transferToBasicBlock(rightbb,si->getParent(),*new_state);
                        old_state->splitStates.push_back(new_state);
                        new_state->splitStates.push_back(old_state);
                    }
                }
                }
                obit++;
            }
            }
            bit++;
        }
    }
    else
    {
        if(cond->isContainShadow())
        {
            if(state.isSPEO())
                cond=cond->findShadowExpr(0);
            else if(state.isSPEN())
                cond=cond->findShadowExpr(1);
        }
        if(BuptShadow)
            ocond=cond;
            cond = toUnique(state, cond);
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
          // Somewhat gross to create these all the time, but fine till we
          // switch to an internal rep.
          LLVM_TYPE_Q llvm::IntegerType *Ty =
        cast<IntegerType>(si->getCondition()->getType());
          ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
          unsigned index = si->findCaseValue(ci).getSuccessorIndex();
    #else
          unsigned index = si->findCaseValue(ci);
    #endif
        if(index)
            addConstraint(state, EqExpr::create(ocond, cond));
        else
        {
              ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
              for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
               i != e; ++i) {
            ref<Expr> value = evalConstant(i.getCaseValue());
    #else
              for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
            ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif
            ref<Expr> match = EqExpr::create(ocond, value);
            isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
              }
            addConstraint(state, isDefault);
        }
          transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
        } else {
          std::map<BasicBlock*, ref<Expr> > targets;
          ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
          for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
           i != e; ++i) {
        ref<Expr> value = evalConstant(i.getCaseValue());
    #else
          for (unsigned i=1, cases = si->getNumCases(); i<cases; ++i) {
        ref<Expr> value = evalConstant(si->getCaseValue(i));
    #endif
        ref<Expr> match = EqExpr::create(cond, value);
        isDefault = AndExpr::create(isDefault, Expr::createIsZero(match));
        bool result;
        bool success = solver->mayBeTrue(state, match, result);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (result) {
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
          BasicBlock *caseSuccessor = i.getCaseSuccessor();
    #else
          BasicBlock *caseSuccessor = si->getSuccessor(i);
    #endif
          std::map<BasicBlock*, ref<Expr> >::iterator it =
            targets.insert(std::make_pair(caseSuccessor,
                   ConstantExpr::alloc(0, Expr::Bool))).first;

          it->second = OrExpr::create(match, it->second);
        }
          }
          bool res;
          bool success = solver->mayBeTrue(state, isDefault, res);
          assert(success && "FIXME: Unhandled solver failure");
          (void) success;
          if (res)
        targets.insert(std::make_pair(si->getDefaultDest(), isDefault));

          std::vector< ref<Expr> > conditions;
          for (std::map<BasicBlock*, ref<Expr> >::iterator it =
             targets.begin(), ie = targets.end();
           it != ie; ++it)
        conditions.push_back(it->second);

          std::vector<ExecutionState*> branches;
          branch(state, conditions, branches);

          std::vector<ExecutionState*>::iterator bit = branches.begin();
          for (std::map<BasicBlock*, ref<Expr> >::iterator it =
             targets.begin(), ie = targets.end();
           it != ie; ++it) {
        ExecutionState *es = *bit;
        if (es)
        {
            //bupt use
          addConstraint(*es, it->second);
          transferToBasicBlock(it->first, bb, *es);
        }
        ++bit;
          }
        }
    }
    break;
 }
  case Instruction::Unreachable:
    // Note that this is not necessarily an internal bug, llvm will
    // generate unreachable instructions in cases where it knows the
    // program will crash. So it is effectively a SEGV or internal
    // error.
    terminateStateOnExecError(state, "reached \"unreachable\" instruction");
    break;

  case Instruction::Invoke:
  case Instruction::Call: {
    CallSite cs(i);

    unsigned numArgs = cs.arg_size();
    Value *fp = cs.getCalledValue();
    Function *f = getTargetFunction(fp, state);



    // Skip debug intrinsics, we can't evaluate their metadata arguments.
    if (f && isDebugIntrinsic(f, kmodule))
      break;

    if (isa<InlineAsm>(fp)) {
      terminateStateOnExecError(state, "inline assembly is unsupported");
      break;
    }
    // evaluate arguments
    std::vector< ref<Expr> > arguments;
    arguments.reserve(numArgs);

    for (unsigned j=0; j<numArgs; ++j)
      arguments.push_back(eval(ki, j+1, state).value);

    if (f) {
      const FunctionType *fType =
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
      const FunctionType *fpType =
        dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());

      // special case the call with a bitcast case
      if (fType != fpType) {
        assert(fType && fpType && "unable to get function type");

        // XXX check result coercion

        // XXX this really needs thought and validation
        unsigned i=0;
        for (std::vector< ref<Expr> >::iterator
               ai = arguments.begin(), ie = arguments.end();
             ai != ie; ++ai) {
          Expr::Width to, from = (*ai)->getWidth();

          if (i<fType->getNumParams()) {
            to = getWidthForLLVMType(fType->getParamType(i));

            if (from != to) {
              // XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
              bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
          bool isSExt = cs.paramHasAttr(i+1, llvm::Attributes::SExt);
#else
          bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
#endif
              if (isSExt) {
                arguments[i] = SExtExpr::create(arguments[i], to);
              } else {
                arguments[i] = ZExtExpr::create(arguments[i], to);
              }
            }
          }

          i++;
        }
      }
    //butp use
    unsigned idx=0;
    if(debug_call==1)
        klee_message("function %s arguments:",f->getName().data());
    for(std::vector<ref<Expr> >::iterator ai=arguments.begin(),ae=arguments.end();ai!=ae;++ai)
    {
        if(idx<f->arg_size() && fType->getParamType(idx)->isPointerTy())
            arguments[idx]->setIsPointer();
        if(debug_call==1){
            arguments[idx]->dump();
        }
        idx++;
    }
    if(debug_func==1){
        errs() << " Function "<<f->getName() << " arguments: \n";
        unsigned aiIdx=0;
        for(std::vector<ref<Expr> >::iterator ai=arguments.begin(),ae=arguments.end();ai!=ae;++ai,aiIdx++)
        {
            errs()<<"argument["<<aiIdx<<"]:\n"
                << (*ai)<<"\n";
            if(isX86_64 && (*ai)->getWidth() != Expr::Int64 ){
                continue;
            } else if((*ai)->getWidth() != Expr::Int32){
                continue;
            }
            if((*ai)->isPointer()){
                ObjectPair op;
                bool resolve_success;
                bool result=state.addressSpace.resolveOne(state, solver, *ai, op, resolve_success);
                if(result){
                    errs()<<"resolveOne succ\n";
                    if(resolve_success){
                        errs()<<"find mo in address "<<op.first->address<<"\n";
                    } else {
                        errs()<<"find mo failed\n";
                    }
                } else {
                    errs()<<"resolveOne succ\n";
                }
            } else {
                errs()<<"is not Pointer\n";
            }
        }
    }
    if(f->getName().str()=="exit" && arguments.size()>0)
    {
        if(state.isUE())
        {
            //this version KLEE does not check and return exit code
            //check for data divergence
/*            if(arguments[0]->isContainShadow())
            {
                ref<Expr> old_exit=arguments[0]->findShadowExpr(0);
                ref<Expr> new_exit=arguments[0]->findShadowExpr(1);
                ConstantExpr *oldreturnCode=dyn_cast<ConstantExpr>(old_exit);
                ConstantExpr *newreturnCode=dyn_cast<ConstantExpr>(new_exit);
                if(oldreturnCode && newreturnCode){
                    programExitCode=(int32_t)newreturnCode->getZExtValue();
                    if(newreturnCode->compareContents(*old_exit)!=0)
                    {
                           state.needTestCase=true;
                           state.ctlordata=true;
                            if(old_exit->isCtrlAffected()||new_exit->isCtrlAffected())
                            state.ctlAffected=true;
                    }
                }
            }
*/
        }
        //bupt use
        else if(state.isSPEO())
        {    //old state meets exit call
            state.tmode=ExecutionState::exitcall;
            state.splitStatus=true;
            break;
        }
        else if(state.isSPEN())
        {
            state.tmode=ExecutionState::exitcall;
            /*
            ExecutionState *old_state=*(state.splitStates.begin());
            if(old_state->tmode==ExecutionState::err)
            {
                state.needTestCase=true;
                //create test case using constraint from both two states
                //interpreterHandler->processTestCase(state, state.errmsg.c_str(), "fixed.err");
                state.needTestCase=false;
                terminateState(state);
                break;
            }
            else if(state.tmode==ExecutionState::normal)
            {
                //?
            }
            else if(state.tmode==ExecutionState::exitcall)
            {
                //whether to check exit code
            }
            */
            break;
        }
    }
    //bupt use
    if("klee_change"==f->getName().str())
    {
        state.markHasChanged();
        if(arguments[0]->isContainShadow())
            arguments[0]=arguments[0]->findShadowExpr(0);
        if(arguments[1]->isContainShadow())
            arguments[1]=arguments[1]->findShadowExpr(1);
        ref<Expr> result=ShadowExpr::create(arguments[0],arguments[1]);
        bindLocal(ki,state,result);
        break;
    }
      executeCall(state, ki, f, arguments);
    } else {
      ref<Expr> v = eval(ki, 0, state).value;

      ExecutionState *free = &state;
      bool hasInvalid = false, first = true;

      /* XXX This is wasteful, no need to do a full evaluate since we
         have already got a value. But in the end the caches should
         handle it for us, albeit with some overhead. */
    //bupt use
    if(state.isUE() && v->isContainShadow())
    {
          ref<Expr> vold= v->findShadowExpr(0);
          ref<Expr> vnew= v->findShadowExpr(1);
          StatePair ctl = fork(state, EqExpr::create(vold, vnew), false);
          if(ctl.first)
          {
                v=vold;
                free=ctl.first;
                do {
                ref<ConstantExpr> value;
                bool success = solver->getValue(*free, v, value,false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                StatePair res = fork(*free, EqExpr::create(v, value), true);
                if (res.first) {
                  uint64_t addr = value->getZExtValue();
                  if (legalFunctions.count(addr)) {
                    f = (Function*) addr;

                    // Don't give warning on unique resolution
                    if (res.second || !first)
                      klee_warning_once((void*) (unsigned long) addr,
                            "resolved symbolic function pointer to: %s",
                            f->getName().data());

                    executeCall(*res.first, ki, f, arguments);
                  } else {
                    if (!hasInvalid) {
                      terminateStateOnExecError(state, "invalid function pointer");
                      hasInvalid = true;
                    }
                  }
                }

                first = false;
                free = res.second;
                  } while (free);
          }
          if(ctl.second)//control flow divergence
          {
            //bupt use
            //control divergence
            //no different branches. how?
          }

    }
    else
    {
        if(state.isSPEO())
            v=v->findShadowExpr(0);
        else if(state.isSPEN())
            v=v->findShadowExpr(1);
          do {
        ref<ConstantExpr> value;
        bool success;
        if(BuptShadow)
            success = solver->getValue(*free, v, value,free->hasChangedBefore());
        else
            success = solver->getValue(*free, v, value);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        StatePair res = fork(*free, EqExpr::create(v, value), true);
        if (res.first) {
          uint64_t addr = value->getZExtValue();
          if (legalFunctions.count(addr)) {
            f = (Function*) addr;

            // Don't give warning on unique resolution
            if (res.second || !first)
              klee_warning_once((void*) (unsigned long) addr,
                    "resolved symbolic function pointer to: %s",
                    f->getName().data());

            executeCall(*res.first, ki, f, arguments);
          } else {
            if (!hasInvalid) {
              terminateStateOnExecError(state, "invalid function pointer");
              hasInvalid = true;
            }
          }
        }

        first = false;
        free = res.second;
          } while (free);
    }
    }
    break;
  }
  case Instruction::PHI: {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
    ref<Expr> result = eval(ki, state.incomingBBIndex, state).value;
#else
    ref<Expr> result = eval(ki, state.incomingBBIndex * 2, state).value;
#endif
    if(ki->inst->getType()->isPointerTy())
        result->setIsPointer();
    bindLocal(ki, state, result);
    break;
  }

    // Special instructions
  case Instruction::Select: {
    ref<Expr> cond = eval(ki, 0, state).value;
    ref<Expr> tExpr = eval(ki, 1, state).value;
    ref<Expr> fExpr = eval(ki, 2, state).value;
    ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::VAArg:
    terminateStateOnExecError(state, "unexpected VAArg instruction");
    break;

    // Arithmetic / logical

  case Instruction::Add: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, AddExpr::create(left, right));
    break;
  }

  case Instruction::Sub: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, SubExpr::create(left, right));
    break;
  }

  case Instruction::Mul: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, MulExpr::create(left, right));
    break;
  }

  case Instruction::UDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = UDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::URem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = URemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SRem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SRemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::And: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AndExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Or: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = OrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Xor: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = XorExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Shl: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = ShlExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::LShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = LShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::AShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

    // Compare

  case Instruction::ICmp: {
    CmpInst *ci = cast<CmpInst>(i);
    ICmpInst *ii = cast<ICmpInst>(ci);

    switch(ii->getPredicate()) {
    case ICmpInst::ICMP_EQ: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = EqExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_NE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = NeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_UGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgtExpr::create(left, right);
      bindLocal(ki, state,result);
      break;
    }

    case ICmpInst::ICMP_UGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgtExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    default:
      terminateStateOnExecError(state, "invalid ICmp predicate");
    }
    break;
  }

    // Memory instructions...
  case Instruction::Alloca: {
    AllocaInst *ai = cast<AllocaInst>(i);
    unsigned elementSize =
      kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
    ref<Expr> size = Expr::createPointer(elementSize);
    if (ai->isArrayAllocation()) {
      ref<Expr> count = eval(ki, 0, state).value;
      count = Expr::createZExtToPointerWidth(count);
      size = MulExpr::create(size, count);
    }
    bool isLocal = i->getOpcode()==Instruction::Alloca;
    executeAlloc(state, size, isLocal, ki);
    break;
  }

  case Instruction::Load: {
    ref<Expr> base = eval(ki, 0, state).value;
    executeMemoryOperation(state, false, base, 0, ki);
    break;
  }
  case Instruction::Store: {
    ref<Expr> base = eval(ki, 1, state).value;
    ref<Expr> value = eval(ki, 0, state).value;
    //bupt use
    const llvm::Type *val_type=i->getOperand(0)->getType();
    if(!value.isNull() && val_type->isPointerTy())
        value->setIsPointer();
    executeMemoryOperation(state, true, base, value, 0);
    break;
  }

  case Instruction::GetElementPtr: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
    ref<Expr> base = eval(ki, 0, state).value;

    for (std::vector< std::pair<unsigned, uint64_t> >::iterator
           it = kgepi->indices.begin(), ie = kgepi->indices.end();
         it != ie; ++it) {
      uint64_t elementSize = it->second;
      ref<Expr> index = eval(ki, it->first, state).value;
      base = AddExpr::create(base,
                             MulExpr::create(Expr::createSExtToPointerWidth(index),
                                             Expr::createPointer(elementSize)));
    }
    if (kgepi->offset)
      base = AddExpr::create(base,
                             Expr::createPointer(kgepi->offset));
    base->setIsPointer();
    bindLocal(ki, state, base);
    break;
  }

    // Conversion
  case Instruction::Trunc: {
    CastInst *ci = cast<CastInst>(i);
    if(debug==1){
        errs()<<eval(ki, 0, state).value<<"\n";
    }
    ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value,
                                           0,
                                           getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ZExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::SExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::IntToPtr: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width pType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    //bupt use
    ref<Expr> result=ZExtExpr::create(arg, pType);
    result->setIsPointer();
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::PtrToInt: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width iType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    ref<Expr> result=ZExtExpr::create(arg, iType);
    result->setIsNotPointer();
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::BitCast: {
    ref<Expr> value = eval(ki, 0, state).value;
    ref<Expr> result = value ;
    if(value->isPointer())
    result->setIsPointer();
    else
    result->setIsNotPointer();
    bindLocal(ki, state, result);
    break;
  }

    // Floating point instructions

  case Instruction::FAdd: {
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {

        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FAdd operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FAdd operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FAdd operation in new");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_left->getWidth()), old_left->getAPValue());
        old_Res.add(APFloat(*fpWidthToSemantics(old_right->getWidth()),old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(*fpWidthToSemantics(new_left->getWidth()), new_left->getAPValue());
        new_Res.add(APFloat(*fpWidthToSemantics(new_right->getWidth()),new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat old_Res(old_left->getAPValue());
        old_Res.add(APFloat(old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(new_left->getAPValue());
        new_Res.add(APFloat(new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif

        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res.bitcastToAPInt()),ConstantExpr::alloc(new_Res.bitcastToAPInt()));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FAdd operation");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
        Res.add(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat Res(left->getAPValue());
        Res.add(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    }
    break;
  }

  case Instruction::FSub: {
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FSub operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FSub operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FSub operation in new");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_left->getWidth()), old_left->getAPValue());
        old_Res.subtract(APFloat(*fpWidthToSemantics(old_right->getWidth()), old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(*fpWidthToSemantics(new_left->getWidth()), new_left->getAPValue());
        new_Res.subtract(APFloat(*fpWidthToSemantics(new_right->getWidth()), new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat old_Res(old_left->getAPValue());
        old_Res.subtract(APFloat(old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(new_left->getAPValue());
        new_Res.subtract(APFloat(new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res.bitcastToAPInt()),ConstantExpr::alloc(new_Res.bitcastToAPInt()));
        bindLocal(ki, state, result);

    }
    else
    {

        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FSub operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
        Res.subtract(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat Res(left->getAPValue());
        Res.subtract(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    }
    break;
  }

  case Instruction::FMul: {
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FMul operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in new");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_left->getWidth()), old_left->getAPValue());
        old_Res.multiply(APFloat(*fpWidthToSemantics(old_right->getWidth()), old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(*fpWidthToSemantics(new_left->getWidth()), new_left->getAPValue());
        new_Res.multiply(APFloat(*fpWidthToSemantics(new_right->getWidth()), new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat old_Res(old_left->getAPValue());
        old_Res.multiply(APFloat(old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(new_left->getAPValue());
        new_Res.multiply(APFloat(new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res.bitcastToAPInt()),ConstantExpr::alloc(new_Res.bitcastToAPInt()));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FMul operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
        Res.multiply(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat Res(left->getAPValue());
        Res.multiply(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));

    }
    break;
  }

  case Instruction::FDiv: {
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FMul operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in new");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_left->getWidth()), old_left->getAPValue());
        old_Res.divide(APFloat(*fpWidthToSemantics(old_right->getWidth()), old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(*fpWidthToSemantics(new_left->getWidth()), new_left->getAPValue());
        new_Res.divide(APFloat(*fpWidthToSemantics(new_right->getWidth()), new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat old_Res(old_left->getAPValue());
        old_Res.divide(APFloat(old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(new_left->getAPValue());
        new_Res.divide(APFloat(new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res.bitcastToAPInt()),ConstantExpr::alloc(new_Res.bitcastToAPInt()));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FDiv operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
        Res.divide(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat Res(left->getAPValue());
        Res.divide(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    }
    break;
  }

  case Instruction::FRem: {
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FMul operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in new");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_left->getWidth()), old_left->getAPValue());
        old_Res.mod(APFloat(*fpWidthToSemantics(old_right->getWidth()), old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(*fpWidthToSemantics(new_left->getWidth()), new_left->getAPValue());
        new_Res.mod(APFloat(*fpWidthToSemantics(new_right->getWidth()), new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat old_Res(old_left->getAPValue());
        old_Res.mod(APFloat(old_right->getAPValue()), APFloat::rmNearestTiesToEven);
        llvm::APFloat new_Res(new_left->getAPValue());
        new_Res.mod(APFloat(new_right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res.bitcastToAPInt()),ConstantExpr::alloc(new_Res.bitcastToAPInt()));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FRem operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
        Res.mod(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()),
            APFloat::rmNearestTiesToEven);
    #else
        llvm::APFloat Res(left->getAPValue());
        Res.mod(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
    #endif
        bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    }
    break;
  }

  case Instruction::FPTrunc: {
    FPTruncInst *fi = cast<FPTruncInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_arg->getWidth()) || resultType > old_arg->getWidth()){
            if (!fpWidthToSemantics(new_arg->getWidth()) || resultType > new_arg->getWidth()){
            return terminateStateOnExecError(state, "Unsupported FPTrunc operation in both");
            } else {
            return terminateStateOnExecError(state, "Unsupported FPTrunc operation in new");
            }
        } else {
            return terminateStateOnExecError(state, "Unsupported FPTrunc operation in old");
        }

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_arg->getWidth()), old_arg->getAPValue());
    #else
        llvm::APFloat old_Res(old_arg->getAPValue());
    #endif
        bool old_losesInfo = false;
        old_Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &old_losesInfo);

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat new_Res(*fpWidthToSemantics(new_arg->getWidth()), new_arg->getAPValue());
    #else
        llvm::APFloat new_Res(new_arg->getAPValue());
    #endif
        bool new_losesInfo = false;
        new_Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &new_losesInfo);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res),ConstantExpr::alloc(new_Res));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
          return terminateStateOnExecError(state, "Unsupported FPTrunc operation");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    #else
        llvm::APFloat Res(arg->getAPValue());
    #endif
        bool losesInfo = false;
        Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &losesInfo);
        bindLocal(ki, state, ConstantExpr::alloc(Res));

    }
    break;
  }

  case Instruction::FPExt: {
    FPExtInst *fi = cast<FPExtInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());

    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_arg->getWidth()) || resultType > old_arg->getWidth()){
            if (!fpWidthToSemantics(new_arg->getWidth()) || resultType > new_arg->getWidth()){
            return terminateStateOnExecError(state, "Unsupported FPExt operation in both");
            } else {
            return terminateStateOnExecError(state, "Unsupported FPExt operation in new");
            }
        } else {
            return terminateStateOnExecError(state, "Unsupported FPExt operation in old");
        }
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Res(*fpWidthToSemantics(old_arg->getWidth()), old_arg->getAPValue());
    #else
        llvm::APFloat old_Res(old_arg->getAPValue());
    #endif
        bool old_losesInfo = false;
        old_Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &old_losesInfo);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat new_Res(*fpWidthToSemantics(new_arg->getWidth()), new_arg->getAPValue());
    #else
        llvm::APFloat new_Res(new_arg->getAPValue());
    #endif
        bool new_losesInfo = false;
        new_Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &new_losesInfo);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Res),ConstantExpr::alloc(new_Res));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
          return terminateStateOnExecError(state, "Unsupported FPExt operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    #else
        llvm::APFloat Res(arg->getAPValue());
    #endif
        bool losesInfo = false;
        Res.convert(*fpWidthToSemantics(resultType),
            llvm::APFloat::rmNearestTiesToEven,
            &losesInfo);
        bindLocal(ki, state, ConstantExpr::alloc(Res));
    }
    break;
  }

  case Instruction::FPToUI: {
    FPToUIInst *fi = cast<FPToUIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_arg->getWidth()) || resultType > 64){
            if (!fpWidthToSemantics(new_arg->getWidth()) || resultType > 64){
            return terminateStateOnExecError(state, "Unsupported FPToUI operation in both");
            } else {
            return terminateStateOnExecError(state, "Unsupported FPToUI operation in new");
            }
        } else {
            return terminateStateOnExecError(state, "Unsupported FPToUI operation in old");
        }
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Arg(*fpWidthToSemantics(old_arg->getWidth()), old_arg->getAPValue());
    #else
        llvm::APFloat old_Arg(old_arg->getAPValue());
    #endif
        uint64_t old_value = 0;
        bool old_isExact = true;
        old_Arg.convertToInteger(&old_value, resultType, false,
                 llvm::APFloat::rmTowardZero, &old_isExact);


    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat new_Arg(*fpWidthToSemantics(new_arg->getWidth()), new_arg->getAPValue());
    #else
        llvm::APFloat new_Arg(new_arg->getAPValue());
    #endif
        uint64_t new_value = 0;
        bool new_isExact = true;
        new_Arg.convertToInteger(&new_value, resultType, false,
                 llvm::APFloat::rmTowardZero, &new_isExact);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_value, resultType),ConstantExpr::alloc(new_value, resultType));
        bindLocal(ki, state, result);

    }
    else
    {
        if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
          return terminateStateOnExecError(state, "Unsupported FPToUI operation");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    #else
        llvm::APFloat Arg(arg->getAPValue());
    #endif
        uint64_t value = 0;
        bool isExact = true;
        Arg.convertToInteger(&value, resultType, false,
                 llvm::APFloat::rmTowardZero, &isExact);
        bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    }
    break;
  }

  case Instruction::FPToSI: {
    FPToSIInst *fi = cast<FPToSIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());

    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_arg->getWidth()) || resultType > 64){
            if (!fpWidthToSemantics(new_arg->getWidth()) || resultType > 64){
            return terminateStateOnExecError(state, "Unsupported FPToSI operation in both");
            } else {
            return terminateStateOnExecError(state, "Unsupported FPToSI operation in new");
            }
        } else {
            return terminateStateOnExecError(state, "Unsupported FPToSI operation in old");
        }
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat old_Arg(*fpWidthToSemantics(old_arg->getWidth()), old_arg->getAPValue());
    #else
        llvm::APFloat old_Arg(old_arg->getAPValue());

    #endif
        uint64_t old_value = 0;
        bool old_isExact = true;
        old_Arg.convertToInteger(&old_value, resultType, true,
                 llvm::APFloat::rmTowardZero, &old_isExact);
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat new_Arg(*fpWidthToSemantics(new_arg->getWidth()), new_arg->getAPValue());
    #else
        llvm::APFloat new_Arg(new_arg->getAPValue());

    #endif
        uint64_t new_value = 0;
        bool new_isExact = true;
        new_Arg.convertToInteger(&new_value, resultType, true,
                 llvm::APFloat::rmTowardZero, &new_isExact);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_value, resultType),ConstantExpr::alloc(new_value, resultType));
        bindLocal(ki, state, result);

    }

    else
    {
        if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
          return terminateStateOnExecError(state, "Unsupported FPToSI operation");
    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    #else
        llvm::APFloat Arg(arg->getAPValue());

    #endif
        uint64_t value = 0;
        bool isExact = true;
        Arg.convertToInteger(&value, resultType, true,
                 llvm::APFloat::rmTowardZero, &isExact);
        bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    }
    break;
  }

  case Instruction::UIToFP: {
    UIToFPInst *fi = cast<UIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported UIToFP operation");

    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if(state.isUE() && shadowflag)
    {
        llvm::APFloat old_f(*semantics, 0);
        old_f.convertFromAPInt(old_arg->getAPValue(), false,
                   llvm::APFloat::rmNearestTiesToEven);
        llvm::APFloat new_f(*semantics, 0);
        new_f.convertFromAPInt(new_arg->getAPValue(), false,
                   llvm::APFloat::rmNearestTiesToEven);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_f),ConstantExpr::alloc(new_f));
        bindLocal(ki, state, result);

    }

    else
    {
        llvm::APFloat f(*semantics, 0);
        f.convertFromAPInt(arg->getAPValue(), false,
                   llvm::APFloat::rmNearestTiesToEven);

        bindLocal(ki, state, ConstantExpr::alloc(f));
    }
    break;
  }

  case Instruction::SIToFP: {
    SIToFPInst *fi = cast<SIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported SIToFP operation");

    //bupt use
    ref<Expr> arg_value=eval(ki,0,state).value;
    ref<ConstantExpr> old_arg,new_arg,arg;
    bool shadowflag=false;
    if(arg_value->isContainShadow())
    {
        if(state.isSPEO())
            arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_arg=toConstant(state, arg_value->findShadowExpr(0), "floating point");
            new_arg=toConstant(state, arg_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    } else {
        arg=toConstant(state, arg_value, "floating point");
    }
    if( state.isUE() && shadowflag)
    {
        llvm::APFloat old_f(*semantics, 0);
        old_f.convertFromAPInt(old_arg->getAPValue(), true,
                   llvm::APFloat::rmNearestTiesToEven);
        llvm::APFloat new_f(*semantics, 0);
        new_f.convertFromAPInt(new_arg->getAPValue(), true,
                   llvm::APFloat::rmNearestTiesToEven);
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_f),ConstantExpr::alloc(new_f));
        bindLocal(ki, state, result);

    }
    else
    {
        llvm::APFloat f(*semantics, 0);
        f.convertFromAPInt(arg->getAPValue(), true,
                   llvm::APFloat::rmNearestTiesToEven);

        bindLocal(ki, state, ConstantExpr::alloc(f));
    }
    break;
  }

  case Instruction::FCmp: {
    FCmpInst *fi = cast<FCmpInst>(i);
    ref<Expr> left_value= eval(ki, 0, state).value;
    ref<Expr> right_value= eval(ki, 1, state).value;
    //bupt use
    bool shadowflag=false;
    ref<ConstantExpr> old_left, old_right, new_left, new_right, left, right;
    if(left_value->isContainShadow())
    {
        if(state.isSPEO())
                left = toConstant(state,left_value->findShadowExpr(0),"floating point");
        else if(state.isSPEN())
                left = toConstant(state,left_value->findShadowExpr(1),"floating point");
        else if(state.isUE())
        {
                old_left = toConstant(state,left_value->findShadowExpr(0),"floating point");
                new_left = toConstant(state,left_value->findShadowExpr(1),"floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_left= new_left= left= toConstant(state, left_value, "floating point");
    }
    if(right_value->isContainShadow())
    {
        if(state.isSPEO())
            right= toConstant(state, right_value->findShadowExpr(0), "floating point");
        else if(state.isSPEN())
            right= toConstant(state, right_value->findShadowExpr(1), "floating point");
        else if(state.isUE())
        {
            old_right= toConstant(state, right_value->findShadowExpr(0), "floating point");
            new_right= toConstant(state, right_value->findShadowExpr(1), "floating point");
            shadowflag=true;
        }
    }
    else
    {
        old_right= new_right= right= toConstant(state, right_value, "floating point");
    }

    if(state.isUE() && shadowflag)
    {
        if (!fpWidthToSemantics(old_left->getWidth()) ||
            !fpWidthToSemantics(old_right->getWidth())){
            if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in both old and new");
            else
              return terminateStateOnExecError(state, "Unsupported FMul operation in old");
        } else if (!fpWidthToSemantics(new_left->getWidth()) ||
            !fpWidthToSemantics(new_right->getWidth()))
              return terminateStateOnExecError(state, "Unsupported FMul operation in new");
        //old
        #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
            APFloat old_LHS(*fpWidthToSemantics(old_left->getWidth()),old_left->getAPValue());
            APFloat old_RHS(*fpWidthToSemantics(old_right->getWidth()),old_right->getAPValue());
        #else
            APFloat old_LHS(old_left->getAPValue());
            APFloat old_RHS(old_right->getAPValue());
        #endif
            APFloat::cmpResult old_CmpRes = old_LHS.compare(old_RHS);

            bool old_Result = false;
            switch( fi->getPredicate() ) {
              // Predicates which only care about whether or not the operands are NaNs.
            case FCmpInst::FCMP_ORD:
              old_Result = old_CmpRes != APFloat::cmpUnordered;
              break;

            case FCmpInst::FCMP_UNO:
              old_Result = old_CmpRes == APFloat::cmpUnordered;
              break;

              // Ordered comparisons return false if either operand is NaN.  Unordered
              // comparisons return true if either operand is NaN.
            case FCmpInst::FCMP_UEQ:
              if (old_CmpRes == APFloat::cmpUnordered) {
            old_Result = true;
            break;
              }
            case FCmpInst::FCMP_OEQ:
              old_Result = old_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_UGT:
              if (old_CmpRes == APFloat::cmpUnordered) {
            old_Result = true;
            break;
              }
            case FCmpInst::FCMP_OGT:
              old_Result = old_CmpRes == APFloat::cmpGreaterThan;
              break;

            case FCmpInst::FCMP_UGE:
              if (old_CmpRes == APFloat::cmpUnordered) {
            old_Result = true;
            break;
              }
            case FCmpInst::FCMP_OGE:
              old_Result = old_CmpRes == APFloat::cmpGreaterThan || old_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_ULT:
              if (old_CmpRes == APFloat::cmpUnordered) {
            old_Result = true;
            break;
              }
            case FCmpInst::FCMP_OLT:
              old_Result = old_CmpRes == APFloat::cmpLessThan;
              break;

            case FCmpInst::FCMP_ULE:
              if (old_CmpRes == APFloat::cmpUnordered) {
            old_Result = true;
            break;
              }
            case FCmpInst::FCMP_OLE:
              old_Result = old_CmpRes == APFloat::cmpLessThan || old_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_UNE:
              old_Result = old_CmpRes == APFloat::cmpUnordered || old_CmpRes != APFloat::cmpEqual;
              break;
            case FCmpInst::FCMP_ONE:
              old_Result = old_CmpRes != APFloat::cmpUnordered && old_CmpRes != APFloat::cmpEqual;
              break;

            default:
              assert(0 && "Invalid FCMP predicate!");
            case FCmpInst::FCMP_FALSE:
              old_Result = false;
              break;
            case FCmpInst::FCMP_TRUE:
              old_Result = true;
              break;
            }

        //new
        #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
            APFloat new_LHS(*fpWidthToSemantics(new_left->getWidth()),new_left->getAPValue());
            APFloat new_RHS(*fpWidthToSemantics(new_right->getWidth()),new_right->getAPValue());
        #else
            APFloat new_LHS(new_left->getAPValue());
            APFloat new_RHS(new_right->getAPValue());
        #endif
            APFloat::cmpResult new_CmpRes = new_LHS.compare(new_RHS);

            bool new_Result = false;
            switch( fi->getPredicate() ) {
              // Predicates which only care about whether or not the operands are NaNs.
            case FCmpInst::FCMP_ORD:
              new_Result = new_CmpRes != APFloat::cmpUnordered;
              break;

            case FCmpInst::FCMP_UNO:
              new_Result = new_CmpRes == APFloat::cmpUnordered;
              break;

              // Ordered comparisons return false if either operand is NaN.  Unordered
              // comparisons return true if either operand is NaN.
            case FCmpInst::FCMP_UEQ:
              if (new_CmpRes == APFloat::cmpUnordered) {
            new_Result = true;
            break;
              }
            case FCmpInst::FCMP_OEQ:
              new_Result = new_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_UGT:
              if (new_CmpRes == APFloat::cmpUnordered) {
            new_Result = true;
            break;
              }
            case FCmpInst::FCMP_OGT:
              new_Result = new_CmpRes == APFloat::cmpGreaterThan;
              break;

            case FCmpInst::FCMP_UGE:
              if (new_CmpRes == APFloat::cmpUnordered) {
            new_Result = true;
            break;
              }
            case FCmpInst::FCMP_OGE:
              new_Result = new_CmpRes == APFloat::cmpGreaterThan || new_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_ULT:
              if (new_CmpRes == APFloat::cmpUnordered) {
            new_Result = true;
            break;
              }
            case FCmpInst::FCMP_OLT:
              new_Result = new_CmpRes == APFloat::cmpLessThan;
              break;

            case FCmpInst::FCMP_ULE:
              if (new_CmpRes == APFloat::cmpUnordered) {
            new_Result = true;
            break;
              }
            case FCmpInst::FCMP_OLE:
              new_Result = new_CmpRes == APFloat::cmpLessThan || new_CmpRes == APFloat::cmpEqual;
              break;

            case FCmpInst::FCMP_UNE:
              new_Result = new_CmpRes == APFloat::cmpUnordered || new_CmpRes != APFloat::cmpEqual;
              break;
            case FCmpInst::FCMP_ONE:
              new_Result = new_CmpRes != APFloat::cmpUnordered && new_CmpRes != APFloat::cmpEqual;
              break;

            default:
              assert(0 && "Invalid FCMP predicate!");
            case FCmpInst::FCMP_FALSE:
              new_Result = false;
              break;
            case FCmpInst::FCMP_TRUE:
              new_Result = true;
              break;
            }
        ref<Expr> result=ShadowExpr::create(ConstantExpr::alloc(old_Result, Expr::Bool), ConstantExpr::alloc(new_Result, Expr::Bool));
        bindLocal(ki, state, result);
    }
    else
    {
        if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
          return terminateStateOnExecError(state, "Unsupported FCmp operation");

    #if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        APFloat LHS(*fpWidthToSemantics(left->getWidth()),left->getAPValue());
        APFloat RHS(*fpWidthToSemantics(right->getWidth()),right->getAPValue());
    #else
        APFloat LHS(left->getAPValue());
        APFloat RHS(right->getAPValue());
    #endif
        APFloat::cmpResult CmpRes = LHS.compare(RHS);

        bool Result = false;
        switch( fi->getPredicate() ) {
          // Predicates which only care about whether or not the operands are NaNs.
        case FCmpInst::FCMP_ORD:
          Result = CmpRes != APFloat::cmpUnordered;
          break;

        case FCmpInst::FCMP_UNO:
          Result = CmpRes == APFloat::cmpUnordered;
          break;

          // Ordered comparisons return false if either operand is NaN.  Unordered
          // comparisons return true if either operand is NaN.
        case FCmpInst::FCMP_UEQ:
          if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
          }
        case FCmpInst::FCMP_OEQ:
          Result = CmpRes == APFloat::cmpEqual;
          break;

        case FCmpInst::FCMP_UGT:
          if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
          }
        case FCmpInst::FCMP_OGT:
          Result = CmpRes == APFloat::cmpGreaterThan;
          break;

        case FCmpInst::FCMP_UGE:
          if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
          }
        case FCmpInst::FCMP_OGE:
          Result = CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual;
          break;

        case FCmpInst::FCMP_ULT:
          if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
          }
        case FCmpInst::FCMP_OLT:
          Result = CmpRes == APFloat::cmpLessThan;
          break;

        case FCmpInst::FCMP_ULE:
          if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
          }
        case FCmpInst::FCMP_OLE:
          Result = CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual;
          break;

        case FCmpInst::FCMP_UNE:
          Result = CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual;
          break;
        case FCmpInst::FCMP_ONE:
          Result = CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual;
          break;

        default:
          assert(0 && "Invalid FCMP predicate!");
        case FCmpInst::FCMP_FALSE:
          Result = false;
          break;
        case FCmpInst::FCMP_TRUE:
          Result = true;
          break;
        }

        bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
    }
    break;
  }
  case Instruction::InsertValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;
    ref<Expr> val = eval(ki, 1, state).value;

    ref<Expr> l = NULL, r = NULL;
    unsigned lOffset = kgepi->offset*8, rOffset = kgepi->offset*8 + val->getWidth();

    if (lOffset > 0)
      l = ExtractExpr::create(agg, 0, lOffset);
    if (rOffset < agg->getWidth())
      r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

    ref<Expr> result;
    if (!l.isNull() && !r.isNull())
      result = ConcatExpr::create(r, ConcatExpr::create(val, l));
    else if (!l.isNull())
      result = ConcatExpr::create(val, l);
    else if (!r.isNull())
      result = ConcatExpr::create(r, val);
    else
      result = val;

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ExtractValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;

    ref<Expr> result = ExtractExpr::create(agg, kgepi->offset*8, getWidthForLLVMType(i->getType()));

    bindLocal(ki, state, result);
    break;
  }

    // Other instructions...
    // Unhandled
  case Instruction::ExtractElement:
  case Instruction::InsertElement:
  case Instruction::ShuffleVector:
    terminateStateOnError(state, "XXX vector instructions unhandled",
                          "xxx.err");
    break;

  default:
    terminateStateOnExecError(state, "illegal instruction");
    break;
  }
}

void Executor::updateStates(ExecutionState *current) {
    /*
    errs() <<"executor states before update:\n";
      for (std::set<ExecutionState*>::const_iterator it = states.begin(),
              ie = states.end(); it != ie; ++it) {
          errs()<<*it<<"\n";
      }
      */
  if (searcher) {
    searcher->update(current, addedStates, removedStates);
  }
  if(BuptShadow)
  {
      for (std::set<ExecutionState*>::const_iterator it = addedStates.begin(),
       ie = addedStates.end(); it != ie; ++it) {
          ExecutionState *es = *it;
          if(es->isSPEN())
              continue;
          else
              states.insert(es);
      }
  }
  else
  {
      states.insert(addedStates.begin(), addedStates.end());
  }

  addedStates.clear();

  for (std::set<ExecutionState*>::iterator
         it = removedStates.begin(), ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    std::set<ExecutionState*>::iterator it2 = states.find(es);
    //assert(it2!=states.end());
    //XXX check all removedStates.insert(state)
    if(it2!=states.end())
        states.erase(it2);
    std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it3 =
      seedMap.find(es);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    if(it2!=states.end()){
        processTree->remove(es->ptreeNode);
        delete es;
    }
  }
  removedStates.clear();
  /*
    errs() <<"executor states after update:\n";
      for (std::set<ExecutionState*>::const_iterator it = states.begin(),
              ie = states.end(); it != ie; ++it) {
          errs()<<*it<<"\n";
      }
      */
}

template <typename TypeIt>
void Executor::computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie) {
  ref<ConstantExpr> constantOffset =
    ConstantExpr::alloc(0, Context::get().getPointerWidth());
  uint64_t index = 1;
  for (TypeIt ii = ib; ii != ie; ++ii) {
    if (LLVM_TYPE_Q StructType *st = dyn_cast<StructType>(*ii)) {
      const StructLayout *sl = kmodule->targetData->getStructLayout(st);
      const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
      uint64_t addend = sl->getElementOffset((unsigned) ci->getZExtValue());
      constantOffset = constantOffset->Add(ConstantExpr::alloc(addend,
                                                               Context::get().getPointerWidth()));
    } else {
      const SequentialType *set = cast<SequentialType>(*ii);
      uint64_t elementSize =
        kmodule->targetData->getTypeStoreSize(set->getElementType());
      Value *operand = ii.getOperand();
      if (Constant *c = dyn_cast<Constant>(operand)) {
        ref<ConstantExpr> index =
          evalConstant(c)->SExt(Context::get().getPointerWidth());
        ref<ConstantExpr> addend =
          index->Mul(ConstantExpr::alloc(elementSize,
                                         Context::get().getPointerWidth()));
        constantOffset = constantOffset->Add(addend);
      } else {
        kgepi->indices.push_back(std::make_pair(index, elementSize));
      }
    }
    index++;
  }
  kgepi->offset = constantOffset->getZExtValue();
}

void Executor::bindInstructionConstants(KInstruction *KI) {
  KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(KI);

  if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(KI->inst)) {
    computeOffsets(kgepi, gep_type_begin(gepi), gep_type_end(gepi));
  } else if (InsertValueInst *ivi = dyn_cast<InsertValueInst>(KI->inst)) {
    computeOffsets(kgepi, iv_type_begin(ivi), iv_type_end(ivi));
    assert(kgepi->indices.empty() && "InsertValue constant offset expected");
  } else if (ExtractValueInst *evi = dyn_cast<ExtractValueInst>(KI->inst)) {
    computeOffsets(kgepi, ev_type_begin(evi), ev_type_end(evi));
    assert(kgepi->indices.empty() && "ExtractValue constant offset expected");
  }
}

void Executor::bindModuleConstants() {
  for (std::vector<KFunction*>::iterator it = kmodule->functions.begin(),
         ie = kmodule->functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    for (unsigned i=0; i<kf->numInstructions; ++i)
      bindInstructionConstants(kf->instructions[i]);
  }

  kmodule->constantTable = new Cell[kmodule->constants.size()];
  for (unsigned i=0; i<kmodule->constants.size(); ++i) {
    Cell &c = kmodule->constantTable[i];
    c.value = evalConstant(kmodule->constants[i]);
  }
}

void Executor::run(ExecutionState &initialState) {
  bindModuleConstants();

  // Delay init till now so that ticks don't accrue during
  // optimization and such.
  initTimers();

  states.insert(&initialState);
  Expr::Width WordSize = Context::get().getPointerWidth();
  if(WordSize == Expr::Int64)
      isX86_64=true;
  else
      isX86_64=false;

  if (usingSeeds && !BuptShadow) {
    std::vector<SeedInfo> &v = seedMap[&initialState];

    for (std::vector<KTest*>::const_iterator it = usingSeeds->begin(),
           ie = usingSeeds->end(); it != ie; ++it)
      v.push_back(SeedInfo(*it));

    int lastNumSeeds = usingSeeds->size()+10;
    double lastTime, startTime = lastTime = util::getWallTime();
    ExecutionState *lastState = 0;
    while (!seedMap.empty()) {
      if (haltExecution) goto dump;

      std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
        seedMap.upper_bound(lastState);
      if (it == seedMap.end())
        it = seedMap.begin();
      lastState = it->first;
      unsigned numSeeds = it->second.size();
      ExecutionState &state = *lastState;
      KInstruction *ki = state.pc;
      stepInstruction(state);

      executeInstruction(state, ki);
      processTimers(&state, MaxInstructionTime * numSeeds);
      updateStates(&state);

      if ((stats::instructions % 1000) == 0) {
        int numSeeds = 0, numStates = 0;
        for (std::map<ExecutionState*, std::vector<SeedInfo> >::iterator
               it = seedMap.begin(), ie = seedMap.end();
             it != ie; ++it) {
          numSeeds += it->second.size();
          numStates++;
        }
        double time = util::getWallTime();
        if (SeedTime>0. && time > startTime + SeedTime) {
          klee_warning("seed time expired, %d seeds remain over %d states",
                       numSeeds, numStates);
          break;
        } else if (numSeeds<=lastNumSeeds-10 ||
                   time >= lastTime+10) {
          lastTime = time;
          lastNumSeeds = numSeeds;
          klee_message("%d seeds remaining over: %d states",
                       numSeeds, numStates);
        }
      }
    }

    klee_message("seeding done (%d states remain)", (int) states.size());

    // XXX total hack, just because I like non uniform better but want
    // seed results to be equally weighted.
    for (std::set<ExecutionState*>::iterator
           it = states.begin(), ie = states.end();
         it != ie; ++it) {
      (*it)->weight = 1.;
    }

    if (OnlySeed)
      goto dump;
  }
//bupt use
    if(BuptShadow)
    {
        initialState.intoUE();
        searcher = constructUserSearcher(*this);
        searcher->update(0, states, std::set<ExecutionState*>());
        std::vector<SeedInfo> &v=seedMap[&initialState];
        if(usingSeeds)
        {
            for(std::vector<KTest*>::const_iterator it=usingSeeds->begin(), ie=usingSeeds->end();it!=ie;++it)
                v.push_back(SeedInfo(*it));
        }
        else
            v.push_back(SeedInfo(NULL));
        while(!states.empty())
        {
            if(haltExecution)
            {
                klee_message("meet haltExecution\n");
                haltExecution=false;
                goto dump;
            }
            ExecutionState &state=searcher->selectState();
            if(debug==1){
                errs()<<"states'size: "<<states.size()<<"\n";
                errs()<<"selected state: "<<&state<<"\n";
                std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&state);
                if(it!=seedMap.end()){
                    errs()<<"seedMap founded\n";
                }
            }
            if(debug_constraint==1){
                errs() <<"constraints size: "<<state.constraints.size()<<"\n";
                for(ConstraintManager::constraint_iterator pcit=state.constraints.begin(),pcie=state.constraints.end();pcit!=pcie;pcit++){
                    (*pcit)->dump();
                }
            }
            KInstruction *ki=state.pc;
            bool newflag=false;
            bool noMerge=false;
            ExecutionState *new_state=NULL;
            if(state.isSPEO())
            {
                if(state.splitStatus)
                {
                    //select a new version state to execute or merge
                    new_state=state.splitStates.back();
                    if(debug==1){
                        errs()<<"state "<<&state<<" related new_states'size: "<<state.splitStates.size()<<"\n";
                        errs()<<"selected new state: "<<new_state<<"\n";
                    }
                    ki=new_state->pc;
                    BasicBlock *curr_add=ki->inst->getParent();
                    if(new_state->stack.size()==new_state->splitframe && new_state->mergePoint==curr_add)//new state meets merge point
                    {
                        new_state->splitStatus=true;
                        //remove new_state from splitStates
                        state.splitStates.pop_back();
                        //remove new_state,set<SeedInfo> pair from seedMap
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(new_state);
                        if(it!=seedMap.end()){
                            seedMap.erase(it);
                        }
                        if(state.tmode==ExecutionState::err)//old error but new not
                        {
                            if(state.splitStates.empty())//the last new_state
                            {
                                //merge state with new_state
                                if(state.mergeConstraints(*new_state)){
                                    //check its pair's status
                                    std::string shadowsuffix(state.suffix);
                                    klee_message("error occurs only at old version\nold Info: %s",state.errmsg.c_str());
                                    shadowsuffix="fixed."+shadowsuffix;
                                    state.needTestCase=true;
                                    interpreterHandler->processTestCase(state, state.errmsg.c_str(), shadowsuffix.c_str());
                                    state.needTestCase=false;
                                } else {
                                    errs()<<"1. merge state "<<&state<<" "<<new_state<<" constraint conflict!\n";
                                }
                                removedStates.insert(&state);
                                updateStates(&state);
                            } else {
                                // split state, merge constraints and generate test case for err
                                ExecutionState *old_state=state.branch();
                                std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&state);
                                if(it!=seedMap.end()){
                                    std::vector<SeedInfo> seeds = it->second;
                                    seedMap[old_state]=seeds;
                                }
                                addedStates.insert(old_state);
                                state.ptreeNode->data=0;
                                std::pair< PTree::Node*, PTree::Node* > res=processTree->split(state.ptreeNode, old_state, &state);
                                old_state->ptreeNode=res.first;
                                state.ptreeNode=res.second;
                                if(old_state->mergeConstraints(*new_state)){
                                    //check its pair's status
                                    std::string shadowsuffix(old_state->suffix);
                                    klee_message("error occurs only at old version\nold Info: %s",old_state->errmsg.c_str());
                                    shadowsuffix="fixed."+shadowsuffix;
                                    old_state->needTestCase=true;
                                    interpreterHandler->processTestCase(*old_state, old_state->errmsg.c_str(), shadowsuffix.c_str());
                                    old_state->needTestCase=false;
                                    //terminateState(state);
                                } else {
                                    errs()<<"2. merge state "<<old_state<<" "<<new_state<<" constraint conflict!\n";
                                }
                                removedStates.insert(old_state);
                                updateStates(&state);
                            }
                        }
                        else if(state.tmode==ExecutionState::exitcall)//old meets exit call but new meets merge point
                        {
                            if(state.splitStates.empty()){
                                removedStates.insert(&state);
                                updateStates(&state);
                            }//the last new_state
                            else
                                continue;
                        }
                        else if(state.tmode==ExecutionState::normal)
                        {
                            //merge states
                            if(state.splitStates.empty())//the last new_state
                            {
                                //merge state with new_state
                                if(state.USEmerge(*new_state)){
                                    errs()<<"3. merge state "<<&state<<" "<<new_state<<" success merged!\n";
                                    state.intoUE();
                                } else {
                                    errs()<<"3. merge state "<<&state<<" "<<new_state<<" constraint conflict!\n";
                                    removedStates.insert(&state);
                                }
                                updateStates(&state);
                            }
                            else
                            {
                                //copy state and merge it with new_state
                                //ExecutionState *old_state;
                                ExecutionState *old_state=state.branch();
                                std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&state);
                                if(it!=seedMap.end()){
                                    std::vector<SeedInfo> seeds = it->second;
                                    seedMap[old_state]=seeds;
                                }
                                addedStates.insert(old_state);
                                state.ptreeNode->data=0;
                                std::pair< PTree::Node*, PTree::Node* > res=processTree->split(state.ptreeNode, old_state, &state);
                                old_state->ptreeNode=res.first;
                                state.ptreeNode=res.second;
                                //merge old_state with new_state
                                if(old_state->USEmerge(*new_state)){
                                    errs()<<"4. merge state "<<old_state<<" "<<new_state<<" success merged!\n";
                                    old_state->intoUE();
                                    old_state->mergeSet.clear();
                                    old_state->new_pathSequential.clear();
                                } else {
                                    errs()<<"4. merge state "<<old_state<<" "<<new_state<<" constraint conflict!\n";
                                    removedStates.insert(old_state);
                                }
                                //removedStates.insert(new_state);
                                //clear record
                                updateStates(&state);
                            }
                        }
                        continue;
                    }
                    else if(new_state->tmode==ExecutionState::err)//new_state terminated at err point
                    {
                        new_state->splitStatus=true;
                        state.splitStates.pop_back();//remove new_state from splitStates
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(new_state);
                        if(it!=seedMap.end()){
                            seedMap.erase(it);
                        }
                        if(state.splitStates.empty())//the last new_state
                        {
                            //merge state with new_state
                            if(state.mergeConstraints(*new_state)){
                                std::string shadowsuffix(new_state->suffix);
                                if(state.tmode==ExecutionState::err){ // both old and new terminated at err
                                    if(state.errpc==new_state->errpc)//same location
                                    {
                                        klee_message("error occurs at the same locations in two versions\nold Info: %s\nnew Info: %s",state.errmsg.c_str(),new_state->errmsg.c_str());
                                        shadowsuffix="remain."+shadowsuffix;
                                    }
                                    else //different location
                                    {
                                        klee_message("error occurs at the different locations in two versions\nold Info: %s\nnew Info: %s",state.errmsg.c_str(),new_state->errmsg.c_str());
                                        shadowsuffix="newintro."+shadowsuffix;
                                    }
                                    state.needTestCase=true;
                                    interpreterHandler->processTestCase(state, state.errmsg.c_str(), shadowsuffix.c_str());
                                    state.needTestCase=false;
                                } else { // only new terminated at err
                                        klee_message("error occurs only at new version\nnew Info:%s",new_state->errmsg.c_str());
                                        shadowsuffix="newintro."+shadowsuffix;
                                        new_state->needTestCase=true;
                                        interpreterHandler->processTestCase(*new_state, new_state->errmsg.c_str(), shadowsuffix.c_str());
                                        new_state->needTestCase=false;
                                }
                            } else {
                                errs()<<"5. merge state "<<&state<<" "<<new_state<<" constraint conflict!\n";
                            }
                            removedStates.insert(&state); // handled the last new state for this state, remove current state
                            updateStates(&state);
                        } else {
                            // copy state to old_state
                            ExecutionState *old_state=state.branch();
                            std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&state);
                            if(it!=seedMap.end()){
                                std::vector<SeedInfo> seeds = it->second;
                                seedMap[old_state]=seeds;
                            }
                            addedStates.insert(old_state);
                            state.ptreeNode->data=0;
                            std::pair< PTree::Node*, PTree::Node* > res=processTree->split(state.ptreeNode, old_state, &state);
                            old_state->ptreeNode=res.first;
                            state.ptreeNode=res.second;
                            // merge constraints of old_state and new_state to generate test case for err
                            if(old_state->mergeConstraints(*new_state)){
                                std::string shadowsuffix(new_state->suffix);
                                if(old_state->tmode==ExecutionState::err){// both old and new terminated at err point
                                    if(old_state->errpc==new_state->errpc)//same location
                                    {
                                        klee_message("error occurs at the same locations in two versions\nold Info: %s\nnew Info: %s",old_state->errmsg.c_str(),new_state->errmsg.c_str());
                                        shadowsuffix="remain."+shadowsuffix;
                                    }
                                    else //different location
                                    {
                                        klee_message("error occurs at the different locations in two versions\nold Info: %s\nnew Info: %s",new_state->errmsg.c_str(),new_state->errmsg.c_str());
                                        shadowsuffix="newintro."+shadowsuffix;
                                    }
                                    old_state->needTestCase=true;
                                    interpreterHandler->processTestCase(*old_state, old_state->errmsg.c_str(), shadowsuffix.c_str());
                                    old_state->needTestCase=false;
                                } else { // only new terminated at err point
                                        klee_message("error occurs only at new version\nnew Info:%s",new_state->errmsg.c_str());
                                        shadowsuffix="newintro."+shadowsuffix;
                                        new_state->needTestCase=true;
                                        interpreterHandler->processTestCase(*new_state, new_state->errmsg.c_str(), shadowsuffix.c_str());
                                        new_state->needTestCase=false;
                                }
                            } else {
                                errs()<<"6.merge state "<<old_state<<" "<<new_state<<" constraint conflict!\n";
                            }
                            removedStates.insert(old_state);
                            updateStates(&state);
                        }
                        continue;
                    }
                    else if(new_state->tmode==ExecutionState::exitcall)//new meets exit call
                    {
                        new_state->splitStatus=true;
                        state.splitStates.pop_back();//remove new_state from splitStates
                        std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(new_state);
                        if(it!=seedMap.end()){
                            seedMap.erase(it);
                        }
                        if(state.tmode==ExecutionState::err)//old error but new not
                        {
                            //merge constraints and generate test case
                            if(state.splitStates.empty()){ // meet the last new_state
                                if(state.mergeConstraints(*new_state)){
                                    //check its pair's status
                                    std::string shadowsuffix(state.suffix);
                                    klee_message("error occurs only at old version\nold Info: %s",state.errmsg.c_str());
                                    shadowsuffix="fixed."+shadowsuffix;
                                    state.needTestCase=true;
                                    interpreterHandler->processTestCase(state, state.errmsg.c_str(), shadowsuffix.c_str());
                                    state.needTestCase=false;
                                    //terminateState(state);
                                } else {
                                    errs()<<"7.merge state "<<&state<<" "<<new_state<<" constraint conflict!\n";
                                }
                                removedStates.insert(&state);
                                updateStates(&state);
                            } else {
                                // copy state to old_state
                                ExecutionState *old_state=state.branch();
                                std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = seedMap.find(&state);
                                if(it!=seedMap.end()){
                                    std::vector<SeedInfo> seeds = it->second;
                                    seedMap[old_state]=seeds;
                                }
                                addedStates.insert(old_state);
                                state.ptreeNode->data=0;
                                std::pair< PTree::Node*, PTree::Node* > res=processTree->split(state.ptreeNode, old_state, &state);
                                old_state->ptreeNode=res.first;
                                state.ptreeNode=res.second;
                                if(old_state->mergeConstraints(*new_state)){
                                    //check its pair's status
                                    std::string shadowsuffix(old_state->suffix);
                                    klee_message("error occurs only at old version\nold Info: %s",old_state->errmsg.c_str());
                                    shadowsuffix="fixed."+shadowsuffix;
                                    old_state->needTestCase=true;
                                    interpreterHandler->processTestCase(*old_state, old_state->errmsg.c_str(), shadowsuffix.c_str());
                                    old_state->needTestCase=false;
                                } else {
                                    errs()<<"8.merge state "<<old_state<<" "<<new_state<<" constraint conflict!\n";
                                }
                                removedStates.insert(old_state);
                                updateStates(&state);
                            }
                        }
                        else if(state.splitStates.empty()){
                            removedStates.insert(&state);
                            updateStates(&state);
                        }//the last new_state
                        continue;
                    }
                    else
                        //execute the new version  state
                        newflag=true;
                }
                else
                {
                    //check for mergePoint
                    BasicBlock *curr_add=ki->inst->getParent();
                    if(state.mergePoint==curr_add && state.stack.size()==state.splitframe)//meet merge point
                    {
                        state.splitStatus=true;
                        continue;
                    }
                }
            }
            if(newflag)
            {
                ki=new_state->pc;
                if(debug==1){
                    if(new_state->isSPEN()){
                        errs()<<"selected new state: "<<new_state<<"\n";
                    }
                    printFileLine(*new_state, ki);
                    llvm::errs() <<"\n";
                }
                stepInstruction(*new_state);
                executeInstruction(*new_state, ki);
                updateStates(new_state);
            }
            else
            {
                ki=state.pc;
                if(debug==1){
                    if(state.isSPEO()){
                        errs()<<"selected old state: "<<&state<<"\n";
                    } else {
                        errs()<<"selected uni state: "<<&state<<"\n";
                    }
                    printFileLine(state, ki);
                    llvm::errs() <<"\n";
                }
                stepInstruction(state);
                executeInstruction(state, ki);
                updateStates(&state);
            }
        }
        goto dump;
    }
  searcher = constructUserSearcher(*this);

  searcher->update(0, states, std::set<ExecutionState*>());

  while (!states.empty() && !haltExecution) {
    ExecutionState &state = searcher->selectState();
    KInstruction *ki = state.pc;
    stepInstruction(state);

    executeInstruction(state, ki);
    processTimers(&state, MaxInstructionTime);

    if (MaxMemory) {
      if ((stats::instructions & 0xFFFF) == 0) {
        // We need to avoid calling GetMallocUsage() often because it
        // is O(elts on freelist). This is really bad since we start
        // to pummel the freelist once we hit the memory cap.
        unsigned mbs = util::GetTotalMallocUsage() >> 20;
        if (mbs > MaxMemory) {
          if (mbs > MaxMemory + 100) {
            // just guess at how many to kill
            unsigned numStates = states.size();
            unsigned toKill = std::max(1U, numStates - numStates*MaxMemory/mbs);

            klee_warning("killing %d states (over memory cap)", toKill);

            std::vector<ExecutionState*> arr(states.begin(), states.end());
            for (unsigned i=0,N=arr.size(); N && i<toKill; ++i,--N) {
              unsigned idx = rand() % N;

              // Make two pulls to try and not hit a state that
              // covered new code.
              if (arr[idx]->coveredNew)
                idx = rand() % N;

              std::swap(arr[idx], arr[N-1]);
              terminateStateEarly(*arr[N-1], "Memory limit exceeded.");
            }
          }
          atMemoryLimit = true;
        } else {
          atMemoryLimit = false;
        }
      }
    }

    updateStates(&state);
  }

  delete searcher;
  searcher = 0;

 dump:
  if (DumpStatesOnHalt && !states.empty()) {
    llvm::errs() << "KLEE: halting execution, dumping remaining states size: "<<states.size()<<"\n";
    if(!BuptShadow){
        for (std::set<ExecutionState*>::iterator
               it = states.begin(), ie = states.end();
             it != ie; ++it) {
          ExecutionState &state = **it;
          stepInstruction(state); // keep stats rolling
          terminateStateEarly(state, "Execution halting.");
        }
    }
    updateStates(0);
  }
}

std::string Executor::getAddressInfo(ExecutionState &state,
                                     ref<Expr> address) const{
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    example = CE->getZExtValue();
  } else {
    ref<ConstantExpr> value;
    bool success;
    if(BuptShadow)
        success = solver->getValue(state, address, value,!state.hasChangedBefore());
    else
        success = solver->getValue(state, address, value);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair< ref<Expr>, ref<Expr> > res = solver->getRange(state, address);
    if(BuptShadow){
        res = solver->getRange(state, address,!state.hasChangedBefore());
    } else {
        res = solver->getRange(state, address);
    }
    info << "\trange: [" << res.first << ", " << res.second <<"]\n";
  }

  MemoryObject hack((unsigned) example);
  MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower==state.addressSpace.objects.end()) {
    info << "none\n";
  } else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address
         << " of size " << mo->size << "\n"
         << "\t\t" << alloc_info << "\n";
  }
  if (lower!=state.addressSpace.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower==state.addressSpace.objects.end()) {
      info << "none\n";
    } else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address
           << " of size " << mo->size << "\n"
           << "\t\t" << alloc_info << "\n";
    }
  }

  return info.str();
}

void Executor::terminateState(ExecutionState &state) {
    //bupt use
    if(state.isSPEO())
        return;
  if (replayOut && replayPosition!=replayOut->numObjects) {
    klee_warning_once(replayOut,
                      "replay did not consume all objects in test input.");
  }

  interpreterHandler->incPathsExplored();

  std::set<ExecutionState*>::iterator it = addedStates.find(&state);
  if (it==addedStates.end()) {
    state.pc = state.prevPC;

    removedStates.insert(&state);
  } else {
    // never reached searcher, just delete immediately
    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it3 =
      seedMap.find(&state);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    addedStates.erase(it);
    processTree->remove(state.ptreeNode);
    delete &state;
  }
}

void Executor::terminateStateEarly(ExecutionState &state,
                                   const Twine &message) {
  if (!OnlyOutputStatesCoveringNew || state.coveredNew ||
      (AlwaysOutputSeeds && seedMap.count(&state)))
    interpreterHandler->processTestCase(state, (message + "\n").str().c_str(),
                                        "early");
  terminateState(state);
}

void Executor::terminateStateOnExit(ExecutionState &state) {
  //bupt use
  if(BuptShadow)
  {
    if(state.needTestCase)
        interpreterHandler->processTestCase(state, 0, 0);
  }
  else
  {
      if (!OnlyOutputStatesCoveringNew || state.coveredNew ||
          (AlwaysOutputSeeds && seedMap.count(&state)))
        interpreterHandler->processTestCase(state, 0, 0);
  }
  terminateState(state);
}
//bupt use
void Executor::createTestCaseButNoTerminate(ExecutionState &state)
{
    if(BuptShadow)
        interpreterHandler->processTestCase(state, 0, 0);
    state.constraints.pop_back();
    state.needTestCase=false;
    state.ctlordata=false;
    state.ctlAffected=false;
}

const InstructionInfo & Executor::getLastNonKleeInternalInstruction(const ExecutionState &state,
    Instruction ** lastInstruction) {
  // unroll the stack of the applications state and find
  // the last instruction which is not inside a KLEE internal function
  ExecutionState::stack_ty::const_reverse_iterator it = state.stack.rbegin(),
      itE = state.stack.rend();

  // don't check beyond the outermost function (i.e. main())
  itE--;

  const InstructionInfo * ii = 0;
  if (kmodule->internalFunctions.count(it->kf->function) == 0){
    ii =  state.prevPC->info;
    *lastInstruction = state.prevPC->inst;
    //  Cannot return yet because even though
    //  it->function is not an internal function it might of
    //  been called from an internal function.
  }

  // Wind up the stack and check if we are in a KLEE internal function.
  // We visit the entire stack because we want to return a CallInstruction
  // that was not reached via any KLEE internal functions.
  for (;it != itE; ++it) {
    // check calling instruction and if it is contained in a KLEE internal function
    const Function * f = (*it->caller).inst->getParent()->getParent();
    if (kmodule->internalFunctions.count(f)){
      ii = 0;
      continue;
    }
    if (!ii){
      ii = (*it->caller).info;
      *lastInstruction = (*it->caller).inst;
    }
  }

  if (!ii) {
    // something went wrong, play safe and return the current instruction info
    *lastInstruction = state.prevPC->inst;
    return *state.prevPC->info;
  }
  return *ii;
}
void Executor::terminateStateOnError(ExecutionState &state,
                                     const llvm::Twine &messaget,
                                     const char *suffix,
                                     const llvm::Twine &info) {
  std::string message = messaget.str();
  static std::set< std::pair<Instruction*, std::string> > emittedErrors;
  Instruction * lastInst;
  const InstructionInfo &ii = getLastNonKleeInternalInstruction(state, &lastInst);

  if (BuptShadow || EmitAllErrors ||
      emittedErrors.insert(std::make_pair(lastInst, message)).second) {
    if (ii.file != "") {
      klee_message("ERROR: %s:%d: %s", ii.file.c_str(), ii.line, message.c_str());
    } else {
      klee_message("ERROR: (location information missing) %s", message.c_str());
    }
    if (!EmitAllErrors)
      klee_message("NOTE: now ignoring this error at this location");

    std::string MsgString;
    llvm::raw_string_ostream msg(MsgString);
    msg << "Error: " << message << "\n";
    if (ii.file != "") {
      msg << "File: " << ii.file << "\n";
      msg << "Line: " << ii.line << "\n";
      msg << "assembly.ll line: " << ii.assemblyLine << "\n";
    }
    msg << "Stack: \n";
    state.dumpStack(msg);

    std::string info_str = info.str();
    if (info_str != "")
      msg << "Info: \n" << info_str;
    //bupt use
    if(BuptShadow)
    {
        if(state.isUE())
        {
            //generate test case for err directly in UE mode
            std::string shadowsuffix(suffix);
            shadowsuffix="unified."+shadowsuffix;
            state.needTestCase=true;
            interpreterHandler->processTestCase(state, msg.str().c_str(), shadowsuffix.c_str());
            state.needTestCase=false;
            terminateState(state);
        } else {
            // delay test case generation in split mode
            state.tmode=ExecutionState::err;
            state.splitStatus=true;
            state.errpc=state.prevPC;
            state.errmsg=msg.str();
            state.suffix=suffix;
        }
    }
    else
    {
        interpreterHandler->processTestCase(state, msg.str().c_str(), suffix);
        terminateState(state);
    }
  }

}

// XXX shoot me
static const char *okExternalsList[] = { "printf",
                                         "fprintf",
                                         "puts",
                                         "getpid" };
static std::set<std::string> okExternals(okExternalsList,
                                         okExternalsList +
                                         (sizeof(okExternalsList)/sizeof(okExternalsList[0])));

void Executor::callExternalFunction(ExecutionState &state,
                                    KInstruction *target,
                                    Function *function,
                                    std::vector< ref<Expr> > &arguments) {
    // check if specialFunctionHandler wants it
    if (specialFunctionHandler->handle(state, function, target, arguments))
        return;

    if (NoExternals && !okExternals.count(function->getName())) {
        llvm::errs() << "KLEE:ERROR: Calling not-OK external function : "
                     << function->getName().str() << "\n";
        terminateStateOnError(state, "externals disallowed", "user.err");
        return;
    }
    is_print=false;
    std::string func_name=function->getName().str();
    if(func_name=="syscall")//syscall write
    {
        ref<Expr> callno=arguments[0];
        if (ConstantExpr *ce = dyn_cast<ConstantExpr>(callno)) {
            llvm::APInt novalue=ce->getAPValue();
            const uint64_t *nodata=novalue.getRawData();
            if(*nodata==1||*nodata==16||*nodata==18||*nodata==20||*nodata==296||*nodata==311)
            {
                is_print=true;
                printfunc="syscall write";
            }
        }
    }
    else
    if(func_name=="pututline"||func_name=="write"||func_name=="putc"||func_name=="fputc"||func_name=="putw"||func_name=="puts"||func_name=="fputs"||func_name=="fwrite"||func_name=="vprintf"||func_name=="vsprintf"||func_name=="fputchar"||func_name=="fprintf"||func_name=="vfprintf"||func_name=="printf"||func_name=="putchar")
    {
        is_print=true;
        printfunc=func_name;
    }

    // normal external function handling path
    // allocate 128 bits for each argument (+return value) to support fp80's;
    // we could iterate through all the arguments first and determine the exact
    // size we need, but this is faster, and the memory usage isn't significant.
    uint64_t *args = (uint64_t*) alloca(2*sizeof(*args) * (arguments.size() + 1));
    memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
    unsigned wordIndex = 2;
    //bupt use

    uint64_t *new_args = (uint64_t*) alloca(2*sizeof(*new_args) * (arguments.size() + 1));
    memset(new_args, 0, 2 * sizeof(*new_args) * (arguments.size() + 1));
    // store args for situation that one or more arguments contain shadow expression
    unsigned new_wordIndex = 2;
    bool shadow_exe=false;
    // check all arguments, if one argument contain shadow expression, set flag shadow_exe = true
    for(std::vector< ref<Expr> >::iterator ai=arguments.begin(), ae=arguments.end(); ai!=ae; ++ai)
    {
        if((*ai).isNull())
            continue;
        if((*ai)->isContainShadow())
        {
            ref<Expr> left=(*ai)->findShadowExpr(0);
            ref<Expr> right=(*ai)->findShadowExpr(1);
            if(state.isSPEO())
                (*ai)=left;
            else if(state.isSPEN())
                (*ai)=right;
            else if(state.isUE())
            {
                ref<Expr> dif_arg=NeExpr::create(left, right);
                bool mustBeFalse;
                bool success=solver->mustBeFalse(state, dif_arg, mustBeFalse, false);
                assert(success && "FIXME");
                if(!mustBeFalse){
                    shadow_exe=true;
                    break;
                }
                else
                    (*ai)=right;
            }
        }
    }

    bool IsShadowed=false;
    //std::map< ObjectPair, std::pair< ref<Expr> , ref<Expr> > > record;
    //std::map< const MemoryObject*, std::map< unsigned, ref<Expr> > > record;
    std::map<const MemoryObject*,std::vector<ref<Expr> > > record;
    std::set< const MemoryObject* > allRelatedMems;
    std::map< size_t, ref<Expr> > VarargRecord;
    ref<Expr> left, right;
    StackFrame &sf=state.stack.back();
    //rebuild arguments
    // look all the memory space *function* related, include the memory space the pointer type argument points to, and the space pointed by the pointer stored in the memory space
    int idx=0;
    for(std::vector< ref<Expr> >::iterator ai=arguments.begin(), ae=arguments.end(); ai!=ae; ++ai)
        //update the shexp to old version in memory space. in UE and SPEO mode
        //update the shexp to new version in memory space in SPEN mode
    {
        bool needtestcase=true;
        if((*ai).isNull())
            continue;
        if((*ai)->isContainShadow())
        {
            left= (*ai)->findShadowExpr(0);
            right=(*ai)->findShadowExpr(1);
            if(is_print && state.isUE())
            {
                ref<Expr> dif_arg=NeExpr::create(left,right);
                bool mustBeFalse;
                bool success=solver->mustBeFalse(state, dif_arg, mustBeFalse, false);
                assert(success && "FIXME");
                if(!mustBeFalse){
                    //generate test case
                    state.needTestCase=true;
                    state.ctlordata=true;
                    std::string MsgString;
                    llvm::raw_string_ostream msg(MsgString);
                    msg << "Data Divergence Founded in print-family-functions "<<func_name<<"\n";
                    if (target->info->file !="") {
                      msg << "File: " << target->info->file << "\n";
                      msg << "Line: " << target->info->line << "\n";
                      msg << "assembly.ll line: " << target->info->assemblyLine << "\n";
                    }
		    msg << "Stack: \n";
	    	    state.dumpStack(msg);
                    state.divmsg=msg.str();
                    interpreterHandler->processTestCase(state,0,0);
                    state.needTestCase=false;
                    state.ctlordata=false;
                    needtestcase=false;
                }
            }
            if(state.isSPEN())
                left=right;
        }
        else
            left=(*ai);
        //check whether "left" is an address
        if(left->isPointer())//pointer
        {
            if(debug_pointer==1){
                errs()<<"check argument "<<left<<"\n";
            }
            ObjectPair op;
            bool resolve_success;
            bool result=state.addressSpace.resolveOne(state, solver, left, op, resolve_success);
            if(result && resolve_success)
            {
                allRelatedMems.insert(op.first);
                if(debug_pointer==1){
                    errs()<<"find mo in address "<<op.first->address<<"\n";
                }
                const MemoryObject *aMO=op.first;
                const ObjectState *aOS=op.second;
                const MemoryObject *varMO=aMO;
                const ObjectState *varOS=aOS;
                unsigned size=aMO->size;

                if(aMO->size <= 8 && aMO->size != 1 && aMO->size != 2 && aMO->size !=4  && aMO->size != 8){
                   ref<Expr> offset=aMO->getOffsetExpr(left);
                   ref<Expr> expr;
                   unsigned size=aMO->size*8;
                   expr=aOS->read(offset,size);//XXX: to update
                   if(debug_pointer==1){
                       errs() << "value "<<left
                           << " width "<<left->getWidth()<<" found "
                           << "mo "<<aMO->address<< "\n";
                       aMO->allocSite->dump();
                       errs()<<"offset: "<<offset<<"\n"
                           <<"value in mo:\n";
                       for (unsigned i=0; i<aMO->size; i++) {
                           ref<Expr> av = aOS->read8(i);
                           errs()<<av<<" ";
                       }
                       errs()<<"\n";
                       errs()<< "-------- End value dump ------------\n";
                       errs()<< "expr read from mo:\n"
                           <<expr<<"\n";
                   }
                    continue;
                }
                //store var arg
                if(aMO->isStoreVararg){
                    if(debug_pointer==1){
                        errs()<<"argument "<<left<<" is PointerTy and the memory pointed stores Vararg\n";
                    }
                    ObjectState *sv_wos=state.addressSpace.getWriteable(aMO,aOS);
                    if(isX86_64){
                        sv_wos->write(0,ConstantExpr::create(48,32));
                        sv_wos->write(4,ConstantExpr::create(304,32));
                        sv_wos->write(16,ConstantExpr::create(0,64));
                        ref<Expr> address = sv_wos->read(8,64);
                        if(address->isContainShadow()){
                            // update address to one version
                            // in UE and SPEO mode update to old version
                            // in SPEN mode update to new version
                            if(state.isSPEN()){
                                address=address->findShadowExpr(1);
                                sv_wos->write(8,address);
                            } else{
                                address=address->findShadowExpr(0);
                                sv_wos->write(8,address);
                            }
                        }
                        if(address->isPointer())//pointer
                        {
                            ObjectPair argOP;
                            bool resolve_success;
                            bool result=state.addressSpace.resolveOne(state,solver,address,argOP,resolve_success);
                            if(result && resolve_success){
                                    allRelatedMems.insert(argOP.first);
                             //   if(argOP.first->isVararg){
                                    if(debug_pointer==1){
                                        errs()<<"memory in address "<<left<<" stores Vararg address: "<<address<<" in x64 machine\n";
                                    }
                                    varMO=argOP.first;
                                    varOS=argOP.second;
                             //   }
                            }
                        }
                    } else {
                        ref<Expr> address = sv_wos->read(0,32);
                        if(address->isContainShadow()){
                            if(state.isSPEN()){
                                 address=address->findShadowExpr(1);
                                 sv_wos->write(0,address);
                            } else {
                                 address=address->findShadowExpr(0);
                                 sv_wos->write(0,address);
                            }
                        }
                        if(address->isPointer())//x32
                        {
                            ObjectPair argOP;
                            bool resolve_success;
                            bool result=state.addressSpace.resolveOne(state,solver,address,argOP,resolve_success);
                            if(result && resolve_success){
                                    allRelatedMems.insert(argOP.first);
                                   if(debug_pointer==1){
                                        errs()<<"memory in address "<<left<<" stores Vararg address: "<<address<<" in x32 machine\n";
                                    }
                                    varMO=argOP.first;
                                    varOS=argOP.second;
                            }
                        }
                    }
                    if(varMO->size <= 8 && varMO->size != 1 &&
                            varMO->size != 2 && varMO->size !=4  && varMO->size != 8){
                        // all the size cases cannot be a pointer type value
                        continue;
                    }

                    ObjectState *var_wos=state.addressSpace.getWriteable(varMO,varOS);
                    for(std::map<size_t,size_t>::iterator it=sf.varargsMap.begin(),ie=sf.varargsMap.end();it!=ie;++it){
                        if(isX86_64 && it->second != Expr::Int64 ){
                            continue;
                        } else if(it->second != Expr::Int32){
                            continue;
                        }
                        ref<Expr> res=var_wos->read(it->first,it->second);
                        if(debug_pointer==1){
                            errs()<<"Vararg in address: "<<varMO->address
                                <<" stores vararg "<<res<<"\n";
                        }
                        if(res->isPointer()){
                            if(state.isSPEN()){
                                IsShadowed=IsShadowed || handlePointer(res,record,allRelatedMems,state,needtestcase && is_print,2);
                            } else {
                                IsShadowed=IsShadowed || handlePointer(res,record,allRelatedMems,state,needtestcase && is_print,1);
                            }
                        }
                    }
                }
                //not var arg
                else{
                   ref<Expr> offset=aMO->getOffsetExpr(left);
                   if(debug_pointer==1){
                       errs() << "value "<<left
                           << " width "<<left->getWidth()<<" found "
                           << "mo "<<aMO->address<< "\n";
                       aMO->allocSite->dump();
                       errs()<<"offset: "<<offset<<"\n"
                           <<"value in mo:\n";
                       for (unsigned i=0; i<aMO->size; i++) {
                           ref<Expr> av = aOS->read8(i);
                           errs()<<av<<" ";
                       }
                       errs()<<"\n";
                       errs()<< "-------- End value dump ------------\n";
                   }
                   ref<Expr> expr;
                    if(isX86_64){
                        expr=aOS->read(offset,Expr::Int64);//XXX: is x64-64 architecture
                    } else {
                        expr=aOS->read(offset,Expr::Int32);//XXX: is x86-32 architecture
                    }
                   if(expr->isPointer()){
                       // looking forward
                        if(state.isSPEN()){
                            IsShadowed=IsShadowed || handlePointer(expr,record,allRelatedMems,state,needtestcase && is_print,2);
                        } else {
                            IsShadowed=IsShadowed || handlePointer(expr,record,allRelatedMems,state,needtestcase && is_print,1);
                        }
                   } else {
                       // deal with notPointerTy expression
                       ObjectState *wos=state.addressSpace.getWriteable(aMO,aOS);
                       op.second=wos;
                       for (unsigned i=0; i<aMO->size; i++) {
                           ref<Expr> av = wos->read8(i);
                           if(av->isContainShadow()){
                               if(state.isSPEN()){
                                   wos->write(i,av->findShadowExpr(1));
                               } else if(state.isSPEO()){
                                   wos->write(i,av->findShadowExpr(0));
                               } else {
                                   record[aMO].push_back(av->findShadowExpr(1));
                                   wos->write(i,av->findShadowExpr(0));
                                   IsShadowed=true;
                               }
                           } else {
                                record[aMO].push_back(av);
                           }
                       }
                   }
                }
            } else {
                if(debug_pointer==1){
                    errs()<<"find mo failed\n";
                }
            }
        }
    }//rebuild arguments

    //UE shadow execution
    if(shadow_exe){
        // shadow_exe == true represents that the arguments of *function* are differ in old/new version
        // thus we use arg and new_arg store two versions arguments separately
        for (std::vector<ref<Expr> >::iterator ai = arguments.begin(), ae = arguments.end(); ai!=ae; ++ai) {
            if (AllowExternalSymCalls)
            {
                // don't bother checking uniqueness
                if(debug_cef==1){
                    errs()<<"ExSymCall 1.argument "<<(*ai)<<"\n";
                    if((*ai)->isPointer())
                        errs()<<" is Pointer\n";
                    else
                        errs()<<" is not Pointer\n";
                }
                ref<ConstantExpr> ce;
                ref<ConstantExpr> new_ce;
                if((*ai)->isContainShadow()){
                    // for argument that contains shadow expression
                    // arg and new_arg separately store left/right expression from shadow expression
                    ref<Expr> left=(*ai)->findShadowExpr(0);
                    ref<Expr> right=(*ai)->findShadowExpr(1);
                    bool success = solver->getValue(state, left, ce,false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    ce->toMemory(&args[wordIndex]);
                    wordIndex += (ce->getWidth()+63)/64;
                    bool new_success = solver->getValue(state, right, new_ce,false);
                    assert(new_success && "FIXME: Unhandled solver failure");
                    (void) new_success;
                    new_ce->toMemory(&new_args[new_wordIndex]);
                    new_wordIndex += (new_ce->getWidth()+63)/64;
                } else {
                    // for argument that does not contain shadow expression
                    // arg and new_arg separately store the same argument expression
                    bool success = solver->getValue(state, *ai, ce,false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    ce->toMemory(&args[wordIndex]);
                    wordIndex += (ce->getWidth()+63)/64;
                    bool new_success = solver->getValue(state, *ai, new_ce,false);
                    assert(new_success && "FIXME: Unhandled solver failure");
                    (void) new_success;
                    new_ce->toMemory(&new_args[new_wordIndex]);
                    new_wordIndex += (new_ce->getWidth()+63)/64;
                }
            }  // AllowExternalSymCalls
            else {
                // similar with AllowExternalSymCalls
                if((*ai)->isContainShadow()){
                    bool left_err=false, right_err=false;
                    ref<Expr> left=(*ai)->findShadowExpr(0);
                    ref<Expr> right=(*ai)->findShadowExpr(1);
                    ref<Expr> arg = toUnique(state, left);
                    ref<Expr> new_arg = toUnique(state, right);
                    if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
                        // XXX kick toMemory functions from here
                        ce->toMemory(&args[wordIndex]);
                        wordIndex += (ce->getWidth()+63)/64;
                    } else {
                        errs()<<"left err\n";
                        left_err=true;
                    }
                    if (ConstantExpr *ce = dyn_cast<ConstantExpr>(new_arg)) {
                        // XXX kick toMemory functions from here
                        ce->toMemory(&new_args[new_wordIndex]);
                        new_wordIndex += (ce->getWidth()+63)/64;
                    } else {
                        errs()<<"right err\n";
                        right_err=true;
                    }
                    if(left_err && right_err){
                        terminateStateOnExecError(state,
                                      "external call with symbolic argument in both old and new versions: " +
                                      function->getName());
                        return;
                    } else if ( left_err && ! right_err ){
                        terminateStateOnExecError(state,
                                      "external call with symbolic argument only in old version: " +
                                      function->getName());
                        return;
                    } else if ( !left_err && right_err ){
                        terminateStateOnExecError(state,
                                      "external call with symbolic argument only in new versions: " +
                                      function->getName());
                        return;
                    }
                } else {
                    ref<Expr> arg = toUnique(state, *ai);
                    if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
                        // XXX kick toMemory functions from here
                        ce->toMemory(&args[wordIndex]);
                        wordIndex += (ce->getWidth()+63)/64;
                        ce->toMemory(&new_args[new_wordIndex]);
                        new_wordIndex += (ce->getWidth()+63)/64;
                    } else {
                        errs()<<"arg err\n";
                        terminateStateOnExecError(state,
                                      "external call with symbolic argument in both old and new versions: " +
                                      function->getName());
                        return;
                    } // meet error when dyn_cast<ConstantExpr>(arg)
                } // argument not contain shadow expression
            } // not AllowExternalSymCalls
        } // loop for each argument
    } // shadow execution

    else
    {
        // shadow_exe == false represents that *function* arguments are same in the two versions
        for (std::vector<ref<Expr> >::iterator ai = arguments.begin(),
             ae = arguments.end(); ai!=ae; ++ai) {
            if (AllowExternalSymCalls) { // don't bother checking uniqueness
                if(debug_cef==1){
                    errs()<<"ExSymCall 2.argument "<<(*ai)<<"\n";
                    if((*ai)->isPointer())
                        errs()<<" is Pointer\n";
                    else
                        errs()<<" is not Pointer\n";
                }
                ref<ConstantExpr> ce;
                bool success;
                if(BuptShadow)
                    success= solver->getValue(state, *ai, ce,!state.hasChangedBefore());
                else
                    success= solver->getValue(state, *ai, ce);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                ce->toMemory(&args[wordIndex]);
                wordIndex += (ce->getWidth()+63)/64;
            } else {
                ref<Expr> arg = toUnique(state, *ai);
                if(debug_cef==1){
                    errs()<<"argument "<<(*ai)<<"\n"
                        <<"after toUnique " << arg << "\n";
                }
                if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
                // XXX kick toMemory functions from here
                ce->toMemory(&args[wordIndex]);
                wordIndex += (ce->getWidth()+63)/64;
                } else {
                    if(state.isSPEO())
                    {
                        errs()<<"old err\n";
                        terminateStateOnExecError(state,
                                  "external call with symbolic argument in old version: " +
                                  function->getName());
                    }
                    else if(state.isSPEN())
                    {
                        errs()<<"new err\n";
                        terminateStateOnExecError(state,
                                  "external call with symbolic argument in new version: " +
                                  function->getName());
                    }
                    else
                    {
                        errs()<<"arg err 2\n";
                        terminateStateOnExecError(state,
                                  "external call with symbolic argument in both old and new versions: " +
                                  function->getName());
                    }
                    return;
                }
            }
        }
    }

    state.addressSpace.copyOutConcretes();

    if (!SuppressExternalWarnings) {
        std::string TmpStr;
        llvm::raw_string_ostream os(TmpStr);
        os << "calling external: " << function->getName().str() << "(";
        for (unsigned i=0; i<arguments.size(); i++) {
          os << arguments[i];
          if (i != arguments.size()-1)
          os << ", ";
        }
        os << ")";

        if (AllExternalWarnings)
          klee_warning("%s", os.str().c_str());
        else
          klee_warning_once(function, "%s", os.str().c_str());
    }

    // actual execute external call
    if(state.isUE())
    {

        bool old_err_suc=false, new_err_suc=false;
        bool old_err_copy=false, new_err_copy=false;
        std::map<const MemoryObject*,std::vector<ref<Expr> > > stageOneRes;
        if(IsShadowed){
            // IsShadowed == true represents that the memory spaces which *function* arguments may access contain shadow expression
            // thus we separately execute two version's function call, store the result separately and combine together after both of
            // the two version finish current external call
            if(!shadow_exe)
                new_args=args;
            bool success = externalDispatcher->executeCall(function, target->inst, args);
            if (!success) {
                old_err_suc=true;
            }
            if (!state.addressSpace.copyInConcretes()) {
                old_err_copy=true;
            }
            if (!old_err_suc && ! old_err_copy) {
                // Store the values in all argument related memory space in the old version execution in stageOneRes
                for(std::set<const MemoryObject*>::iterator it=allRelatedMems.begin(),ie=allRelatedMems.end();it!=ie;it++){
                    const ObjectState *os=state.addressSpace.findObject(*it);
                    for(unsigned i=0;i<(*it)->size;i++){
                        ref<Expr> e=os->read8(i);
                        stageOneRes[*it].push_back(e);
                    }
                }
                //Update values in all related memorys for the old version to the new version's
                for(std::map< const MemoryObject*, std::vector<ref<Expr> > >::iterator it=record.begin(),ie=record.end();it!=ie;++it){
                    const ObjectState *os=state.addressSpace.findObject(it->first);
                    ObjectState *wos=state.addressSpace.getWriteable(it->first,os);
                    for(unsigned i=0;i<(it->first)->size;i++){
                        wos->write(i,(it->second)[i]);
                    }
                }
            }
            record.erase(record.begin(), record.end());
            allRelatedMems.erase(allRelatedMems.begin(), allRelatedMems.end());
            IsShadowed=false;
            //rebuild arguments for new version run
            //update the shexp to new version in memory space.
            for(std::vector< ref<Expr> >::iterator ai=arguments.begin(), ae=arguments.end(); ai!=ae; ++ai)
            {
                bool needtestcase=false;
                if((*ai).isNull())
                    continue;
                if((*ai)->isContainShadow())
                {
                    left= (*ai)->findShadowExpr(1);
                }
                else
                    left=(*ai);
                //check whether "left" is an address
                if(left->isPointer())//pointer
                {
                    if(debug_pointer==1){
                        errs()<<"check argument "<<left<<"\n";
                    }
                    ObjectPair op;
                    bool resolve_success;
                    bool result=state.addressSpace.resolveOne(state, solver, left, op, resolve_success);
                    if(result && resolve_success)
                    {
                        allRelatedMems.insert(op.first);
                        if(debug_pointer==1){
                            errs()<<"find mo in address "<<op.first->address<<"\n";
                        }
                        const MemoryObject *aMO=op.first;
                        const ObjectState *aOS=op.second;
                        const MemoryObject *varMO=aMO;
                        const ObjectState *varOS=aOS;
                        unsigned size=aMO->size;

                        if(aMO->size <= 8 && aMO->size != 1 && aMO->size != 2 && aMO->size !=4  && aMO->size != 8){
                           if(debug_pointer==1){
                               errs() << "value "<<left
                                   << " width "<<left->getWidth()<<" found "
                                   << "mo "<<aMO->address<< "\n";
                               aMO->allocSite->dump();
                               errs()<<"value in mo:\n";
                               for (unsigned i=0; i<aMO->size; i++) {
                                   ref<Expr> av = aOS->read8(i);
                                   errs()<<av<<" ";
                               }
                               errs()<<"\n";
                               errs()<< "-------- End value dump ------------\n";
                           }
                            continue;
                        }
                        //store var arg
                        if(aMO->isStoreVararg){
                            if(debug_pointer==1){
                                errs()<<"argument "<<left<<" is PointerTy and the memory pointed stores Vararg\n";
                            }
                            ObjectState *sv_wos=state.addressSpace.getWriteable(aMO,aOS);
                            if(isX86_64){
                                sv_wos->write(0,ConstantExpr::create(48,32));
                                sv_wos->write(4,ConstantExpr::create(304,32));
                                sv_wos->write(16,ConstantExpr::create(0,64));
                                ref<Expr> address = sv_wos->read(8,64);
                                if(address->isContainShadow()){
                                    address=address->findShadowExpr(1);
                                    sv_wos->write(8,address);
                                }
                                if(address->isPointer())//pointer
                                {
                                    ObjectPair argOP;
                                    bool resolve_success;
                                    bool result=state.addressSpace.resolveOne(state,solver,address,argOP,resolve_success);
                                    if(result && resolve_success){
                                        allRelatedMems.insert(argOP.first);
                                        if(debug_pointer==1){
                                            errs()<<"memory in address "<<left<<" stores Vararg address: "<<address<<" in x64 machine\n";
                                        }
                                        varMO=argOP.first;
                                        varOS=argOP.second;
                                    }
                                }
                            } else {
                                ref<Expr> address = sv_wos->read(0,32);
                                if(address->isContainShadow()){
                                    address=address->findShadowExpr(1);
                                    sv_wos->write(0,address);
                                }
                                if(address->isPointer())//x32
                                {
                                    ObjectPair argOP;
                                    bool resolve_success;
                                    bool result=state.addressSpace.resolveOne(state,solver,address,argOP,resolve_success);
                                    if(result && resolve_success){
                                            allRelatedMems.insert(argOP.first);
                                           if(debug_pointer==1){
                                                errs()<<"memory in address "<<left<<" stores Vararg address: "<<address<<" in x32 machine\n";
                                            }
                                            varMO=argOP.first;
                                            varOS=argOP.second;
                                    }
                                }
                            }
                            if(varMO->size <= 8 && varMO->size != 1 &&
                                    varMO->size != 2 && varMO->size !=4  && varMO->size != 8){
                                continue;
                            }

                            ObjectState *var_wos=state.addressSpace.getWriteable(varMO,varOS);
                            for(std::map<size_t,size_t>::iterator it=sf.varargsMap.begin(),ie=sf.varargsMap.end();it!=ie;++it){
                                if(isX86_64 && it->second != Expr::Int64 ){
                                    continue;
                                } else if(it->second != Expr::Int32){
                                    continue;
                                }
                                ref<Expr> res=var_wos->read(it->first,it->second);
                                if(debug_pointer==1){
                                    errs()<<"Vararg in address: "<<varMO->address
                                        <<" stores vararg "<<res<<"\n";
                                }
                                if(res->isPointer()){
                                   IsShadowed=IsShadowed || handlePointer(res,record,allRelatedMems,state,needtestcase && is_print,2);
                                }
                            }
                        }
                        //not var arg
                        else{
                           if(debug_pointer==1){
                               errs() << "value "<<left
                                   << " width "<<left->getWidth()<<" found "
                                   << "mo "<<aMO->address<< "\n";
                               aMO->allocSite->dump();
                                errs() <<"value in mo:\n";
                               for (unsigned i=0; i<aMO->size; i++) {
                                   ref<Expr> av = aOS->read8(i);
                                   errs()<<av<<" ";
                               }
                               errs()<<"\n";
                               errs()<< "-------- End value dump ------------\n";
                           }
                           ref<Expr> offset=aMO->getOffsetExpr(left);
                           ref<Expr> expr;
                           // unsigned size=aMO->size*8;
                            if(isX86_64){
                                expr=aOS->read(offset,Expr::Int64);//XXX: is x64-64 architecture
                            } else {
                                expr=aOS->read(offset,Expr::Int32);//XXX: is x86-32 architecture
                            }
                           if(expr->isPointer()){
                               // looking forward
                                IsShadowed=IsShadowed || handlePointer(left,record,allRelatedMems,state,needtestcase && is_print, 2);
                           } else {
                               // deal with notPointerTy arguments
                               ObjectState *wos=state.addressSpace.getWriteable(aMO,aOS);
                               op.second=wos;
                               for (unsigned i=0; i<aMO->size; i++) {
                                   ref<Expr> av = wos->read8(i);
                                   if(av->isContainShadow()){
                                       record[aMO].push_back(av->findShadowExpr(0));
                                       wos->write(i,av->findShadowExpr(1));
                                       IsShadowed=true;
                                   } else {
                                        record[aMO].push_back(av);
                                   }
                               }
                           }
                        }
                    } else {
                        if(debug_pointer==1){
                            errs()<<"find mo failed\n";
                        }
                    }
                }
            }
            bool new_success = externalDispatcher->executeCall(function, target->inst, new_args);
            if (!new_success) {
                new_err_suc=true;
            }
            if (!state.addressSpace.copyInConcretes()) {
                new_err_copy=true;
            }
            if(!new_err_suc && !new_err_copy){
                // combine the execution result for memory space both access in the two version
                // write the combination back to the memorys
                for(std::set<const MemoryObject*>::iterator it=allRelatedMems.begin(),ie=allRelatedMems.end();it!=ie;){
                    std::map<const MemoryObject*, std::vector<ref<Expr> > >::iterator stageOne=stageOneRes.find(*it);
                    if(stageOne != stageOneRes.end()){
                        const ObjectState *os=state.addressSpace.findObject(*it);
                        ObjectState *wos=state.addressSpace.getWriteable(*it,os);
                        for(unsigned i=0;i<(*it)->size;i++){
                            ref<Expr> ae=(stageOne->second)[i];
                            ref<Expr> be=wos->read8(i);
                            ref<Expr> res=ShadowExpr::create(ae,be);
                            wos->write(i,res);
                        }
                        stageOneRes.erase(stageOne);
                        std::set<const MemoryObject*>::iterator tmp=it;
                        it++;
                        allRelatedMems.erase(it);
                    } else {
                        it++;
                    }
                }
                // for all the memory only access in the new version,
                // create shadow expression: shadow(0,new_value)
                // and write back the shexp to the memory
                for(std::set<const MemoryObject*>::iterator it=allRelatedMems.begin(),ie=allRelatedMems.end();it!=ie;it++){
                    const ObjectState *os=state.addressSpace.findObject(*it);
                    ObjectState *wos=state.addressSpace.getWriteable(*it,os);
                    for(unsigned i=0;i<(*it)->size;i++){
                        ref<Expr> be=wos->read8(i);
                        ref<Expr> ae=ConstantExpr::create(0,be->getWidth());
                        ref<Expr> res=ShadowExpr::create(ae,be);
                        wos->write(i,res);
                    }
                }
                // for all the memory only access in the old version,
                // create shadow expression: shadow(old_value,0)
                // and write back the shexp to the memory
                for(std::map<const MemoryObject*, std::vector<ref<Expr> > >::iterator it=stageOneRes.begin(),ie=stageOneRes.end();it!=ie;it++){
                    const ObjectState *os=state.addressSpace.findObject(it->first);
                    ObjectState *wos=state.addressSpace.getWriteable(it->first,os);
                    for(unsigned i=0;i<(it->first)->size;i++){
                        ref<Expr> ae=(it->second)[i];
                        ref<Expr> be=ConstantExpr::create(0,ae->getWidth());
                        ref<Expr> res=ShadowExpr::create(ae,be);
                        wos->write(i,res);
                    }
                }
            }
            if( old_err_suc && new_err_suc ){
                terminateStateOnError(state, " in both version: failed extcall: " + function->getName(),
                              "both.external.err");
                return;
            } else if( old_err_suc && !new_err_suc ){
                terminateStateOnError(state, " in old version: failed external call: " + function->getName(),
                              "old.external.err");
                return;
            }  else if( !old_err_suc && new_err_suc ){
                terminateStateOnError(state, " in new version: failed external call: " + function->getName(),
                              "new.external.err");
                return;
            }
            if( old_err_copy && new_err_copy ){
                terminateStateOnError(state, "in both version: external modified read-only object",
                              "external.err");
                return;
            } else if( old_err_copy && !new_err_copy ){
                terminateStateOnError(state, "in old version: external modified read-only object",
                              "external.err");
                return;
            }  else if( old_err_copy && new_err_copy ){
                terminateStateOnError(state, "in new version: external modified read-only object",
                              "external.err");
                return;
            }

            LLVM_TYPE_Q Type *resultType = target->inst->getType();
            if (resultType != Type::getVoidTy(getGlobalContext())) {
                ref<Expr> e = ConstantExpr::fromMemory((void*) args,
                                       getWidthForLLVMType(resultType));
                ref<Expr> new_e = ConstantExpr::fromMemory((void*) new_args,
                                       getWidthForLLVMType(resultType));
                ref<Expr> dif_e=NeExpr::create(e,new_e);
                bool mustBeFalse;
                bool success=solver->mustBeFalse(state,dif_e,mustBeFalse,false);
                assert(success && "FIXME");
                if(mustBeFalse){
                    bindLocal(target, state, e);
                } else{
                    bindLocal(target, state, ShadowExpr::create(e,new_e));
                }
            }
        } else {//!IsShadowed
            // IsShadowed == false represents that all the memoryspace accessed in the two version contains no shadow expression
            // thus we do not need to deal with the values write to the memory spaces
            if(shadow_exe){
                // However, if shadow_exe == true,
                // we still need to separately execute the two version with different arguments
                // and combine the execution results
                bool success = externalDispatcher->executeCall(function, target->inst, args);
                if (!success) {
                    old_err_suc=true;
                }
                if (!state.addressSpace.copyInConcretes()) {
                    old_err_copy=true;
                }
                bool new_success = externalDispatcher->executeCall(function, target->inst, new_args);
                if (!new_success) {
                    new_err_suc=true;
                }
                if (!state.addressSpace.copyInConcretes()) {
                    new_err_copy=true;
                }
                if( old_err_suc && new_err_suc ){
                    terminateStateOnError(state, " in both version: failed external call: " + function->getName(),
                            "both.external.err");
                    return;
                } else if( old_err_suc && !new_err_suc ){
                    terminateStateOnError(state, " in old version: failed external call: " + function->getName(),
                            "old.external.err");
                    return;
                }  else if( !old_err_suc && new_err_suc ){
                    terminateStateOnError(state, " in new version: failed external call: " + function->getName(),
                            "new.external.err");
                    return;
                }
                if( old_err_copy && new_err_copy ){
                    terminateStateOnError(state, "in both version: external modified read-only object",
                            "external.err");
                    return;
                } else if( old_err_copy && !new_err_copy ){
                    terminateStateOnError(state, "in old version: external modified read-only object",
                            "external.err");
                    return;
                }  else if( old_err_copy && new_err_copy ){
                    terminateStateOnError(state, "in new version: external modified read-only object",
                            "external.err");
                    return;
                }

                LLVM_TYPE_Q Type *resultType = target->inst->getType();
                if (resultType != Type::getVoidTy(getGlobalContext())) {
                    ref<Expr> e = ConstantExpr::fromMemory((void*) args,
                                       getWidthForLLVMType(resultType));
                    ref<Expr> new_e = ConstantExpr::fromMemory((void*) new_args,
                                       getWidthForLLVMType(resultType));
                    ref<Expr> dif_e=NeExpr::create(e,new_e);
                    bool mustBeFalse;
                    bool success=solver->mustBeFalse(state,dif_e,mustBeFalse,false);
                    assert(success && "FIXME");
                    if(mustBeFalse){
                        bindLocal(target, state, e);
                    } else{
                        bindLocal(target, state, ShadowExpr::create(e,new_e));
                    }
                }
            } else {
                bool success = externalDispatcher->executeCall(function, target->inst, args);
                if (!success) {
                    terminateStateOnError(state, "failed external call: " + function->getName(),
                              "external.err");
                    return;
                }

                if (!state.addressSpace.copyInConcretes()) {
                    terminateStateOnError(state, "external modified read-only object",
                              "external.err");
                    return;
                }

                LLVM_TYPE_Q Type *resultType = target->inst->getType();
                if (resultType != Type::getVoidTy(getGlobalContext())) {
                    ref<Expr> e = ConstantExpr::fromMemory((void*) args,
                                       getWidthForLLVMType(resultType));
                    bindLocal(target, state, e);
                }
            } // contain no shadow arguments and has no shadowexpr in varargs
        } // may contain shadow arguments but has no shadowexpr in varargs
    }
    else
    {

          bool success = externalDispatcher->executeCall(function, target->inst, args);
          if (!success) {
            terminateStateOnError(state, "failed external call: " + function->getName(),
                      "external.err");
            return;
          }

          if (!state.addressSpace.copyInConcretes()) {
            terminateStateOnError(state, "external modified read-only object",
                      "external.err");
            return;
          }

          LLVM_TYPE_Q Type *resultType = target->inst->getType();
          if (resultType != Type::getVoidTy(getGlobalContext())) {
            ref<Expr> e = ConstantExpr::fromMemory((void*) args,
                               getWidthForLLVMType(resultType));
            bindLocal(target, state, e);
          }
    }
    is_print=false;
}

/***/

ref<Expr> Executor::replaceReadWithSymbolic(ExecutionState &state,
                                            ref<Expr> e) {
  unsigned n = interpreterOpts.MakeConcreteSymbolic;
  if (!n || replayOut || replayPath)
    return e;

  // right now, we don't replace symbolics (is there any reason to?)
  if (!isa<ConstantExpr>(e))
    return e;

  if (n != 1 && random() % n)
    return e;

  // create a new fresh location, assert it is equal to concrete value in e
  // and return it.

  static unsigned id;
  const Array *array = Array::CreateArray("rrws_arr" + llvm::utostr(++id),
                      Expr::getMinBytesForWidth(e->getWidth()));
  ref<Expr> res = Expr::createTempRead(array, e->getWidth());
  ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, res));
  llvm::errs() << "Making symbolic: " << eq << "\n";
  state.addConstraint(eq);
  return res;
}

ObjectState *Executor::bindObjectInState(ExecutionState &state,
                                         const MemoryObject *mo,
                                         bool isLocal,
                                         const Array *array) {
  ObjectState *os = array ? new ObjectState(mo, array) : new ObjectState(mo);
  state.addressSpace.bindObject(mo, os);

  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object
  // on function return.
  if (isLocal)
    state.stack.back().allocas.push_back(mo);

  return os;
}

void Executor::executeAlloc(ExecutionState &state,
                            ref<Expr> size,
                            bool isLocal,
                            KInstruction *target,
                            bool zeroMemory,
                            const ObjectState *reallocFrom) {

    //bupt use
    ref<Expr> old_size,new_size;
    bool isShadowed=false,hasNewSize=false;
    if(size->isContainShadow()){
        //check weather the two version alloc different size of the memory
        old_size=size->findShadowExpr(0);
        new_size=size->findShadowExpr(1);
        ref<Expr> dif_size=NeExpr::create(old_size,new_size);
        bool mustBeFalse;
        bool success=solver->mustBeFalse(state,dif_size,mustBeFalse,false);
        assert(success && "Unhandled solver");
        if(!mustBeFalse)
        {
            if(state.isSPEO())
                size=old_size;
            else if(state.isSPEN())
                size=new_size;
            else
                isShadowed=true;
        }
        else
            size=new_size;
    }
    else {
        old_size=size;
        new_size=size;
    }
    if(state.isUE() && isShadowed)
    {
        ref<Expr> old_osize=old_size,new_osize=new_size;
        old_size=toUnique(state, old_size);
        new_size=toUnique(state, new_size);
        ConstantExpr *old_CE = dyn_cast<ConstantExpr>(old_size);
        ConstantExpr *new_CE = dyn_cast<ConstantExpr>(new_size);
        if(old_CE && new_CE) // both size expression in the two version are ConstantExpr
        {
            if (!dyn_cast<ConstantExpr>(old_osize) && !dyn_cast<ConstantExpr>(new_osize))
            {
                addConstraint(state, EqExpr::create(old_osize, old_size));
                addConstraint(state, EqExpr::create(new_osize, new_size));
            }
            // alloc different size of memory and
            // generate shexpr for instrunction execution result
            // combine the different memory space to the *locals*
            MemoryObject *old_mo = memory->allocate(old_CE->getZExtValue(), isLocal, false,
                        state.prevPC->inst);
            MemoryObject *new_mo = memory->allocate(new_CE->getZExtValue(), isLocal, false,
                        state.prevPC->inst);
            if(!old_mo && !new_mo)
                bindLocal(target, state, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
            else
            {
                if(!old_mo && new_mo)
                {

                    ObjectState *new_os = bindObjectInState(state, new_mo, isLocal);
                    if (zeroMemory) {
                        new_os->initializeToZero();
                    } else {
                        new_os->initializeToRandom();
                    }
                    ref<Expr> shadow_res=ShadowExpr::create(ConstantExpr::alloc(0, Context::get().getPointerWidth()),new_mo->getBaseExpr());
                    bindLocal(target, state, shadow_res);

                    if (reallocFrom) {
                        unsigned count = std::min(reallocFrom->size, new_os->size);
                        for (unsigned i=0; i<count; i++)
                          new_os->write(i, reallocFrom->read8(i));
                        state.newFreed.push_back(reallocFrom->getObject());
                    }
                }
                if(old_mo && !new_mo)
                {

                    ObjectState *old_os = bindObjectInState(state, old_mo, isLocal);
                    if (zeroMemory) {
                      old_os->initializeToZero();
                    } else {
                      old_os->initializeToRandom();
                    }
                    ref<Expr> shadow_res=ShadowExpr::create(old_mo->getBaseExpr(),ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                    bindLocal(target, state, shadow_res);

                    if (reallocFrom) {
                      unsigned count = std::min(reallocFrom->size, old_os->size);
                      for (unsigned i=0; i<count; i++)
                        old_os->write(i, reallocFrom->read8(i));
                      state.oldFreed.push_back(reallocFrom->getObject());
                    }
                }
                if(old_mo && new_mo)
                {
                    ObjectState *new_os = bindObjectInState(state, new_mo, isLocal);
                    ObjectState *old_os = bindObjectInState(state, old_mo, isLocal);
                    if (zeroMemory) {
                      old_os->initializeToZero();
                    } else {
                      old_os->initializeToRandom();
                    }
                    if (zeroMemory) {
                      new_os->initializeToZero();
                    } else {
                      new_os->initializeToRandom();
                    }
                    ref<Expr> shadow_res=ShadowExpr::create(old_mo->getBaseExpr(),new_mo->getBaseExpr());
                    bindLocal(target, state, shadow_res);
                    if (reallocFrom) {
                      unsigned count_old = std::min(reallocFrom->size, old_os->size);
                      unsigned count_new = std::min(reallocFrom->size, new_os->size);
                      for (unsigned i=0; i<count_old; i++)
                        old_os->write(i, reallocFrom->read8(i));
                      for (unsigned i=0; i<count_new; i++)
                        new_os->write(i, reallocFrom->read8(i));
                      state.addressSpace.unbindObject(reallocFrom->getObject());
                    }
                }
            }
        }

        else if(!old_CE && new_CE) // size expression in the old version is not ConstantExpr, need to get constant value for the old_size
        {
            ref<ConstantExpr> example;
            bool success = solver->getValue(state, old_size, example,!state.hasChangedBefore());
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;

            // Try and start with a small example.
            Expr::Width W = example->getWidth();
            while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
              ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
              bool res;
              bool success = solver->mayBeTrue(state, EqExpr::create(tmp, old_size), res,false);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (!res)
            break;
              example = tmp;
            }

            StatePair fixedSize = fork(state, EqExpr::create(example, old_size), true);

            if (fixedSize.second) {
                // Check for exactly two values
                ref<ConstantExpr> tmp;
                bool success = solver->getValue(*fixedSize.second, old_size, tmp,false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                bool res;
                success = solver->mustBeTrue(*fixedSize.second,
                                 EqExpr::create(tmp, old_size),
                                 res,
                                 false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                if (res) {
                    ref<Expr> shadow_size=ShadowExpr::create(tmp,new_size);
                    executeAlloc(*fixedSize.second, shadow_size, isLocal,
                        target, zeroMemory, reallocFrom);
                } else {
                    // See if a *really* big value is possible. If so assume
                    // malloc will fail for it, so lets fork and return 0.
                    StatePair hugeSize =fork(*fixedSize.second,
                            UltExpr::create(ConstantExpr::alloc(1<<31, W), old_size),true);
                    if (hugeSize.first) {
                        klee_message("NOTE: found huge malloc, returning 0");
                        bindLocal(target, *hugeSize.first,
                              ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                    }

                    if (hugeSize.second) {
                        std::string Str;
                        llvm::raw_string_ostream info(Str);
                        ExprPPrinter::printOne(info, "  size expr", old_size);
                        info << "  concretization : " << example << "\n";
                        info << "  unbound example: " << tmp << "\n";
                        terminateStateOnError(*hugeSize.second,
                                  "concretized symbolic size",
                                  "model.err",
                                  info.str());
                    }
                }
            }

            if (fixedSize.first) // can be zero when fork fails
            {
                ref<Expr> shadow_size=ShadowExpr::create(example,new_size);
                executeAlloc(*fixedSize.first, shadow_size, isLocal,
                       target, zeroMemory, reallocFrom);
            }
        }

        else if(old_CE && !new_CE) // size expression in the new version is not ConstantExpr, need to get constant value for the new_size
        {
            ref<ConstantExpr> example;
            bool success = solver->getValue(state, new_size, example,!state.hasChangedBefore());
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;

            // Try and start with a small example.
            Expr::Width W = example->getWidth();
            while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
              ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
              bool res;
              bool success = solver->mayBeTrue(state, EqExpr::create(tmp, new_size), res,false);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (!res)
                break;
              example = tmp;
            }
            StatePair fixedSize = fork(state, EqExpr::create(example, new_size), true);

            if (fixedSize.second) {
              // Check for exactly two values
                ref<ConstantExpr> tmp;
                bool success = solver->getValue(*fixedSize.second, new_size, tmp,false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                bool res;
                success = solver->mustBeTrue(*fixedSize.second,
                                 EqExpr::create(tmp, new_size),
                                 res,
                                 false);
                assert(success && "FIXME: Unhandled solver failure");
                (void) success;
                if (res) {
                    ref<Expr> shadow_size=ShadowExpr::create(old_size,tmp);
                    executeAlloc(*fixedSize.second, shadow_size, isLocal,
                        target, zeroMemory, reallocFrom);
                } else {
                    // See if a *really* big value is possible. If so assume
                    // malloc will fail for it, so lets fork and return 0.
                    StatePair hugeSize =
                      fork(*fixedSize.second,
                       UltExpr::create(ConstantExpr::alloc(1<<31, W), new_size),
                       true);
                    if (hugeSize.first) {
                      klee_message("NOTE: found huge malloc, returning 0");
                      bindLocal(target, *hugeSize.first,
                            ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                    }

                    if (hugeSize.second) {
                      std::string Str;
                      llvm::raw_string_ostream info(Str);
                      ExprPPrinter::printOne(info, "  size expr", new_size);
                      info << "  concretization : " << example << "\n";
                      info << "  unbound example: " << tmp << "\n";
                      terminateStateOnError(*hugeSize.second,
                                "concretized symbolic size",
                                "model.err",
                                info.str());
                    }
                }
            }

            if (fixedSize.first) // can be zero when fork fails
            {
                ref<Expr> shadow_size=ShadowExpr::create(old_size,example);
                executeAlloc(*fixedSize.first, shadow_size, isLocal,
                       target, zeroMemory, reallocFrom);
            }
        }

        else
        {
            ref<ConstantExpr> new_example,old_example;
            bool success = solver->getValue(state, old_size, old_example,!state.hasChangedBefore());
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            // Try and start with a small example.
            Expr::Width old_W = old_example->getWidth();
            while (old_example->Ugt(ConstantExpr::alloc(128, old_W))->isTrue()) {
              ref<ConstantExpr> old_tmp = old_example->LShr(ConstantExpr::alloc(1, old_W));
              bool res;
              bool success = solver->mayBeTrue(state, EqExpr::create(old_tmp, old_size), res,false);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (!res)
                break;
              old_example = old_tmp;
            }

            success = solver->getValue(state, new_size, new_example,!state.hasChangedBefore());
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;
            // Try and start with a small example.
            Expr::Width new_W = new_example->getWidth();
            while (new_example->Ugt(ConstantExpr::alloc(128, new_W))->isTrue()) {
              ref<ConstantExpr> new_tmp = new_example->LShr(ConstantExpr::alloc(1, new_W));
              bool res;
              bool success = solver->mayBeTrue(state, EqExpr::create(new_tmp, new_size), res,false);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (!res)
                break;
              new_example = new_tmp;
            }

            StatePair new_fixedSize = fork(state, EqExpr::create(new_example, new_size), true);
            if(new_fixedSize.first){
                StatePair dif_fixedSize = fork(*new_fixedSize.first, EqExpr::create(old_example,old_size),true);
                if (dif_fixedSize.second) // can be zero when fork fails
                {
                    ref<ConstantExpr> tmp;
                    bool success = solver->getValue(*dif_fixedSize.second, old_size, tmp,false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    bool res;
                    success = solver->mustBeTrue(*dif_fixedSize.second,
                                 EqExpr::create(tmp, old_size),
                                 res,
                                 false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    if (res) {
                        ref<Expr> dif_example=ShadowExpr::create(tmp,new_example);
                        executeAlloc(*dif_fixedSize.second, dif_example, isLocal,
                               target, zeroMemory, reallocFrom);
                    } else {
                        // See if a *really* big value is possible. If so assume
                        // malloc will fail for it, so lets fork and return 0.
                        StatePair hugeSize =
                          fork(*dif_fixedSize.second,
                           UltExpr::create(ConstantExpr::alloc(1<<31, old_W), old_size),
                           true);
                        if (hugeSize.first) {
                            ref<Expr> dif_example=ShadowExpr::create(ConstantExpr::alloc(0, Context::get().getPointerWidth()),new_example);
                            executeAlloc(*dif_fixedSize.second, dif_example, isLocal,
                                   target, zeroMemory, reallocFrom);
                        }

                        if (hugeSize.second) {
                            std::string Str;
                            llvm::raw_string_ostream info(Str);
                              ExprPPrinter::printOne(info, "  size expr", old_size);
                              info << "  concretization : " << old_example << "\n";
                              info << "  unbound example: " << tmp << "\n";
                              terminateStateOnError(*hugeSize.second,
                                        "new_example==new_size && old_example!=old_size && no satisfied old_example is found && INTMAX >= old_size: concretized symbolic size",
                                        "n_succ.o_failed._model.err",
                                        info.str());
                        }
                    }
                }

                if (dif_fixedSize.first) // can be zero when fork fails
                {
                    ref<Expr> dif_example=ShadowExpr::create(old_example,new_example);
                    executeAlloc(*dif_fixedSize.first, dif_example, isLocal,
                           target, zeroMemory, reallocFrom);
                }
            }
            if(new_fixedSize.second){
                StatePair dif_fixedSize2 = fork(*new_fixedSize.second, EqExpr::create(old_example,old_size),true);
                if (dif_fixedSize2.first) // can be zero when fork fails
                {
                    // Check for exactly two values
                    ref<ConstantExpr> tmp;
                    bool success = solver->getValue(*dif_fixedSize2.first, new_size, tmp,false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    bool res;
                    success = solver->mustBeTrue(*dif_fixedSize2.first,
                                     EqExpr::create(tmp, new_size),
                                     res,
                                     false);
                    assert(success && "FIXME: Unhandled solver failure");
                    (void) success;
                    if (res) {
                        ref<Expr> dif_example=ShadowExpr::create(old_example,tmp);
                        executeAlloc(*dif_fixedSize2.first, dif_example, isLocal,
                               target, zeroMemory, reallocFrom);
                    } else {
                        // See if a *really* big value is possible. If so assume
                        // malloc will fail for it, so lets fork and return 0.
                        StatePair hugeSize =
                          fork(*dif_fixedSize2.first,
                           UltExpr::create(ConstantExpr::alloc(1<<31, new_W), new_size),
                           true);
                        if (hugeSize.first) {
                            ref<Expr> dif_example=ShadowExpr::create(old_example,ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                            executeAlloc(*hugeSize.first, dif_example, isLocal,
                                   target, zeroMemory, reallocFrom);
                        }

                        if (hugeSize.second) {
                            std::string Str;
                            llvm::raw_string_ostream info(Str);
                              ExprPPrinter::printOne(info, "  size expr", new_size);
                              info << "  concretization : " << new_example << "\n";
                              info << "  unbound example: " << tmp << "\n";
                              terminateStateOnError(*hugeSize.second,
                                        "new_example != new_size && old_example == old_size  && no satisfied new_example is found && INTMAX >= new_size: concretized symbolic size",
                                        "new_failed.old_succ.model.err",
                                        info.str());
                        }
                    }
                }

                if (dif_fixedSize2.second) // can be zero when fork fails
                {
                    // Check for exactly two values
                    ref<ConstantExpr> new_tmp;
                    bool new_success = solver->getValue(*dif_fixedSize2.second, new_size, new_tmp,false);
                    assert(new_success && "FIXME: Unhandled solver failure");
                    (void) new_success;
                    bool new_res;
                    new_success = solver->mustBeTrue(*dif_fixedSize2.second,
                                 EqExpr::create(new_tmp, new_size),
                                 new_res,
                                 false);
                    assert(new_success && "FIXME: Unhandled solver failure");
                    (void) new_success;
                    // Check for exactly two values
                    ref<ConstantExpr> old_tmp;
                    bool old_success = solver->getValue(*dif_fixedSize2.second, old_size, old_tmp,false);
                    assert(old_success && "FIXME: Unhandled solver failure");
                    (void) old_success;
                    bool old_res;
                    old_success = solver->mustBeTrue(*dif_fixedSize2.second,
                                 EqExpr::create(old_tmp, old_size),
                                 old_res,
                                 false);
                    assert(old_success && "FIXME: Unhandled solver failure");
                    (void) old_success;
                    if (old_res && new_res) {
                        ref<Expr> dif_example=ShadowExpr::create(old_tmp,new_tmp);
                        executeAlloc(*dif_fixedSize2.second, dif_example, isLocal,
                           target, zeroMemory, reallocFrom);
                    } else {
                        // See if a *really* big value is possible. If so assume
                        // malloc will fail for it, so lets fork and return 0.
                        StatePair hugeSize_new =
                          fork(*dif_fixedSize2.second,
                               UltExpr::create(ConstantExpr::alloc(1<<31, new_W), new_size),
                               true);
                        if (hugeSize_new.first) {
                        StatePair dif_hugeSize =
                          fork(*hugeSize_new.first,
                               UltExpr::create(ConstantExpr::alloc(1<<31, old_W), old_size),
                               true);
                            if(dif_hugeSize.first){
                            bindLocal(target,*dif_hugeSize.first,ConstantExpr::alloc(0,Context::get().getPointerWidth()));
                            }
                            if(dif_hugeSize.second){
                            std::string Str;
                            llvm::raw_string_ostream info(Str);
                              ExprPPrinter::printOne(info, "  size expr", old_size);
                              info << "  concretization : " << old_example << "\n";
                              info << "  unbound example: " << old_tmp << "\n";
                              terminateStateOnError(*dif_hugeSize.second,
                                        "new_example != new_size && old_example != old_size && (!old_res || !new_res) && INTMAX < new_size && INTMAX >= old_size: found huge malloc in new and concretized symbolic size in old",
                                        "new_failed.old_failed.model.err",
                                        info.str());
                            }
                        }
                        if (hugeSize_new.second) {
                            StatePair dif_hugeSize =fork(*hugeSize_new.second,
                               UltExpr::create(ConstantExpr::alloc(1<<31, old_W), old_size),
                               true);
                            if(dif_hugeSize.first){
                            std::string Str;
                            llvm::raw_string_ostream info(Str);
                              ExprPPrinter::printOne(info, "  size expr", new_size);
                              info << "  concretization : " << new_example << "\n";
                              info << "  unbound example: " << new_tmp << "\n";
                              terminateStateOnError(*dif_hugeSize.first,
                                        "new_example != new_size && old_example != old_size && (!old_res || !new_res) && INTMAX >= new_size && INTMAX < old_size: found concretized symbolic size in new and huge malloc size in old",
                                        "new_failed.old_failed.model.err",
                                        info.str());
                            }
                            if(dif_hugeSize.second){
                            std::string Str;
                            llvm::raw_string_ostream info(Str);
                              ExprPPrinter::printOne(info, "  old_size expr", old_size);
                              info << "  concretization : " << old_example << "\n";
                              info << "  unbound example: " << old_tmp << "\n";
                              ExprPPrinter::printOne(info, "  new_size expr", new_size);
                              info << "  concretization : " << new_example << "\n";
                              info << "  unbound example: " << new_tmp << "\n";
                              terminateStateOnError(*dif_hugeSize.second,
                                        "new_example != new_size && old_example != old_size && (!old_res || !new_res) && INTMAX >= new_size && INTMAX >= old_size: both found concretized symbolic size",
                                        "new_failed.old_failed.model.err",
                                        info.str());
                            }
                        }
                    }
                }
            }
        }
    }
    else
    {
        //bupt use
        ref<Expr> osize;
        if(BuptShadow)
            osize=size;
        size = toUnique(state, size);
        if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
            //bupt use
            if(BuptShadow && !dyn_cast<ConstantExpr> (osize)){
                if(!state.constraints.addConstraintInMerge(EqExpr::create(osize, size))){
                    state.markHasChanged();
                    size = toUnique(state, size);
                    addConstraint(state, EqExpr::create(osize, size));
                    state.removeHasChanged();
                }
            }
            MemoryObject *mo = memory->allocate(CE->getZExtValue(), isLocal, false,
                            state.prevPC->inst);
            if (!mo) {
              bindLocal(target, state,
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
            } else {
                ObjectState *os = bindObjectInState(state, mo, isLocal);
                if (zeroMemory) {
                  os->initializeToZero();
                } else {
                  os->initializeToRandom();
                }
                if(debug_mem==1){
                    errs() << " alloca memory "<<mo<<" address: "<< mo->address << " for inst: "<<target->info->assemblyLine<<"@";
                    target->inst->dump();
                }
                bindLocal(target, state, mo->getBaseExpr());

                if (reallocFrom) {
                  unsigned count = std::min(reallocFrom->size, os->size);
                  for (unsigned i=0; i<count; i++)
                    os->write(i, reallocFrom->read8(i));
                  /*
                  if(state.isSPEO())
                    state.oldFreed.push_back(reallocFrom->getObject());
                  else if(state.isSPEN())
                    state.newFreed.push_back(reallocFrom->getObject());
                  else
                  */
                    state.addressSpace.unbindObject(reallocFrom->getObject());
                }
            }
        } else {
            // XXX For now we just pick a size. Ideally we would support
            // symbolic sizes fully but even if we don't it would be better to
            // "smartly" pick a value, for example we could fork and pick the
            // min and max values and perhaps some intermediate (reasonable
            // value).
            //
            // It would also be nice to recognize the case when size has
            // exactly two values and just fork (but we need to get rid of
            // return argument first). This shows up in pcre when llvm
            // collapses the size expression with a select.

            ref<ConstantExpr> example;
            bool success ;
            if(BuptShadow)
                success= solver->getValue(state, size, example,!state.hasChangedBefore());
            else
                success= solver->getValue(state, size, example);
            assert(success && "FIXME: Unhandled solver failure");
            (void) success;

            // Try and start with a small example.
            Expr::Width W = example->getWidth();
            while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
              ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
              bool res;
              bool success ;
              if(BuptShadow)
                  success= solver->mayBeTrue(state, EqExpr::create(tmp, size), res,!state.hasChangedBefore());
              else
                  success= solver->mayBeTrue(state, EqExpr::create(tmp, size), res);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (!res)
                break;
              example = tmp;
            }

            StatePair fixedSize = fork(state, EqExpr::create(example, size), true);

            if (fixedSize.second) {
              // Check for exactly two values
              ref<ConstantExpr> tmp;
              bool success ;
              if(BuptShadow)
                  success= solver->getValue(*fixedSize.second, size, tmp,!state.hasChangedBefore());
              else
                  success= solver->getValue(*fixedSize.second, size, tmp);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              bool res;
              if(BuptShadow)
                success = solver->mustBeTrue(*fixedSize.second, EqExpr::create(tmp, size), res,!state.hasChangedBefore());
              else
                success = solver->mustBeTrue(*fixedSize.second, EqExpr::create(tmp, size), res);
              assert(success && "FIXME: Unhandled solver failure");
              (void) success;
              if (res) {
                executeAlloc(*fixedSize.second, tmp, isLocal,
                         target, zeroMemory, reallocFrom);
              } else {
                // See if a *really* big value is possible. If so assume
                // malloc will fail for it, so lets fork and return 0.
                StatePair hugeSize =
                  fork(*fixedSize.second,
                       UltExpr::create(ConstantExpr::alloc(1<<31, W), size),
                       true);
                if (hugeSize.first) {
                  klee_message("NOTE: found huge malloc, returning 0");
                  bindLocal(target, *hugeSize.first,
                        ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                }

                if (hugeSize.second) {
                  std::string Str;
                  llvm::raw_string_ostream info(Str);
                  ExprPPrinter::printOne(info, "  size expr", size);
                  info << "  concretization : " << example << "\n";
                  info << "  unbound example: " << tmp << "\n";
                  terminateStateOnError(*hugeSize.second,
                            "concretized symbolic size",
                            "model.err",
                            info.str());
                }
              }
            }

            if (fixedSize.first) // can be zero when fork fails
              executeAlloc(*fixedSize.first, example, isLocal,
                   target, zeroMemory, reallocFrom);
        }
    }
}


void Executor::executeFree(ExecutionState &state,
                           ref<Expr> address,
                           KInstruction *target) {

    //bupt use
    ref<Expr> old_addr;
    ref<Expr> new_addr;
    bool hasShadowAddr=false;
    if(address->isContainShadow())
    {
        old_addr=address->findShadowExpr(0);
        new_addr=address->findShadowExpr(1);
        ref<Expr> dif_addr=NeExpr::create(old_addr, new_addr);
        bool mustBeFalse;
        bool success=solver->mustBeFalse(state,dif_addr,mustBeFalse,false);
        assert(success && "Unhandled solver");
        if(!mustBeFalse)
        {
            if(state.isSPEO())
                address=old_addr;
            else if(state.isSPEN())
                address=new_addr;
            else
                hasShadowAddr=true;
        }
        else
            address=new_addr;
    }
    else
    {
        old_addr=address;
        new_addr=address;
    }
    if(state.isUE() && hasShadowAddr)
    {
          StatePair zeroPointer = fork(state, Expr::createIsZero(new_addr), true);
          // check whether the free address in the new version is zero
          if (zeroPointer.first) {
            StatePair old_zeroPointer = fork(*zeroPointer.first, Expr::createIsZero(old_addr), true);
            if(old_zeroPointer.first){
                // both free address in the two version is zero
                if (target)
                  bindLocal(target, *old_zeroPointer.first, Expr::createPointer(0));
            }
            if(old_zeroPointer.second){
                // the address in the new version is zero
                // the address in the old version is not zero
                ExactResolutionList rl;
                resolveExact(*old_zeroPointer.second, old_addr, rl, "new is zero address,free for old");

                for (Executor::ExactResolutionList::iterator it = rl.begin(),
                   ie = rl.end(); it != ie; ++it) {
                  const MemoryObject *mo = it->first.first;
                  if (mo->isLocal) {
                    terminateStateOnError(*it->second,
                          "free of alloca only in old version",
                          "div_old.free.err",
                          getAddressInfo(*it->second, old_addr));
                  } else if (mo->isGlobal) {
                    terminateStateOnError(*it->second,
                          "free of global only in old version",
                          "div_old.free.err",
                          getAddressInfo(*it->second, old_addr));
                  } else {
                    std::vector<const MemoryObject*>::iterator moit=find(it->second->newFreed.begin(),it->second->newFreed.end(),mo);
                    if(moit!=it->second->newFreed.end()){
                        // both the versions need to free the memoryobject *mo*
                        it->second->newFreed.erase(moit);
                        it->second->addressSpace.unbindObject(mo);
                    } else{
                        // the old version cannot access MemoryObject *mo* from now on
                        it->second->oldFreed.push_back(mo);
                    }
                    if (target)
                      bindLocal(target, *it->second, Expr::createPointer(0));
                  }
                }
            }
          }
          if (zeroPointer.second) { // address in the new version not equals to zero
            StatePair old_zeroPointer = fork(*zeroPointer.second, Expr::createIsZero(old_addr), true);
            if(old_zeroPointer.first){
                // the address in the old version is zero
                // the address in the new version is not zero
                ExactResolutionList rl;
                resolveExact(*old_zeroPointer.first, new_addr, rl, "old is zero address,free for new");

                for (Executor::ExactResolutionList::iterator it = rl.begin(),
                   ie = rl.end(); it != ie; ++it) {
                  const MemoryObject *mo = it->first.first;
                  if (mo->isLocal) {
                    terminateStateOnError(*it->second,
                          "free of alloca only in new version",
                          "div_new.free.err",
                          getAddressInfo(*it->second, new_addr));
                  } else if (mo->isGlobal) {
                    terminateStateOnError(*it->second,
                          "free of global only in new version",
                          "div_new.free.err",
                          getAddressInfo(*it->second, new_addr));
                  } else {
                    std::vector<const MemoryObject*>::iterator moit=find(it->second->oldFreed.begin(),it->second->oldFreed.end(),mo);
                    if(moit!=it->second->oldFreed.end()){
                        // both the versions need to free the memoryobject *mo*
                        it->second->oldFreed.erase(moit);
                        it->second->addressSpace.unbindObject(mo);
                    } else{
                        // the new version cannot access MemoryObject *mo* from now on
                        it->second->newFreed.push_back(mo);
                    }
                    if (target)
                      bindLocal(target, *it->second, Expr::createPointer(0));
                  }
                }
            }
            if(old_zeroPointer.second){
                // both the address in the two versions are not zero
                ExactResolutionList old_rl;
                resolveExact(*old_zeroPointer.second, old_addr, old_rl, "both old and new are not zero,free for old");
                ExactResolutionList new_rl;
                resolveExact(*old_zeroPointer.second, new_addr, new_rl, "both old and new are not zero,free for new");

                for (Executor::ExactResolutionList::iterator it = new_rl.begin(),
                   ie = new_rl.end(); it != ie; ++it) {
                  const MemoryObject *mo = it->first.first;
                  if (mo->isLocal) {
                    terminateStateOnError(*it->second,
                          "free of alloca in new version",
                          "div_new.free.err",
                          getAddressInfo(*it->second, new_addr));
                  } else if (mo->isGlobal) {
                    terminateStateOnError(*it->second,
                          "free of global in new version",
                          "div_new.free.err",
                          getAddressInfo(*it->second, new_addr));
                  } else {
                    std::vector<const MemoryObject*>::iterator moit=find(it->second->oldFreed.begin(),it->second->oldFreed.end(),mo);
                    if(moit!=it->second->oldFreed.end()){
                        // both the versions need to free the memoryobject *mo*
                        it->second->oldFreed.erase(moit);
                        it->second->addressSpace.unbindObject(mo);
                    } else{
                        // the new version cannot access MemoryObject *mo* from now on
                        it->second->newFreed.push_back(mo);
                    }
                    /*
                    ref<Expr> old_mo_addr=mo->getBaseExpr();
                    it->second->addressSpace.unbindObject(mo);
                    //questions
                    ref<Expr> dif_mo=ShadowExpr::create(old_mo_addr,Expr::createPointer(0));
                    */
                    if (target)
                    {
                      bindLocal(target, *it->second,  Expr::createPointer(0));
                    }
                  }
                }
                for (Executor::ExactResolutionList::iterator it = old_rl.begin(),
                   ie = old_rl.end(); it != ie; ++it) {
                  const MemoryObject *mo = it->first.first;
                  if (mo->isLocal) {
                    terminateStateOnError(*it->second,
                          "free of alloca in old version",
                          "div_old.free.err",
                          getAddressInfo(*it->second, old_addr));
                  } else if (mo->isGlobal) {
                    terminateStateOnError(*it->second,
                          "free of global in old version",
                          "div_old.free.err",
                          getAddressInfo(*it->second, old_addr));
                  } else {
                    std::vector<const MemoryObject*>::iterator moit=find(it->second->newFreed.begin(),it->second->newFreed.end(),mo);
                    if(moit!=it->second->newFreed.end()){
                        // both the versions need to free the memoryobject *mo*
                        it->second->newFreed.erase(moit);
                        it->second->addressSpace.unbindObject(mo);
                    } else{
                        // the old version cannot access MemoryObject *mo* from now on
                        it->second->newFreed.push_back(mo);
                    }
                      /*
                    ref<Expr> old_mo_addr=mo->getBaseExpr();
                    it->second->addressSpace.unbindObject(mo);
                    //questions
                    ref<Expr> dif_mo=ShadowExpr::create(Expr::createPointer(0),old_mo_addr);
                    */
                    if (target)
                    {
                      bindLocal(target, *it->second, Expr::createPointer(0));
                    }
                  }
                }
            }
        }
    }
    else
    {
        // the two version is freeing the same memoryobject
     StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
      if (zeroPointer.first) {
        if (target)
          bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
      }
      if (zeroPointer.second) { // address != 0
        ExactResolutionList rl;
        resolveExact(*zeroPointer.second, address, rl, "free");

        for (Executor::ExactResolutionList::iterator it = rl.begin(),
           ie = rl.end(); it != ie; ++it) {
          const MemoryObject *mo = it->first.first;
          if (mo->isLocal) {
            terminateStateOnError(*it->second,
                          "free of alloca",
                          "free.err",
                          getAddressInfo(*it->second, address));
          } else if (mo->isGlobal) {
            terminateStateOnError(*it->second,
                          "free of global",
                          "free.err",
                          getAddressInfo(*it->second, address));
          } else {
                it->second->addressSpace.unbindObject(mo);
            if (target)
              bindLocal(target, *it->second, Expr::createPointer(0));
          }
        }
      }
    }
}

void Executor::resolveExact(ExecutionState &state,
                            ref<Expr> p,
                            ExactResolutionList &results,
                            const std::string &name) {
  // XXX we may want to be capping this?
  ResolutionList rl;
  state.addressSpace.resolve(state, solver, p, rl);

  ExecutionState *unbound = &state;
  for (ResolutionList::iterator it = rl.begin(), ie = rl.end();
       it != ie; ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());

    StatePair branches = fork(*unbound, inBounds, true);

    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));

    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }

  if (unbound) {
    terminateStateOnError(*unbound,
                          "memory error: invalid pointer: " + name,
                          "ptr.err",
                          getAddressInfo(*unbound, p));
  }
}

void Executor::executeMemoryOperation(ExecutionState &state,
                                      bool isWrite,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if read */,
                                      KInstruction *target /* undef if write */) {
  Expr::Width type = (isWrite ? value->getWidth() :
                     getWidthForLLVMType(target->inst->getType()));
  unsigned bytes = Expr::getMinBytesForWidth(type);
    //bupt use
    bool shadowed=false;
    ref<Expr> old_value=value, new_value=value, old_address=address, new_address=address, old_res, new_res;
    if(address->isContainShadow())
    {
        old_address=address->findShadowExpr(0);
        new_address=address->findShadowExpr(1);
        ref<Expr> dif_addr=NeExpr::create(old_address, new_address);
        bool mustBeFalse;
        bool success=solver->mustBeFalse(state, dif_addr, mustBeFalse, false);
        assert(success && "FIXME: Unhandled solver");
        if(!mustBeFalse)
        {
            if(state.isSPEO())
                address=old_address;
            else if(state.isSPEN())
                address=new_address;
            else
                shadowed=true;
        }
        else
            address=new_address;
    }

    if(isWrite && value->isContainShadow())
    {
        old_value=value->findShadowExpr(0);
        new_value=value->findShadowExpr(1);
        if(state.isSPEO())
            value=old_value;
        else if(state.isSPEN())
            value=new_value;
    }

    if (!BuptShadow && SimplifySymIndices) {
      if (!isa<ConstantExpr>(address))
        address = state.constraints.simplifyExpr(address);
      if (isWrite && !isa<ConstantExpr>(value))
        value = state.constraints.simplifyExpr(value);
    }
    if(shadowed && state.isUE())//shadow address
    {
        // fast path: single in-bounds resolution
        ObjectPair old_op;
        ObjectPair new_op;
        bool old_success,new_success;
        solver->setTimeout(coreSolverTimeout);

        if (!state.addressSpace.resolveOne(state, solver, old_address, old_op, old_success)) {
          old_address = toConstant(state, old_address, "resolveOne failure");
          old_success = state.addressSpace.resolveOne(cast<ConstantExpr>(old_address), old_op);
        }
        if (!state.addressSpace.resolveOne(state, solver, new_address, new_op, new_success)) {
          new_address = toConstant(state, new_address, "resolveOne failure");
          new_success = state.addressSpace.resolveOne(cast<ConstantExpr>(new_address), new_op);
        }
        solver->setTimeout(0);
        if (old_success && new_success) {
            const MemoryObject *old_mo = old_op.first;
            const MemoryObject *new_mo = new_op.first;
            std::vector<const MemoryObject*>::iterator old_moit=find(state.oldFreed.begin(),state.oldFreed.end(),old_mo);
            std::vector<const MemoryObject*>::iterator new_moit=find(state.newFreed.begin(),state.newFreed.end(),new_mo);
            bool old_UAF=false,new_UAF=false;
            if(old_moit!=state.oldFreed.end()){
                old_UAF=true;
            }
            if(new_moit!=state.newFreed.end()){
                new_UAF=true;
            }
            if(old_UAF && new_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed for both version",
                            "remain.ptr.err",
                            getAddressInfo(state, old_address));
                  return;
            } else if(old_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the old version",
                            "fixed.ptr.err",
                            getAddressInfo(state, old_address));
                  return;
            } else if (new_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the new version",
                            "newintro.ptr.err",
                            getAddressInfo(state, new_address));
                  return;
            }

            // bounds check
            ref<Expr> old_offset = old_mo->getOffsetExpr(old_address);
            ref<Expr> old_boundsCheck = old_mo->getBoundsCheckOffset(old_offset, bytes);

            ref<Expr> new_offset = new_mo->getOffsetExpr(new_address);
            ref<Expr> new_boundsCheck = new_mo->getBoundsCheckOffset(new_offset, bytes);
            bool old_inBounds,new_inBounds;
            solver->setTimeout(coreSolverTimeout);
            bool old_success = solver->mustBeTrue(state, old_boundsCheck,
                              old_inBounds, false);
            bool new_success = solver->mustBeTrue(state, new_boundsCheck,
                              new_inBounds, false);
            solver->setTimeout(0);
            if (!new_success) {
              state.pc = state.prevPC;
              terminateStateEarly(state, "Query timed out (bounds check) in new version.");
              return;
            }
            if (!old_success) {
              state.pc = state.prevPC;
              terminateStateEarly(state, "Query timed out (bounds check) in old version.");
              return;
            }

            if(old_success && new_success){
                if (old_inBounds && new_inBounds) {
                  const ObjectState *old_os = old_op.second;
                  const ObjectState *new_os = new_op.second;
                  if (MaxSymArraySize && old_mo->size >= MaxSymArraySize) {
                    old_address = toConstant(state, old_address, "max-sym-array-size");
                  }
                  if (MaxSymArraySize && new_mo->size >= MaxSymArraySize) {
                    new_address = toConstant(state, new_address, "max-sym-array-size");
                  }

                  old_offset = old_mo->getOffsetExpr(old_address);
                  new_offset = new_mo->getOffsetExpr(new_address);
                  shadowReadOrWrite(state,isWrite,type,target,old_address,old_value,old_offset,old_mo,old_os,new_address,new_value,new_offset,new_mo,new_os);
                  return;
                } // operation in bound
            }
        } // state.resolveOne success

        // we are on an error path (no resolution, multiple resolution, one
        // resolution with out of bounds)

        std::vector<ExecutionState*> boundCheck_state_storage;
        address=new_address;
        ResolutionList rl;
        solver->setTimeout(coreSolverTimeout);
        bool incomplete = state.addressSpace.resolve(state, solver, address, rl, 0, coreSolverTimeout, false);
        ResolutionList old_rl;
        incomplete = state.addressSpace.resolve(state,solver, old_address, old_rl, 0, coreSolverTimeout, false);

        ExecutionState *unbound = &state;
        for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
          const MemoryObject *mo = i->first;
          const ObjectState *os = i->second;
          ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

          StatePair branches = fork(*unbound, inBounds, true);
          ExecutionState *bound = branches.first;
          // bound can be 0 on failure or overlapped
          if (bound) {
              boundCheck_state_storage.push_back(bound);
              if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
                address = toConstant(*bound, address, "max-sym-array-size");
              }
              ref<Expr> offset=mo->getOffsetExpr(address);
              //normalReadOrWrite(*bound,isWrite,offset,type,value,target,mo,os);
              shadowReadOrWrite(state,isWrite,type,target,0,0,0,0,0,address,value,offset,mo,os);
          }
          unbound = branches.second;
          if (!unbound)
            break;
        }
        if (unbound) {
          if (incomplete) {
            terminateStateEarly(*unbound, "Query timed out (resolve).");
          } else {
              unbound->isInBound=false;
    #if DEBUG_EMO
              klee_message("in new version: still has \"unbound\" state");
    #endif
              boundCheck_state_storage.push_back(unbound);
          }
        }

        address=old_address;
        solver->setTimeout(coreSolverTimeout);
        //questions
        for(std::vector<ExecutionState*>::iterator it=boundCheck_state_storage.begin();it!=boundCheck_state_storage.end();++it){
            ExecutionState *unbound = (*it);
            solver->setTimeout(0);
            if(unbound->isInBound){
                for (ResolutionList::iterator i = old_rl.begin(), ie = old_rl.end(); i != ie; ++i) {
                  const MemoryObject *mo = i->first;
                  const ObjectState *os = i->second;
                  ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

                  StatePair branches = fork(*unbound, inBounds, true);
                  ExecutionState *bound = branches.first;
                  // bound can be 0 on failure or overlapped
                  if (bound) {
                      if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
                    address = toConstant(*bound, address, "max-sym-array-size");
                      }
                      ref<Expr> offset=mo->getOffsetExpr(address);
                      //normalReadOrWrite(*bound,isWrite,offset,type,value,target,mo,os);
                      shadowReadOrWrite(state,isWrite,type,target,address,value,offset,mo,os,0,0,0,0,0);
                  }
                  unbound = branches.second;
                  if (!unbound)
                    break;
                } // old_state inBounds and new_state inBounds

                if (unbound) {
                  if (incomplete) {
                    terminateStateEarly(*unbound, "Query timed out (resolve).");
                  } else {
                      terminateStateOnError(*unbound,
                                 "memory error: out of bound pointer",
                                "oo.ni.ptr.err",
                                getAddressInfo(*unbound, address));
                  } // old_state out of Bounds but new_state inBounds
                }
            } else {
              for (ResolutionList::iterator i = old_rl.begin(), ie = old_rl.end(); i != ie; ++i) {
                const MemoryObject *mo = i->first;
                const ObjectState *os = i->second;
                ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

                StatePair branches = fork(*unbound, inBounds, true);
                ExecutionState *bound = branches.first;
                // bound can be 0 on failure or overlapped
                if (bound) {
                  terminateStateOnError(*(*it),
                             "memory error: out of bound pointer",
                            "oi.no.ptr.err",
                             getAddressInfo(*(*it), new_address));
                unbound = branches.second;
                if (!unbound)
                break;
                } // old_state inBounds but new_state out of Bounds
              }
              if (unbound) {
                if (incomplete) {
                  terminateStateEarly(*unbound, "Query timed out (resolve).");
                } else {
                terminateStateOnError(*unbound,
                               "memory error: out of bound pointer",
                              "oo.no.ptr.err",
                              getAddressInfo(*unbound, address));
                } // old_state out of Bounds and new_state out of Bounds
              }
            } // shadow bound check for the new version and the old Version
        }
    }
    else
    {
      // fast path: single in-bounds resolution
      ObjectPair op;
      bool success;
      solver->setTimeout(coreSolverTimeout);
      if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
        address = toConstant(state, address, "resolveOne failure");
        success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
      }
      solver->setTimeout(0);

      if (success) {
        const MemoryObject *mo = op.first;
        if(state.isSPEO()){
            std::vector<const MemoryObject*>::iterator old_moit=find(state.oldFreed.begin(),state.oldFreed.end(),mo);
            if(old_moit!=state.oldFreed.end()){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the old version",
                            "fixed.ptr.err",
                            getAddressInfo(state, address));
                  return;
            }
        } else if (state.isSPEN()){
            std::vector<const MemoryObject*>::iterator new_moit=find(state.newFreed.begin(),state.newFreed.end(),mo);
            if(new_moit!=state.newFreed.end()){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the new version",
                            "newintro.ptr.err",
                            getAddressInfo(state, address));
                  return;
            }
        } else {
            std::vector<const MemoryObject*>::iterator old_moit=find(state.oldFreed.begin(),state.oldFreed.end(),mo);
            std::vector<const MemoryObject*>::iterator new_moit=find(state.newFreed.begin(),state.newFreed.end(),mo);
            bool old_UAF=false,new_UAF=false;
            if(old_moit!=state.oldFreed.end()){
                old_UAF=true;
            }
            if(new_moit!=state.newFreed.end()){
                new_UAF=true;
            }
            if(old_UAF && new_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed for both version",
                            "remain.ptr.err",
                            getAddressInfo(state, address));
                  return;
            } else if(old_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the old version",
                            "fixed.ptr.err",
                            getAddressInfo(state, address));
                  return;
            } else if (new_UAF){
                  terminateStateOnError(state,
                             "memory error: access memory after freed only in the new version",
                            "newintro.ptr.err",
                            getAddressInfo(state, address));
                  return;
            }
        }

        if (MaxSymArraySize && mo->size>=MaxSymArraySize) {
          address = toConstant(state, address, "max-sym-array-size");
        }

        ref<Expr> offset = mo->getOffsetExpr(address);

        bool inBounds;
        solver->setTimeout(coreSolverTimeout);
        if(debug_constraint==1){
            errs() <<"constraints size: "<<state.constraints.size()<<"\n";
            for(ConstraintManager::constraint_iterator pcit=state.constraints.begin(),pcie=state.constraints.end();pcit!=pcie;pcit++){
                (*pcit)->dump();
            }
        }
        bool success ;
        if(BuptShadow)
            success= solver->mustBeTrue(state, mo->getBoundsCheckOffset(offset, bytes),inBounds,!state.hasChangedBefore());
        else
            success= solver->mustBeTrue(state, mo->getBoundsCheckOffset(offset, bytes),inBounds);
        solver->setTimeout(0);
        if (!success) {
          state.pc = state.prevPC;
          terminateStateEarly(state, "Query timed out (bounds check).");
          return;
        }

        if (inBounds) {
          const ObjectState *os = op.second;
          if(MaxSymArraySize && mo->size>=MaxSymArraySize){
              address=toConstant(state, address, "max-sym-array-size");
              offset=mo->getOffsetExpr(address);
          }
          normalReadOrWrite(state, isWrite, offset, type, address, value, target, mo, os);
          return;
        }
      }

      // we are on an error path (no resolution, multiple resolution, one
      // resolution with out of bounds)

      ResolutionList rl;
      solver->setTimeout(coreSolverTimeout);
      bool incomplete = state.addressSpace.resolve(state, solver, address, rl,
                               0, coreSolverTimeout);
      solver->setTimeout(0);

      // XXX there is some query wasteage here. who cares?
      ExecutionState *unbound = &state;

      for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
        const MemoryObject *mo = i->first;
        const ObjectState *os = i->second;
        ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

        StatePair branches = fork(*unbound, inBounds, true);
        ExecutionState *bound = branches.first;

        // bound can be 0 on failure or overlapped
        if (bound) {
        if(MaxSymArraySize && mo->size>=MaxSymArraySize){
            address=toConstant(*bound, address, "max-sym-array-size");
        }
        ref<Expr> offset=mo->getOffsetExpr(address);
        normalReadOrWrite(*bound, isWrite, offset, type,address, value, target, mo, os);
        }

        unbound = branches.second;
        if (!unbound)
          break;
      }

      // XXX should we distinguish out of bounds and overlapped cases?
      if (unbound) {
        if (incomplete) {
          terminateStateEarly(*unbound, "Query timed out (resolve).");
        } else {
          terminateStateOnError(*unbound,
                    "memory error: out of bound pointer",
                    "ptr.err",
                    getAddressInfo(*unbound, address));
        }
      }
    }
}
//bupt use

void Executor::shadowReadOrWrite(ExecutionState &state,
        bool isWrite,
        Expr::Width type,
        KInstruction *target,
        ref<Expr> old_addr,
        ref<Expr> old_value,
        ref<Expr> old_offset,
        const MemoryObject *old_mo,
        const ObjectState *old_os,
        ref<Expr> new_addr,
        ref<Expr> new_value,
        ref<Expr> new_offset,
        const MemoryObject *new_mo,
        const ObjectState *new_os){
  ref<Expr> old_res, new_res;
  if (isWrite) {
    if (old_os && old_os->readOnly && new_os->readOnly) {
      terminateStateOnError(state,
                            "memory error: object read only in both versions",
                            "both.readonly.err");
    } else if (old_os && !old_os->readOnly && new_os->readOnly){
      terminateStateOnError(state,
                            "memory error: object read only in new version",
                            "new.readonly.err");
    } else if (old_os && old_os->readOnly && !new_os->readOnly){
      terminateStateOnError(state,
                            "memory error: object read only in old version",
                            "old.readonly.err");
    } else {
      //add Global Variable into concernArgsAndGVals
      StackFrame &sf=state.stack.back();
      if(state.stack.back().concernFlag){
          if(old_mo && old_mo->isGlobal){
	      // || sf.concernArgsAndGVals.find(old_value)!=sf.concernArgsAndGVals.end()){
                state.stack.back().concernArgsAndGVals[old_addr]=false;
                state.stack.back().concernArgsAndGValsExpr[old_addr]=type;
	  }
          if(new_mo && new_mo->isGlobal){
	      //||sf.concernArgsAndGVals.find(new_value)!=sf.concernArgsAndGVals.end()){
                state.stack.back().concernArgsAndGVals[new_addr]=false;
                state.stack.back().concernArgsAndGValsExpr[new_addr]=type;
          }
      } 
      /*
      if(state.stack.back().kf->function->getName().str() == "__user_main"){
                state.stack.back().concernArgsAndGVals[old_addr]=false;
                state.stack.back().concernArgsAndGValsExpr[old_addr]=type;
                state.stack.back().concernArgsAndGVals[new_addr]=false;
                state.stack.back().concernArgsAndGValsExpr[new_addr]=type;
      }
      if(old_mo->address == new_mo->address){
         ref<Expr> res_value=ShadowExpr::create(old_value,new_value);//zesti:only old_value ?
         ObjectState *wos = state.addressSpace.getWriteable(old_mo,old_os);
         wos->write(old_offset, res_value);
         // concernArgsAndGVals changed
         if(state.stack.back().concernFlag){
             std::map<const MemoryObject*,bool>::iterator mo_it=state.stack.back().concernArgsAndGVals.find(old_mo);
             if(mo_it!=state.stack.back().concernArgsAndGVals.end())
                 state.stack.back().concernArgsAndGVals[old_mo]=true;
         }
      }
      */
      /*
      else
      {
      */
     //questions
      if(old_mo){
         ObjectState *old_wos = state.addressSpace.getWriteable(old_mo,old_os);
         ref<Expr> prev_val=old_wos->read(old_offset,type);
         if(prev_val.isNull())
            prev_val=ConstantExpr::create(0,old_value->getWidth());
         if(prev_val->isContainShadow())
            prev_val=prev_val->findShadowExpr(1);
         if(old_value->isContainShadow())
            old_value=old_value->findShadowExpr(0);

         old_value=ShadowExpr::create(old_value,prev_val);
         old_wos->write(old_offset, old_value);
         if(state.stack.back().concernFlag){
             std::map<ref<Expr>,bool>::iterator mo_it=state.stack.back().concernArgsAndGVals.find(old_addr);
             if(mo_it!=state.stack.back().concernArgsAndGVals.end())
                 state.stack.back().concernArgsAndGVals[old_addr]=true;
                 state.stack.back().concernArgsAndGValsExpr[old_addr]=type;
         }
      // if(state.stack.back().kf->function->getName().str() == "__user_main"){
      //         state.stack.back().concernArgsAndGVals[old_addr]=true;
      //         state.stack.back().concernArgsAndGValsExpr[old_addr]=type;
      // }
      }

      if(new_mo){
         ObjectState *new_wos = state.addressSpace.getWriteable(new_mo,new_os);
         ref<Expr> prev_val=new_wos->read(new_offset,type);
         if(prev_val.isNull())
             prev_val=ConstantExpr::create(0,new_value->getWidth());
         if(prev_val->isContainShadow())
             prev_val=prev_val->findShadowExpr(0);
         if(new_value->isContainShadow())
             new_value=new_value->findShadowExpr(1);

         new_value=ShadowExpr::create(prev_val,new_value);
         new_wos->write(new_offset, new_value);
         if(state.stack.back().concernFlag){
             std::map<ref<Expr>,bool>::iterator mo_it=state.stack.back().concernArgsAndGVals.find(new_addr);
             if(mo_it!=state.stack.back().concernArgsAndGVals.end())
                 state.stack.back().concernArgsAndGVals[new_addr]=true;
                 state.stack.back().concernArgsAndGValsExpr[new_addr]=type;
         }
      // if(state.stack.back().kf->function->getName().str() == "__user_main"){
      //         state.stack.back().concernArgsAndGVals[new_addr]=true;
      //         state.stack.back().concernArgsAndGValsExpr[new_addr]=type;
      // }
      }
      //} // if oldaddress != newaddress
    } // if error or not
  } else {
        if(old_os){
          old_res = old_os->read(old_offset,type);
          if(old_res->isContainShadow())
              old_res=old_res->findShadowExpr(0);
          if (interpreterOpts.MakeConcreteSymbolic)
          {
              old_res = replaceReadWithSymbolic(state, old_res);
          }
        }
        if(new_os){
          new_res = new_os->read(new_offset,type);
          if(new_res->isContainShadow())
              new_res=new_res->findShadowExpr(1);
          if (interpreterOpts.MakeConcreteSymbolic)
          {
              new_res = replaceReadWithSymbolic(state, new_res);
          }
        }
        //ref<Expr> dif=EqExpr::create(old_res,new_res);
        ref<Expr> result=ShadowExpr::create(old_res,new_res);
        unsigned int numOp=target->inst->getNumOperands();
        for(unsigned int i=0;i<numOp;i++){
            llvm::Value *subOpe=target->inst->getOperand(i);
            if (llvm::Instruction *subInst = dyn_cast<llvm::Instruction>(subOpe)){
                if(subInst->getOpcode() == Instruction::GetElementPtr){
                    result->setIsPointer();
                } else {
                    const llvm::Type *val_type=subInst->getType();
                    unsigned int numSOp=subInst->getNumOperands();
                    for(unsigned int j=0;j<numSOp;j++){
                        const llvm::Type *subval_type=subInst->getOperand(j)->getType();
                        if(subval_type->isPointerTy())
                            result->setIsPointer();
                    }
                }
            } else if(llvm::User *uInst=dyn_cast<llvm::User>(subOpe)){
                const llvm::Type *val_type=uInst->getType();
                unsigned int numSOp=uInst->getNumOperands();
                for(unsigned int j=0;j<numSOp;j++){
                    const llvm::Type *subval_type=uInst->getOperand(j)->getType();
                    if(subval_type->isPointerTy())
                      result->setIsPointer();
                }
            }
        }
        bindLocal(target, state, result);
  } // read operation
}
//bupt use
std::vector<unsigned char>
Executor::readObjectAtAddress(ExecutionState &state, ref<Expr> addressExpr) {
        ObjectPair op;
        addressExpr = toUnique(state, addressExpr);
        ref<ConstantExpr> address = cast<ConstantExpr>(addressExpr);
        if (!state.addressSpace.resolveOne(address, op))
            assert(0 && "XXX out of bounds / multiple resolution unhandled");
        bool res;
        assert(solver->mustBeTrue(state, EqExpr::create(address,
                    op.first->getBaseExpr()), res) &&
                     res &&
                     "XXX interior pointer unhandled");
        const MemoryObject *mo = op.first;
        const ObjectState *os = op.second;

        char buf;
        std::vector<unsigned char> result;
        unsigned i;
        for (i = 0; i < mo->size; i++) {
            ref<Expr> cur = os->read8(i);
            cur = toUnique(state, cur);
            assert(isa<ConstantExpr>(cur) &&
                         "hit symbolic byte while reading concrete object");
            buf = cast<ConstantExpr>(cur)->getZExtValue(8);
            result.push_back(buf);
        }

        return result;
    }
void Executor::executeMakeSymbolic(ExecutionState &state,
                                   const MemoryObject *mo,
                                   const std::string &name) {
  // Create a new object state for the memory object (instead of a copy).
  if (!replayOut) {
    // Find a unique name for this array.  First try the original name,
    // or if that fails try adding a unique identifier.
    //bupt use
    std::vector<unsigned char> prevVal;
    if(BuptShadow)
    {
              prevVal = readObjectAtAddress(state,
                                    ConstantExpr::create(mo->address,
                                    Context::get().getPointerWidth()));
    }

    unsigned id = 0;
    std::string uniqueName = name;
    while (!state.arrayNames.insert(uniqueName).second) {
      uniqueName = name + "_" + llvm::utostr(++id);
    }
    const Array *array = Array::CreateArray(uniqueName, mo->size);
    bindObjectInState(state, mo, false, array);
    state.addSymbolic(mo, array);

    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it =
      seedMap.find(&state);
    if (it!=seedMap.end()) { // In seed mode we need to add this as a
                             // binding.
      for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
             siie = it->second.end(); siit != siie; ++siit) {
            SeedInfo &si = *siit;
            //bupt use
            if(BuptShadow){
                if(debug==1){
                    errs()<<"memoryobject: "<<mo->address<<"\n";
                    mo->allocSite->dump();
                    errs()<<"prevVal bind to bindings\n";
                    for(std::vector<unsigned char>::iterator vit=prevVal.begin(),vie=prevVal.end();vit!=vie;vit++){
                        errs()<<(*vit);
                    }
                    errs()<<"\n";
                }
                si.assignment.bindings[array] = prevVal;
            }
            else
            {
                KTestObject *obj = si.getNextInput(mo, NamedSeedMatching);
                if (!obj) {
                  if (ZeroSeedExtension) {
                    std::vector<unsigned char> &values = si.assignment.bindings[array];
                    values = std::vector<unsigned char>(mo->size, '\0');
                  } else if (!AllowSeedExtension) {
                    terminateStateOnError(state,
                              "ran out of inputs during seeding",
                              "user.err");
                    break;
                  }
                } else {
                  if (obj->numBytes != mo->size &&
                      ((!(AllowSeedExtension || ZeroSeedExtension)
                    && obj->numBytes < mo->size) ||
                       (!AllowSeedTruncation && obj->numBytes > mo->size))) {
                    std::stringstream msg;
                    msg << "replace size mismatch: "
                    << mo->name << "[" << mo->size << "]"
                    << " vs " << obj->name << "[" << obj->numBytes << "]"
                    << " in test\n";

                    terminateStateOnError(state,
                              msg.str(),
                              "user.err");
                    break;
                  } else {
                    std::vector<unsigned char> &values = si.assignment.bindings[array];
                    values.insert(values.begin(), obj->bytes,
                          obj->bytes + std::min(obj->numBytes, mo->size));
                    if (ZeroSeedExtension) {
                      for (unsigned i=obj->numBytes; i<mo->size; ++i)
                    values.push_back('\0');
                    }
                  }
                }
            }
        }
    }
  } else {
    ObjectState *os = bindObjectInState(state, mo, false);
    if (replayPosition >= replayOut->numObjects) {
      terminateStateOnError(state, "replay count mismatch", "user.err");
    } else {
      KTestObject *obj = &replayOut->objects[replayPosition++];
      if (obj->numBytes != mo->size) {
        terminateStateOnError(state, "replay size mismatch", "user.err");
      } else {
        for (unsigned i=0; i<mo->size; i++)
          os->write8(i, obj->bytes[i]);
      }
    }
  }
}

/***/

void Executor::runFunctionAsMain(Function *f,
                 int argc,
                 char **argv,
                 char **envp) {
  std::vector<ref<Expr> > arguments;

  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);

  MemoryObject *argvMO = 0;

  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?

  int envc;
  for (envc=0; envp[envc]; ++envc) ;

  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  if (ai!=ae) {
    arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));

    if (++ai!=ae) {
      argvMO = memory->allocate((argc+1+envc+1+1) * NumPtrBytes, false, true,
                                f->begin()->begin());

      arguments.push_back(argvMO->getBaseExpr());

      if (++ai!=ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.push_back(Expr::createPointer(envp_start));

        if (++ai!=ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }

  ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);

  if (pathWriter)
    state->pathOS = pathWriter->open();
  if (symPathWriter)
    state->symPathOS = symPathWriter->open();


  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
    bindArgument(kf, i, *state, arguments[i]);

  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*state, argvMO, false);

    for (int i=0; i<argc+1+envc+1+1; i++) {
      if (i==argc || i>=argc+1+envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);

        MemoryObject *arg = memory->allocate(len+1, false, true, state->pc->inst);
        ObjectState *os = bindObjectInState(*state, arg, false);
        for (j=0; j<len+1; j++)
          os->write8(j, s[j]);

        // Write pointer to newly allocated and initialised argv/envp c-string
        argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
      }
    }
  }

  initializeGlobals(*state);

  processTree = new PTree(state);
  state->ptreeNode = processTree->root;
  Function *kchg=kmodule->module->getFunction("klee_change");
  std::set<Function*> callChain;
  getCallers(kchg,callChain,1); //get all concerned function: function directly/indirectly calls "klee_change"
  run(*state);
  delete processTree;
  processTree = 0;

  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager();

  globalObjects.clear();
  globalAddresses.clear();

  if (statsTracker)
    statsTracker->done();
}

void Executor::getCallers(Function *fn,std::set<Function*> &callChain,int level){
  callChain.insert(fn);
//errs()<<"collect all function calls to function *"<<fn->getName().data()<<"*\n";
  for(Value::use_iterator it=fn->use_begin(),ie=fn->use_end();it!=ie;it++){
      if(llvm::Instruction::classof(*it)){
        //errs()<<"Instruction: ";
        //(*it)->dump();
        //errs()<<"uses function *"<<fn->getName().data()<<"*\n";
          BasicBlock *pubb=cast<Instruction>(*it)->getParent();
          Function *pufn=pubb->getParent();
          if(callChain.find(pufn)==callChain.end()){
            //errs()<<"Function *"<<pufn->getName().data()<<"* calls function *"<<fn->getName().data()<<"*\n";
              concernFunction.insert(make_pair(pufn->getName().str(),level));
              getCallers(pufn,callChain,level+1);
          }
    }
}

}
unsigned Executor::getPathStreamID(const ExecutionState &state) {
  assert(pathWriter);
  return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
  assert(symPathWriter);
  return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res,
                                Interpreter::LogType logFormat) {

  std::ostringstream info;

  switch (logFormat) {
  case STP: {
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    char *log = solver->getConstraintLog(query);
    res = std::string(log);
    free(log);
  } break;

  case KQUERY: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprPPrinter::printConstraints(info, state.constraints);
    res = info.str();
  } break;

  case SMTLIB2: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprSMTLIBPrinter printer;
    printer.setOutput(info);
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    printer.setQuery(query);
    printer.generateOutput();
    res = info.str();
  } break;

  default:
    klee_warning("Executor::getConstraintLog() : Log format not supported!");
  }
}

bool Executor::getSymbolicSolution(const ExecutionState &state,
                                   std::vector<
                                   std::pair<std::string,
                                   std::vector<unsigned char> > >
                                   &res) {
  solver->setTimeout(coreSolverTimeout);

  ExecutionState tmp(state);

  // Go through each byte in every test case and attempt to restrict
  // it to the constraints contained in cexPreferences.  (Note:
  // usually this means trying to make it an ASCII character (0-127)
  // and therefore human readable. It is also possible to customize
  // the preferred constraints.  See test/Features/PreferCex.c for
  // an example) While this process can be very expensive, it can
  // also make understanding individual test cases much easier.
  for (unsigned i = 0; i != state.symbolics.size(); ++i) {
    const MemoryObject *mo = state.symbolics[i].first;
    std::vector< ref<Expr> >::const_iterator pi =
      mo->cexPreferences.begin(), pie = mo->cexPreferences.end();
    for (; pi != pie; ++pi) {
      bool mustBeTrue;
      // Attempt to bound byte to constraints held in cexPreferences
      bool success ;
      if(BuptShadow)
        success= solver->mustBeTrue(tmp, Expr::createIsZero(*pi),mustBeTrue,false);
      else
        success= solver->mustBeTrue(tmp, Expr::createIsZero(*pi),mustBeTrue);
      // If it isn't possible to constrain this particular byte in the desired
      // way (normally this would mean that the byte can't be constrained to
      // be between 0 and 127 without making the entire constraint list UNSAT)
      // then just continue on to the next byte.
      if (!success) break;
      // If the particular constraint operated on in this iteration through
      // the loop isn't implied then add it to the list of constraints.
      if (!mustBeTrue) tmp.addConstraint(*pi);
    }
    if (pi!=pie) break;
  }

  std::vector< std::vector<unsigned char> > values;
  std::vector<const Array*> objects;
  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    objects.push_back(state.symbolics[i].second);
  bool success = solver->getInitialValues(tmp, objects, values);
  solver->setTimeout(0);
  if (!success) {
    klee_warning("unable to compute initial values (invalid constraints?)!");
    ExprPPrinter::printQuery(llvm::errs(), state.constraints,
                             ConstantExpr::alloc(0, Expr::Bool));
    return false;
  }
    //bupt use
         //fix bad test cases
         int fix=0;
         for(int fix_count=0;fix_count<state.symbolics.size();fix_count++)
         {
             if("argv"==state.symbolics[fix_count].first->name)
             {
                 char* init_value=buf_for_argv[fix++];
                 for(int counter=0;counter<values[fix_count].size();counter++)
                 {
                     if(values[fix_count][counter]==' ')
                    values[fix_count][counter]=init_value[counter];
                 }
             }
         }

  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    res.push_back(std::make_pair(state.symbolics[i].first->name, values[i]));
  return true;
}

void Executor::getCoveredLines(const ExecutionState &state,
                               std::map<const std::string*, std::set<unsigned> > &res) {
  res = state.coveredLines;
}

void Executor::doImpliedValueConcretization(ExecutionState &state,
                                            ref<Expr> e,
                                            ref<ConstantExpr> value) {
  abort(); // FIXME: Broken until we sort out how to do the write back.

  if (DebugCheckForImpliedValues)
    ImpliedValue::checkForImpliedValues(solver->solver, e, value);

  ImpliedValueList results;
  ImpliedValue::getImpliedValues(e, value, results);
  for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
       it != ie; ++it) {
    ReadExpr *re = it->first.get();

    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
      // FIXME: This is the sole remaining usage of the Array object
      // variable. Kill me.
      const MemoryObject *mo = 0; //re->updates.root->object;
      const ObjectState *os = state.addressSpace.findObject(mo);

      if (!os) {
        // object has been free'd, no need to concretize (although as
        // in other cases we would like to concretize the outstanding
        // reads, but we have no facility for that yet)
      } else {
        assert(!os->readOnly &&
               "not possible? read only object with static read?");
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        wos->write(CE, it->second);
      }
    }
  }
}

Expr::Width Executor::getWidthForLLVMType(LLVM_TYPE_Q llvm::Type *type) const {
  return kmodule->targetData->getTypeSizeInBits(type);
}

///

Interpreter *Interpreter::create(const InterpreterOptions &opts,
                                 InterpreterHandler *ih) {
  return new Executor(opts, ih);
}

//bupt use

void Executor::chainCreate(BasicBlock *root, BasicBlock* end, CFGPath &currentPath,int mode){
    size_t direct = 0;
    int NumKids = 0;
    llvm::Function * pFunc=root->getParent();
    BasicBlock* RBA=root;
    BasicBlock* EBA=end;
    for(llvm::succ_iterator SI=succ_begin(root);SI!=succ_end(root);SI++){
        NumKids++;
    }
    // mode == 1 Collect all visited BasicBlock from *root* to *end*
    // mode == 2 Check whether *root* is linked to *end*
    // mode == 3 Collect all the leaves nodes
    if(mode == 1)
        currentPath.blockVisited.insert(RBA);
    if(RBA == EBA){
        if( mode == 2)
            currentPath.linked=true;
        return;
    } else if (NumKids == 0 ){
        if( mode == 3 )
            currentPath.exitBBs.insert(root);
        return;
    }
    for(llvm::succ_iterator SI=succ_begin(root);SI!=succ_end(root);SI++,direct++){
        CFGPath::BBIndex RIdx=std::make_pair(RBA,direct);// XXX: could be unified, use node pair as BBIndex, not the direct id
        if(currentPath.visited[RIdx]){
            // skip loop point
            continue;
        } else {
            currentPath.visited[RIdx]=true;
            chainCreate(*SI,end,currentPath,mode);
            // Check whether contain path between root and end
            currentPath.visited[RIdx]=false;
            if( currentPath.linked && mode == 2){
                    return;
            }
        }
    }
}

void Executor::chainCreate(ExecutionState::condsWithMG &coveredMap, BasicBlock *root, BasicBlock* end, CFGPath &currentPath, CFGPath &coveredBBs, CFGPath &mgBBs){
    size_t direct = 0;
    int NumKids = 0;
    llvm::Function * pFunc=root->getParent();
    BasicBlock* RBA=root;
    BasicBlock* EBA=end;
    for(llvm::succ_iterator SI=succ_begin(root);SI!=succ_end(root);SI++){
        NumKids++;
    }
    // Collect all covered path edges between *root* and *end*
    if(RBA == EBA){
        return;
    } else if (NumKids == 0 ){
        return;
    } else if( NumKids == 1 ){
        llvm::succ_iterator SI=succ_begin(root);
        chainCreate(coveredMap,*SI,end,currentPath,coveredBBs,mgBBs);
    }
    for(llvm::succ_iterator SI=succ_begin(root);SI!=succ_end(root);SI++,direct++){
        CFGPath::BBIndex RIdx=std::make_pair(RBA,direct);
        BasicBlock* SBA=*SI;
        if(coveredBBs.visited[RIdx] || mgBBs.visited[RIdx]){
            if(currentPath.visited[RIdx]){
                continue;
            } else {
                coveredMap[std::make_pair(RBA,SBA)]=true;
                currentPath.visited[RIdx]=true;
                chainCreate(coveredMap,*SI,end,currentPath,coveredBBs,mgBBs);
                // Check whether contain path between root and end
                currentPath.visited[RIdx]=false;
            }
        } else {
            coveredMap[std::make_pair(RBA,SBA)]=false;
        }
    }
}

unsigned Executor::getBlockHeight(BasicBlock *start, std::map<BasicBlock*, unsigned> &BlockHeight, std::set<BasicBlock*> &visitedBlock){
    if(succ_begin(start)==succ_end(start)){
        // height of leaf node is 1
        BlockHeight[start]=1;
        return 1;
    }

    if(BlockHeight.find(start)!=BlockHeight.end()){
        return BlockHeight[start];
    }
    visitedBlock.insert(start);
    unsigned childMaxHeight=0;

    for(succ_iterator SI=succ_begin(start),E=succ_end(start);SI != E; SI++){
        if(visitedBlock.find(*SI)!=visitedBlock.end()){
            childMaxHeight = childMaxHeight >  1 ? childMaxHeight : 1;
            //if child is loop point, assume the child height is 1
        } else {
            unsigned child = getBlockHeight(*SI,BlockHeight,visitedBlock);
            childMaxHeight = childMaxHeight > child ? childMaxHeight : child;
        }
    }

    BlockHeight[start]=childMaxHeight+1;
    // height of inner node is the max height of children add 1
    visitedBlock.erase(start);
    return BlockHeight[start];
}

void Executor::findCoveredBB(BasicBlock *root,CFGPath &currentPath){
    // collect all the reachable path range between *root* and *entry*
    std::queue<BasicBlock*> unvisited;
    std::set<BasicBlock*> visited;
    unvisited.push(root);
    while(!unvisited.empty()){
        BasicBlock *current=unvisited.front();

        for(llvm::pred_iterator PI=pred_begin(current),PE=pred_end(current);PI!=PE;PI++){
            if(visited.find(*PI)!=visited.end())
                continue;
            unvisited.push(*PI);
        }
        if(visited.find(current)!=visited.end()){
            unvisited.pop();
            continue;
        }
        for(llvm::pred_iterator PI=pred_begin(current),PE=pred_end(current);PI!=PE;PI++){
            size_t p_direct=0;
            for(llvm::succ_iterator SI=succ_begin(*PI),SE=succ_end(*PI);SI!=SE;SI++,p_direct++){
                if(*SI==current){
                    BasicBlock* PBA=*PI;
                    CFGPath::BBIndex reachDirect=std::make_pair(PBA,p_direct);
                    currentPath.visited[reachDirect]=true;
                    break;
                }
            }
        }
        visited.insert(current);
        unvisited.pop();
    }
}

BasicBlock* Executor::uniqueMergePoint(BasicBlock *mgbb){
    // update unconditional br terminated merge point *mgbb* to the latest conditonal br terminated BasicBlock
    BasicBlock *Node=mgbb;
    size_t numKids=0;
    std::set<BasicBlock*> visited;
    for(llvm::succ_iterator SI=succ_begin(Node),E=succ_end(Node);SI!=E;SI++){
        numKids++;
    }
    if(numKids == 0){
        return Node;
    }
    while(numKids == 1){
        if(visited.find(Node)!=visited.end())
            break;
        BasicBlock* succ=*(succ_begin(Node));
        numKids=0;
        for(llvm::succ_iterator SI=succ_begin(succ),E=succ_end(succ);SI!=E;SI++){
            numKids++;
        }
        visited.insert(Node);
        Node=succ;
    }
    return Node;
}

bool Executor::computeMerge(ExecutionState &state,llvm::BasicBlock *left,    llvm::BasicBlock *right){
    std::set<llvm::BasicBlock*> MergePointSet;
    std::set<llvm::BasicBlock*> leftSucc,rightSucc;
    std::map<BasicBlock*,unsigned> BlockHeight;
    std::set<BasicBlock*>visitedBlock;
    CFGPath exitBBSet;
    CFGPath coveredBBs;
    CFGPath leftPath;
    CFGPath rightPath;
    Function* pFunc=left->getParent();
    llvm::Function::iterator endBB=pFunc->back();
    state.retPoint=endBB;
    chainCreate(left,endBB,leftPath,1);
    chainCreate(right,endBB,rightPath,1);
    // collect all the common BasicBlocks from the left descendants set and right descendants set
    // in MergePointSet
    std::set_intersection(leftPath.blockVisited.begin(),leftPath.blockVisited.end(),
                            rightPath.blockVisited.begin(),rightPath.blockVisited.end(),
                            std::inserter(MergePointSet,MergePointSet.begin()));
    // remove conservative merge point endBB
    MergePointSet.erase(endBB);

    // check left/right itself is merge point or not
    if(leftPath.blockVisited.find(right)!=leftPath.blockVisited.end()){
        MergePointSet.insert(right);
    }
    else if(rightPath.blockVisited.find(left)!=rightPath.blockVisited.end()){
        MergePointSet.insert(left);
    }
    if(MergePointSet.size() < 1)
        return false;


    for(std::set<BasicBlock*>::iterator it=MergePointSet.begin(),ie=MergePointSet.end();it!=ie;it++){
        int count=0;
        BasicBlock *mgBA=uniqueMergePoint(*it);
        if(mgBA != (*it)){
            MergePointSet.erase(it);
            MergePointSet.insert(mgBA);
        }
    }

    std::set<BasicBlock*> removedMG;
    std::set<BasicBlock*> updateMergeSet;
    // remove redundant merge point candidates
    // the remove rule is: any path reach one candidate must pass another candidate, the candidate is redundant
    for(std::set<BasicBlock*>::iterator it=MergePointSet.begin(),ie=MergePointSet.end();it!=ie;it++){
        if(removedMG.find(*it)!=removedMG.end())
            continue;
        BasicBlock *start=(*it);
        std::set<BasicBlock*> rightPreds;
        std::set<BasicBlock*> multiSuccPreds;
        std::set<BasicBlock*> tmpSet;
        CFGPath Succs;
        for(llvm::pred_iterator PI=pred_begin(start),E=pred_end(start);PI!=E;PI++){
            if(rightPath.blockVisited.find(*PI)!=rightPath.blockVisited.end()){
                rightPreds.insert(*PI);
            }
        } // get the pred in right sub-graph
        for(std::set<BasicBlock*>::iterator bit=rightPreds.begin(),bie=rightPreds.end();bit!=bie;bit++){
            int numKids=0;
            for(llvm::succ_iterator sit=succ_begin(*bit),sie=succ_end(*bit);sit!=sie;sit++)
                numKids++;
            if(numKids>1){
                multiSuccPreds.insert(*bit);
            }
        }
        chainCreate(start,endBB,Succs,1);
        Succs.blockVisited.erase(start);
        /*std::set_intersection(Succs.blockVisited.begin(),Succs.blockVisited.end(),
                                MergePointSet.begin(),MergePointSet.end(),
                                std::inserter(tmpSet,tmpSet.begin()));*/
        for(std::set<BasicBlock*>::iterator it=Succs.blockVisited.begin(),ie=Succs.blockVisited.end();it!=ie;it++){
            if(MergePointSet.find(*it)!=MergePointSet.end())
                tmpSet.insert(*it);
        }
        for(std::set<BasicBlock*>::iterator bit=multiSuccPreds.begin(),bie=multiSuccPreds.end();bit!=bie;bit++){
            for(llvm::succ_iterator PI=succ_begin(start),E=succ_end(start);PI!=E;PI++){
                if(tmpSet.find(*PI)!=tmpSet.end()){
                    tmpSet.erase(*PI);
                }
            } // get the pred in right sub-graph
        }
        unsigned curHeight=getBlockHeight(start,BlockHeight,visitedBlock);
        for(std::set<BasicBlock*>::iterator bit=tmpSet.begin(),bie=tmpSet.end();bit!=bie;){
            if(getBlockHeight(*bit,BlockHeight,visitedBlock) > curHeight){
                std::set<BasicBlock*>::iterator tmp=bit;
                bit++;
                tmpSet.erase(tmp);
            } else
                bit++;
        }
        removedMG.insert(tmpSet.begin(),tmpSet.end());
    }
    /*
      std::set_difference(removedMG.begin(),removedMG.end(),
            MergePointSet.begin(),MergePointSet.end(),
            std::inserter(updateMergeSet,updateMergeSet.end()));
            */
    for(std::set<BasicBlock*>::iterator it=MergePointSet.begin(),ie=MergePointSet.end();it!=ie;it++){
        if(removedMG.find(*it)==removedMG.end())
            updateMergeSet.insert(*it);
    }
    /* XXX: aims to deal with two linked merge point;
     * discarded
     * now we generate at least one state for each merge point
    for(std::set<BasicBlock*>::iterator it=updateMergeSet.begin(),ie=updateMergeSet.end();it!=ie;it++){
        if(state.mergeSet.find(*it)!=state.mergeSet.end())
            continue;
        int count=0;
        BasicBlock *start=(*it);
        state.mergeSet[(*it)]=false;
        for(std::set<BasicBlock*>::iterator itt=updateMergeSet.begin();itt!=ie;itt++){
            if(state.mergeSet.find(*itt)!=state.mergeSet.end())
                continue;
            CFGPath linkedMGs;
            BasicBlock *end=(*itt);
            chainCreate(start,end,linkedMGs,2);
            if(linkedMGs.linked)
                count++;
            if(count>1){
                state.mergeSet[(*it)]=true;
                break;
            }
        }
    }
    */
    if(debug==1){
        for(std::set<BasicBlock*>::iterator it=updateMergeSet.begin(),ie=updateMergeSet.end();it!=ie;it++){
            (*it)->dump();
        }
    }


    chainCreate(right,endBB,exitBBSet,3);
    for(std::set<BasicBlock*>::iterator it=exitBBSet.exitBBs.begin(),ie=exitBBSet.exitBBs.end();it!=ie;it++){
        findCoveredBB((*it),coveredBBs);
    }

    for(std::set<BasicBlock*>::iterator it=updateMergeSet.begin(),ie=updateMergeSet.end();it!=ie;it++){
        BasicBlock* mgbb=(*it);
        CFGPath mgCoveredBBs;
        state.mergeSet[mgbb]=false;
        findCoveredBB(mgbb,mgCoveredBBs);
        chainCreate(state.new_pathSequential[(*it)],right,mgbb,rightPath,coveredBBs,mgCoveredBBs);
    }
    return true;
}

bool Executor::handlePointer(ref<Expr> value, std::map <const MemoryObject*, std::vector< ref<Expr> > > &record, std::set<const MemoryObject*> &allRelatedMems,ExecutionState &state, bool tc, int stage)
{
    bool IsShadowed=false;
    ObjectPair op;
    bool resolve_success;
    bool result=state.addressSpace.resolveOne(state,solver,value,op,resolve_success);
    if(result && resolve_success)
    {
           allRelatedMems.insert(op.first);
           const MemoryObject *aMO=op.first;
           const ObjectState *aOS=op.second;
           ObjectState *nor_wos=state.addressSpace.getWriteable(aMO,aOS);
           if(debug_pointer==1){
               errs() << "value "<<value
                   << " width "<<value->getWidth()<<" found "
                   << "mo "<<aMO->address<< "\n";
               aMO->allocSite->dump();
               errs() <<"value in mo:\n";
               for (unsigned i=0; i<aMO->size; i++) {
                   ref<Expr> av = nor_wos->read8(i);
                   errs()<<av<<" ";
               }
               errs()<<"\n";
               errs()<< "-------- End value dump ------------\n";
           }
           ref<Expr> offset=aMO->getOffsetExpr(value);
           ref<Expr> expr,old_expr,new_expr;
           //unsigned size=aMO->size*8;
           if(aMO->size <= 8 && aMO->size != 1 && aMO->size != 2 && aMO->size !=4  && aMO->size != 8)
               return IsShadowed;
           if(isX86_64){
                expr=nor_wos->read(offset,Expr::Int64);//XXX: expr maybe a pointer in X86_64 machine
           } else {
                expr=nor_wos->read(offset,Expr::Int32);//XXX: expr maybe a pointer in X86_32 machine
           }
           if(state.isUE()){
                if(expr->isPointer()){
                    if(expr->isContainShadow()){
                       if(stage==1){
                           // deal with the old-version expression in shadow expression
                        IsShadowed=handlePointer(expr->findShadowExpr(0),record,allRelatedMems,state,tc,stage);
                       } else if(stage==2){
                           // deal with the new-version expression in shadow expression
                        IsShadowed=handlePointer(expr->findShadowExpr(1),record,allRelatedMems,state,tc,stage);
                       }
                   } else {
                        IsShadowed=handlePointer(expr,record,allRelatedMems,state,tc,stage);
                   }
                } else {
                   if(tc)
                   {
                       ref<Expr> old_value,new_value;
                       for (unsigned i=0; i<aMO->size; i++) {
                            unsigned idx = Context::get().isLittleEndian() ? i : (aMO->size - i - 1);
                            ref<Expr> Byte = nor_wos->read8(idx);
                            ref<Expr> old_Byte,new_Byte;
                            if(Byte->isContainShadow()){
                               old_Byte=Byte->findShadowExpr(0);
                               new_Byte=Byte->findShadowExpr(1);
                               old_value = i ? ConcatExpr::create(old_Byte, old_value) : old_Byte;
                               new_value = i ? ConcatExpr::create(new_Byte, new_value) : new_Byte;
                            } else {
                               old_value = i ? ConcatExpr::create(Byte, old_value) : Byte;
                               new_value = i ? ConcatExpr::create(Byte, new_value) : Byte;
                            }
                       }
                       ref<Expr> dif_arg=NeExpr::create(old_value, new_value);
                       bool mustBeFalse;
                       bool success=solver->mustBeFalse(state, dif_arg, mustBeFalse, false);
                       assert(success && "FIXME");
                       if(!mustBeFalse){
                           //generate test case
                           state.needTestCase=true;
                           state.ctlordata=true;
                           interpreterHandler->processTestCase(state,0,0);
                           state.needTestCase=false;
                           state.ctlordata=false;
                       }
                   }
                   for (unsigned i=0; i<aMO->size; i++) {
                       ref<Expr> av = nor_wos->read8(i);
                       if(av->isContainShadow()){
                               if(stage==1){
                                   record[aMO].push_back(av->findShadowExpr(1));
                                   nor_wos->write(i,av->findShadowExpr(0));
                               } else if(stage==2){
                                   record[aMO].push_back(av->findShadowExpr(0));
                                   nor_wos->write(i,av->findShadowExpr(1));
                               }
                               IsShadowed=true;
                       } else {
                            record[aMO].push_back(av);
                       }
                   }
                }
           } else if (state.isSPEO()){
                if(expr->isPointer()){
                    if(expr->isContainShadow()){
                        IsShadowed=handlePointer(expr->findShadowExpr(0),record,allRelatedMems,state,tc,stage);
                   } else {
                        IsShadowed=handlePointer(expr,record,allRelatedMems,state,tc,stage);
                   }
                } else {
                   for (unsigned i=0; i<aMO->size; i++) {
                       ref<Expr> av = nor_wos->read8(i);
                       if(av->isContainShadow()){
                            nor_wos->write(i,av->findShadowExpr(0));
                       }
                   }
                }
           } else {
                if(expr->isPointer()){
                    if(expr->isContainShadow()){
                        IsShadowed=handlePointer(expr->findShadowExpr(1),record,allRelatedMems,state,tc,stage);
                   } else {
                        IsShadowed=handlePointer(expr,record,allRelatedMems,state,tc,stage);
                   }
                } else {
                   for (unsigned i=0; i<aMO->size; i++) {
                       ref<Expr> av = nor_wos->read8(i);
                       if(av->isContainShadow()){
                            nor_wos->write(i,av->findShadowExpr(1));
                       }
                   }
                }
           }
    }
    return IsShadowed;
}

void Executor::normalReadOrWrite(ExecutionState &state,
        bool isWrite,
        ref<Expr> offset,
        Expr::Width type,
        ref<Expr> address,
        ref<Expr> value,
        KInstruction *target,
        const MemoryObject *mo,
        const ObjectState *os) {
    if (isWrite) {
      StackFrame &sf=state.stack.back();
      if (os->readOnly) {
        terminateStateOnError(state,
                              "memory error: object read only",
                              "readonly.err");
      } else {
              //add Global Variable into concernArgsAndGVals
              if(sf.concernFlag){
                  if(mo->isGlobal){
		      //sf.concernArgsAndGVals.find(value)!=sf.concernArgsAndGVals.end()){
                        sf.concernArgsAndGVals[address]=false;
                        sf.concernArgsAndGVals[address]=type;
                  }
              } 
           // if(sf.kf->function->getName().str() == "__user_main"){
           //         sf.concernArgsAndGVals[address]=false;
           //         sf.concernArgsAndGVals[address]=type;
	   // }
              ObjectState *wos = state.addressSpace.getWriteable(mo, os);
              if(debug_mem==1){
                  errs()<<"Inst "<<state.prevPC->info->assemblyLine<<"@"<<state.prevPC->info->line<<": ";
                  state.prevPC->inst->dump();
                  errs()<<"written value:\n";
                  value->dump();
                  ref<Expr> result = wos->read(offset,type);
                  errs() << "previous value in mo "<<mo<<" address: "<<mo->address<<":\n";
                  result->dump();
                  errs()<< "-------- End write value dump ------------\n";
              }

              if( state.isSPEO() ){
                  if(value->isContainShadow()){
                     value=value->findShadowExpr(0);
                  }
              }
              else if(  state.isSPEN() ){
                  if(value->isContainShadow()){
                     value=value->findShadowExpr(1);
                  }
              }
              wos->write(offset, value);
              // concernArgsAndGVals changed
              if(state.stack.back().concernFlag){
                  std::map<ref<Expr>,bool>::iterator mo_it=state.stack.back().concernArgsAndGVals.find(address);
                  if(mo_it!=state.stack.back().concernArgsAndGVals.end())
                      state.stack.back().concernArgsAndGVals[address]=true;
                      state.stack.back().concernArgsAndGValsExpr[address]=type;
              } 
           // if(state.stack.back().kf->function->getName().str() == "__user_main"){
           //         state.stack.back().concernArgsAndGVals[address]=true;
           //         state.stack.back().concernArgsAndGValsExpr[address]=type;
	   // }

          } // normal write operation
    } else {
            ref<Expr> result = os->read(offset,type);
            if (interpreterOpts.MakeConcreteSymbolic)
                result = replaceReadWithSymbolic(state, result);
              if(debug_mem==1){
                  errs()<<"Inst "<<state.prevPC->info->assemblyLine<<"@"<<state.prevPC->info->line<<": ";
                  state.prevPC->inst->dump();
                  errs() << "read from state "<<&state<<" mo "<<mo<<" address: "<<mo->address<<":\n";
                  errs()<<"read result:\n";
                  result->dump();
                  errs()<< "-------- End read result dump ------------\n";
              }
            unsigned int numOp=target->inst->getNumOperands();
            for(unsigned int i=0;i<numOp;i++){
                llvm::Value *subOpe=target->inst->getOperand(i);
                if (llvm::Instruction *subInst = dyn_cast<llvm::Instruction>(subOpe)){
                    if(subInst->getOpcode() == Instruction::GetElementPtr){
                        result->setIsPointer();
                    } else {
                        const llvm::Type *val_type=subInst->getType();
                        unsigned int numSOp=subInst->getNumOperands();
                        for(unsigned int j=0;j<numSOp;j++){
                            const llvm::Type *subval_type=subInst->getOperand(j)->getType();
                            if(subval_type->isPointerTy())
                                result->setIsPointer();
                        }
                    }
                } else if(llvm::User *uInst=dyn_cast<llvm::User>(subOpe)){
                    const llvm::Type *val_type=uInst->getType();
                    unsigned int numSOp=uInst->getNumOperands();
                    for(unsigned int j=0;j<numSOp;j++){
                        const llvm::Type *subval_type=uInst->getOperand(j)->getType();
                        if(subval_type->isPointerTy())
                          result->setIsPointer();
                    }
                }
            }
            bindLocal(target, state, result);
    } // read operation
}

void Executor::detectDataDiv(ExecutionState &state, ref<Expr> value,unsigned size){
	std::string curr_funcName=state.stack.back().kf->function->getName().str();
	int cur_level=-1;
	std::map<std::string, int>::iterator cf=concernFunction.find(curr_funcName);
	if(cf!=concernFunction.end())
	     cur_level=cf->second;
	if(value->isPointer()){
		if(value->isContainShadow()){
		    ref<Expr> old_value=value->findShadowExpr(0);
		    ref<Expr> new_value=value->findShadowExpr(1);	
		    bool result_old,result_new;
		    ObjectPair op_old,op_new;
		    bool success_old = state.addressSpace.resolveOne(state, solver, old_value, op_old, result_old);
		    bool success_new = state.addressSpace.resolveOne(state, solver, new_value, op_new, result_new);
		    if(result_old && success_old && result_new && success_new){
			const MemoryObject *old_mo=op_old.first;
			const ObjectState *old_os=op_old.second;
			const MemoryObject *new_mo=op_new.first;
			const ObjectState *new_os=op_new.second;
			ref<Expr> old_expr,new_expr;
			if(size){
				ref<Expr> offset=old_mo->getOffsetExpr(old_value);
				old_expr=old_os->read(offset,size);
				offset=new_mo->getOffsetExpr(new_value);
				new_expr=new_os->read(offset,size);
			} else {
				old_expr=old_os->read(0,old_mo->size);
				new_expr=new_os->read(0,new_mo->size);
			}
			if(old_expr->isContainShadow()) old_expr=old_expr->findShadowExpr(0);
			if(new_expr->isContainShadow()) new_expr=new_expr->findShadowExpr(1);
			if(old_expr->isPointer() && new_expr->isPointer()){
				ref<Expr> re_value=ShadowExpr::create(old_expr,new_expr);
				detectDataDiv(state,re_value);
			} else if(old_expr->getWidth() == new_expr->getWidth()){
			    ref<Expr> dif_expr=NeExpr::create(old_expr, new_expr);
			    bool mustBeFalse;
			    bool success=solver->mustBeFalse(state, dif_expr, mustBeFalse, false);
			    assert(success && "Unhandled\n");
			    if(!mustBeFalse)
			    {
				state.needTestCase=true;
				state.ctlordata=true;
				if(old_expr->isCtrlAffected() || new_expr->isCtrlAffected())
				    state.ctlAffected=true;
				std::string MsgString;
				llvm::raw_string_ostream msg(MsgString);
				msg << " Data Divergence Founded in Function: "<<curr_funcName<<" level: "<<cur_level<<"\n";
				op_old.first->getAllocInfo(MsgString);
				op_new.first->getAllocInfo(MsgString);
				msg << "Stack: \n";
				state.dumpStack(msg);
				state.divmsg=msg.str();
				createTestCaseButNoTerminate(state);
			    }
			} else {
			    ref<Expr> dif_value=NeExpr::create(old_value, new_value);
			    bool mustBeFalse;
			    bool success=solver->mustBeFalse(state, dif_value, mustBeFalse, false);
			    assert(success && "Unhandled\n");
			    if(!mustBeFalse)
			    {
				state.needTestCase=true;
				state.ctlordata=true;
				if(old_value->isCtrlAffected() || new_value->isCtrlAffected())
				    state.ctlAffected=true;
				std::string MsgString;
				llvm::raw_string_ostream msg(MsgString);
				msg << " Data Divergence Founded in Function: "<<curr_funcName<<" level: "<<cur_level<<"\n";
				op_old.first->getAllocInfo(MsgString);
				op_new.first->getAllocInfo(MsgString);
				msg << "Stack: \n";
				state.dumpStack(msg);
				state.divmsg=msg.str();
				createTestCaseButNoTerminate(state);
			    }

			}
		    } else {
			    ref<Expr> dif_value=NeExpr::create(old_value, new_value);
			    bool mustBeFalse;
			    bool success=solver->mustBeFalse(state, dif_value, mustBeFalse, false);
			    assert(success && "Unhandled\n");
			    if(!mustBeFalse)
			    {
				state.needTestCase=true;
				state.ctlordata=true;
				if(old_value->isCtrlAffected() || new_value->isCtrlAffected())
				    state.ctlAffected=true;
				std::string MsgString;
				llvm::raw_string_ostream msg(MsgString);
				msg << " Data Divergence Founded in Function: "<<curr_funcName<<" level: "<<cur_level<<"\n";
				msg << "Stack: \n";
				state.dumpStack(msg);
				state.divmsg=msg.str();
				createTestCaseButNoTerminate(state);
			    }
		    }
		} else {
		    bool result;
		    ObjectPair op;
		    ref<Expr> expr;
		    bool success = state.addressSpace.resolveOne(state, solver, value, op, result);
		    if(result && success){
			const MemoryObject *mo=op.first;
			const ObjectState *os=op.second;
			if(size){
				ref<Expr> offset=mo->getOffsetExpr(value);
				expr=os->read(offset,size);
			} else {
				expr=os->read(0,mo->size);
			}
			if(expr->isPointer())
				detectDataDiv(state,expr);	
		    }
		}
	} else if(value->isContainShadow()){
	    ref<Expr> old_value=value->findShadowExpr(0);
	    ref<Expr> new_value=value->findShadowExpr(1);	
	    ref<Expr> dif_value=NeExpr::create(old_value, new_value);
	    bool mustBeFalse;
	    bool success=solver->mustBeFalse(state, dif_value, mustBeFalse, false);
	    assert(success && "Unhandled\n");
	    if(!mustBeFalse)
	    {
		state.needTestCase=true;
		state.ctlordata=true;
		if(old_value->isCtrlAffected() || new_value->isCtrlAffected())
		    state.ctlAffected=true;
		std::string MsgString;
		llvm::raw_string_ostream msg(MsgString);
		msg << " Data Divergence Founded in Function: "<<curr_funcName<<" level: "<<cur_level<<"\n";
		//msg << old_value <<"\n" << new_value <<"\n";
		msg << "Stack: \n";
		state.dumpStack(msg);
		state.divmsg=msg.str();
		createTestCaseButNoTerminate(state);
	    }
	} 
}
