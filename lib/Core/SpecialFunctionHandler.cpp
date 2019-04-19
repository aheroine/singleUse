//===-- SpecialFunctionHandler.cpp ----------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Common.h"

#include "Memory.h"
#include "SpecialFunctionHandler.h"
#include "TimingSolver.h"

#include "klee/ExecutionState.h"

#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/Debug.h"

#include "Executor.h"
#include "MemoryManager.h"

#include "klee/CommandLine.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Module.h"
#else
#include "llvm/Module.h"
#endif
#include "llvm/ADT/Twine.h"

#include <errno.h>

using namespace llvm;
using namespace klee;

extern bool debug;
namespace {
  cl::opt<bool>
  ReadablePosix("readable-posix-inputs",
            cl::init(false),
            cl::desc("Prefer creation of POSIX inputs (command-line arguments, files, etc.) with human readable bytes. "
                     "Note: option is expensive when creating lots of tests (default=false)"));
}


/// \todo Almost all of the demands in this file should be replaced
/// with terminateState calls.

///



// FIXME: We are more or less committed to requiring an intrinsic
// library these days. We can move some of this stuff there,
// especially things like realloc which have complicated semantics
// w.r.t. forking. Among other things this makes delayed query
// dispatch easier to implement.
static SpecialFunctionHandler::HandlerInfo handlerInfo[] = {
#define add(name, handler, ret) { name, \
                                  &SpecialFunctionHandler::handler, \
                                  false, ret, false }
#define addDNR(name, handler) { name, \
                                &SpecialFunctionHandler::handler, \
                                true, false, false }
  addDNR("__assert_rtn", handleAssertFail),
  addDNR("__assert_fail", handleAssertFail),
  addDNR("_assert", handleAssert),
  addDNR("abort", handleAbort),
  addDNR("_exit", handleExit),
  { "exit", &SpecialFunctionHandler::handleExit, true, false, true },
  addDNR("klee_abort", handleAbort),
  addDNR("klee_silent_exit", handleSilentExit),
  addDNR("klee_report_error", handleReportError),

  add("calloc", handleCalloc, true),
  add("free", handleFree, false),
  add("klee_assume", handleAssume, false),
  add("klee_check_memory_access", handleCheckMemoryAccess, false),
  add("klee_get_valuef", handleGetValue, true),
  add("klee_get_valued", handleGetValue, true),
  add("klee_get_valuel", handleGetValue, true),
  add("klee_get_valuell", handleGetValue, true),
  add("klee_get_value_i32", handleGetValue, true),
  add("klee_get_value_i64", handleGetValue, true),
  add("klee_define_fixed_object", handleDefineFixedObject, false),
  add("klee_get_obj_size", handleGetObjSize, true),
  add("klee_get_errno", handleGetErrno, true),
  add("klee_is_symbolic", handleIsSymbolic, true),
  add("klee_make_symbolic", handleMakeSymbolic, false),
  add("klee_mark_global", handleMarkGlobal, false),
  add("klee_merge", handleMerge, false),
  add("klee_prefer_cex", handlePreferCex, false),
  add("klee_posix_prefer_cex", handlePosixPreferCex, false),
  add("klee_print_expr", handlePrintExpr, false),
  add("klee_print_range", handlePrintRange, false),
  add("klee_set_forking", handleSetForking, false),
  add("klee_stack_trace", handleStackTrace, false),
  add("klee_warning", handleWarning, false),
  add("klee_warning_once", handleWarningOnce, false),
  add("klee_alias_function", handleAliasFunction, false),
//bupt use
  add("klee_shadow_enabled", handleShadowEnabled, true),
  add("klee_get_concrete_value", handleGetConcreteValue,true),
  add("malloc", handleMalloc, true),
  add("realloc", handleRealloc, true),

  // operator delete[](void*)
  add("_ZdaPv", handleDeleteArray, false),
  // operator delete(void*)
  add("_ZdlPv", handleDelete, false),

  // operator new[](unsigned int)
  add("_Znaj", handleNewArray, true),
  // operator new(unsigned int)
  add("_Znwj", handleNew, true),

  // FIXME-64: This is wrong for 64-bit long...

  // operator new[](unsigned long)
  add("_Znam", handleNewArray, true),
  // operator new(unsigned long)
  add("_Znwm", handleNew, true),

  // clang -fsanitize=unsigned-integer-overflow
  add("__ubsan_handle_add_overflow", handleAddOverflow, false),
  add("__ubsan_handle_sub_overflow", handleSubOverflow, false),
  add("__ubsan_handle_mul_overflow", handleMulOverflow, false),
  add("__ubsan_handle_divrem_overflow", handleDivRemOverflow, false),

#undef addDNR
#undef add
};

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::begin() {
  return SpecialFunctionHandler::const_iterator(handlerInfo);
}

SpecialFunctionHandler::const_iterator SpecialFunctionHandler::end() {
  // NULL pointer is sentinel
  return SpecialFunctionHandler::const_iterator(0);
}

SpecialFunctionHandler::const_iterator& SpecialFunctionHandler::const_iterator::operator++() {
  ++index;
  if ( index >= SpecialFunctionHandler::size())
  {
    // Out of range, return .end()
    base=0; // Sentinel
    index=0;
  }

  return *this;
}

int SpecialFunctionHandler::size() {
	return sizeof(handlerInfo)/sizeof(handlerInfo[0]);
}

SpecialFunctionHandler::SpecialFunctionHandler(Executor &_executor)
  : executor(_executor) {}


void SpecialFunctionHandler::prepare() {
  unsigned N = size();

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);

    // No need to create if the function doesn't exist, since it cannot
    // be called in that case.

    if (f && (!hi.doNotOverride || f->isDeclaration())) {
      // Make sure NoReturn attribute is set, for optimization and
      // coverage counting.
      if (hi.doesNotReturn)
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
        f->addFnAttr(Attribute::NoReturn);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
        f->addFnAttr(Attributes::NoReturn);
#else
        f->addFnAttr(Attribute::NoReturn);
#endif

      // Change to a declaration since we handle internally (simplifies
      // module and allows deleting dead code).
      if (!f->isDeclaration())
        f->deleteBody();
    }
  }
}

void SpecialFunctionHandler::bind() {
  unsigned N = sizeof(handlerInfo)/sizeof(handlerInfo[0]);

  for (unsigned i=0; i<N; ++i) {
    HandlerInfo &hi = handlerInfo[i];
    Function *f = executor.kmodule->module->getFunction(hi.name);

    if (f && (!hi.doNotOverride || f->isDeclaration()))
      handlers[f] = std::make_pair(hi.handler, hi.hasReturnValue);
  }
}


bool SpecialFunctionHandler::handle(ExecutionState &state,
                                    Function *f,
                                    KInstruction *target,
                                    std::vector< ref<Expr> > &arguments) {
  handlers_ty::iterator it = handlers.find(f);
  if (it != handlers.end()) {
    Handler h = it->second.first;
    bool hasReturnValue = it->second.second;
     // FIXME: Check this... add test?
    if (!hasReturnValue && !target->inst->use_empty()) {
      executor.terminateStateOnExecError(state,
                                         "expected return value from void special function");
    } else {
      (this->*h)(state, target, arguments);
    }
    return true;
  } else {
    return false;
  }
}

/****/

// reads a concrete string from memory
std::string
SpecialFunctionHandler::readStringAtAddress(ExecutionState &state,
                                            ref<Expr> addressExpr) {
  ObjectPair op;
  addressExpr = executor.toUnique(state, addressExpr);
  ref<ConstantExpr> address = cast<ConstantExpr>(addressExpr);
  if (!state.addressSpace.resolveOne(address, op))
    assert(0 && "XXX out of bounds / multiple resolution unhandled");
  bool res __attribute__ ((unused));
  assert(executor.solver->mustBeTrue(state,
                                     EqExpr::create(address,
                                                    op.first->getBaseExpr()),
                                     res) &&
         res &&
         "XXX interior pointer unhandled");
  const MemoryObject *mo = op.first;
  const ObjectState *os = op.second;

  char *buf = new char[mo->size];

  unsigned i;
  for (i = 0; i < mo->size - 1; i++) {
    ref<Expr> cur = os->read8(i);
    cur = executor.toUnique(state, cur);
    assert(isa<ConstantExpr>(cur) &&
           "hit symbolic char while reading concrete string");
    buf[i] = cast<ConstantExpr>(cur)->getZExtValue(8);
  }
  buf[i] = 0;

  std::string result(buf);
  delete[] buf;
  return result;
}

/****/

void SpecialFunctionHandler::handleAbort(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==0 && "invalid number of arguments to abort");
  executor.terminateStateOnError(state, "abort failure", "abort.err");
}

void SpecialFunctionHandler::handleExit(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to exit");
  executor.terminateStateOnExit(state);
}

void SpecialFunctionHandler::handleSilentExit(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to exit");
  executor.terminateState(state);
}

void SpecialFunctionHandler::handleAliasFunction(ExecutionState &state,
						 KInstruction *target,
						 std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_alias_function");
  std::string old_fn = readStringAtAddress(state, arguments[0]);
  std::string new_fn = readStringAtAddress(state, arguments[1]);
  KLEE_DEBUG_WITH_TYPE("alias_handling", llvm::errs() << "Replacing " << old_fn
                                           << "() with " << new_fn << "()\n");
  if (old_fn == new_fn)
    state.removeFnAlias(old_fn);
  else state.addFnAlias(old_fn, new_fn);
}
//butp use
extern bool BuptShadow;

void SpecialFunctionHandler::handleShadowEnabled(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==0 &&
         "invalid number of arguments to klee_shadow_enabled");
  //std::cerr<<"BuptShadow: "<<BuptShadow<<std::endl;
  executor.bindLocal(target, state,
                     ConstantExpr::create(BuptShadow, Expr::Int32));
}

void SpecialFunctionHandler::handleAssert(ExecutionState &state,
                                          KInstruction *target,
                                          std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==3 && "invalid number of arguments to _assert");
  executor.terminateStateOnError(state,
				 "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
				 "assert.err");
}

void SpecialFunctionHandler::handleAssertFail(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==4 && "invalid number of arguments to __assert_fail");
  executor.terminateStateOnError(state,
				 "ASSERTION FAIL: " + readStringAtAddress(state, arguments[0]),
				 "assert.err");
}

void SpecialFunctionHandler::handleReportError(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==4 && "invalid number of arguments to klee_report_error");

  // arguments[0], arguments[1] are file, line
  executor.terminateStateOnError(state,
				 readStringAtAddress(state, arguments[2]),
				 readStringAtAddress(state, arguments[3]).c_str());
}

void SpecialFunctionHandler::handleMerge(ExecutionState &state,
                           KInstruction *target,
                           std::vector<ref<Expr> > &arguments) {
  // nop
}

void SpecialFunctionHandler::handleNew(ExecutionState &state,
                         KInstruction *target,
                         std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new");

  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDelete(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // FIXME: Should check proper pairing with allocation type (malloc/free,
  // new/delete, new[]/delete[]).

  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleNewArray(ExecutionState &state,
                              KInstruction *target,
                              std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to new[]");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleDeleteArray(ExecutionState &state,
                                 KInstruction *target,
                                 std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to delete[]");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleMalloc(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 && "invalid number of arguments to malloc");
  executor.executeAlloc(state, arguments[0], false, target);
}

void SpecialFunctionHandler::handleAssume(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_assume");

  ref<Expr> e = arguments[0];
//bupt use
	ref<Expr> e_old=e, e_new=e;
	if(e->isContainShadow())
	{
		e_old=e->findShadowExpr(0);
		e_new=e->findShadowExpr(1);
		if(state.isSPEO())
			e=e_old;
		else if(state.isSPEN())
			e=e_new;
	}
	if(e->isContainShadow() && state.isUE())
	{
		bool old_err=false;
		if(e_old->getWidth() != Expr::Bool)
			e_old=NeExpr::create(e_old, ConstantExpr::create(0, e_old->getWidth()));
		bool old_res;
		bool old_success __attribute__ ((unused)) = executor.solver->mustBeFalse(state, e_old, old_res);
	  	assert(old_success && "FIXME: Unhandled solver failure");
		if(old_res)
			old_err=true;
		else
			executor.addConstraint(state,e_old);
		if(e_new->getWidth() != Expr::Bool)
			e_new=NeExpr::create(e_new, ConstantExpr::create(0, e_new->getWidth()));
		bool new_res;
		bool new_success __attribute__ ((unused)) = executor.solver->mustBeFalse(state, e_new, new_res);
		assert(new_success && "FIXME: Unhandled solver failure");
		if(new_res)
		{
			if(old_err)
		            executor.terminateStateOnError(state,
                                       "invalid klee_assume call (provably false) in both versions",
                                       "both.user.err");
       	 		else
            			executor.terminateStateOnError(state,
                                       "invalid klee_assume call (provably false) in new version",
                                       "new.user.err");
		}
		else
		{
			if(old_err)
			    executor.terminateStateOnError(state,
						       "invalid klee_assume call (provably false) in old version",
						       "old.user.err");
			executor.addConstraint(state, e_new);

		}
	}
	else
	{

	  if (e->getWidth() != Expr::Bool)
	    e = NeExpr::create(e, ConstantExpr::create(0, e->getWidth()));

	  bool res;
	  bool success __attribute__ ((unused)) = executor.solver->mustBeFalse(state, e, res,false);
	  assert(success && "FIXME: Unhandled solver failure");
	  if (res) {
	    executor.terminateStateOnError(state,
					   "invalid klee_assume call (provably false)",
					   "user.err");
	  } else {
	    executor.addConstraint(state, e);
	  }
	}
}

void SpecialFunctionHandler::handleIsSymbolic(ExecutionState &state,
                                KInstruction *target,
                                std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_is_symbolic");

  executor.bindLocal(target, state,
                     ConstantExpr::create(!isa<ConstantExpr>(arguments[0]),
                                          Expr::Int32));
}

void SpecialFunctionHandler::handlePreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_prefex_cex");

  ref<Expr> cond = arguments[1];
  if (cond->getWidth() != Expr::Bool)
    cond = NeExpr::create(cond, ConstantExpr::alloc(0, cond->getWidth()));

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "prefex_cex");

  assert(rl.size() == 1 &&
         "prefer_cex target must resolve to precisely one object");

  rl[0].first.first->cexPreferences.push_back(cond);
}

void SpecialFunctionHandler::handlePosixPreferCex(ExecutionState &state,
                                             KInstruction *target,
                                             std::vector<ref<Expr> > &arguments) {
  if (ReadablePosix)
    return handlePreferCex(state, target, arguments);
}

void SpecialFunctionHandler::handlePrintExpr(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_expr");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1] << "\n";
}

void SpecialFunctionHandler::handleSetForking(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_set_forking");
  ref<Expr> value = executor.toUnique(state, arguments[0]);

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    state.forkDisabled = CE->isZero();
  } else {
    executor.terminateStateOnError(state,
                                   "klee_set_forking requires a constant arg",
                                   "user.err");
  }
}

void SpecialFunctionHandler::handleStackTrace(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  state.dumpStack(outs());
}

void SpecialFunctionHandler::handleWarning(ExecutionState &state,
                                           KInstruction *target,
                                           std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 && "invalid number of arguments to klee_warning");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning("%s: %s", state.stack.back().kf->function->getName().data(),
               msg_str.c_str());
}

void SpecialFunctionHandler::handleWarningOnce(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_warning_once");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  klee_warning_once(0, "%s: %s", state.stack.back().kf->function->getName().data(),
                    msg_str.c_str());
}

void SpecialFunctionHandler::handlePrintRange(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_print_range");

  std::string msg_str = readStringAtAddress(state, arguments[0]);
  llvm::errs() << msg_str << ":" << arguments[1];
  if (!isa<ConstantExpr>(arguments[1])) {
    // FIXME: Pull into a unique value method?
    ref<ConstantExpr> value;
    bool success __attribute__ ((unused)) = executor.solver->getValue(state, arguments[1], value);
    assert(success && "FIXME: Unhandled solver failure");
    bool res;
    success = executor.solver->mustBeTrue(state,
                                          EqExpr::create(arguments[1], value),
                                          res);
    assert(success && "FIXME: Unhandled solver failure");
    if (res) {
      llvm::errs() << " == " << value;
    } else {
      llvm::errs() << " ~= " << value;
      std::pair< ref<Expr>, ref<Expr> > res =
        executor.solver->getRange(state, arguments[1]);
      llvm::errs() << " (in [" << res.first << ", " << res.second <<"])";
    }
  }
  llvm::errs() << "\n";
}

void SpecialFunctionHandler::handleGetObjSize(ExecutionState &state,
                                  KInstruction *target,
                                  std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_obj_size");
  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "klee_get_obj_size");
  for (Executor::ExactResolutionList::iterator it = rl.begin(),
         ie = rl.end(); it != ie; ++it) {
    executor.bindLocal(target, *it->second,
                       ConstantExpr::create(it->first.first->size, Expr::Int32));
  }
}

void SpecialFunctionHandler::handleGetErrno(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==0 &&
         "invalid number of arguments to klee_get_errno");
  executor.bindLocal(target, state,
                     ConstantExpr::create(errno, Expr::Int32));
}

void SpecialFunctionHandler::handleCalloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to calloc");

  ref<Expr> size = MulExpr::create(arguments[0],
                                   arguments[1]);
  executor.executeAlloc(state, size, false, target, true);
}

void SpecialFunctionHandler::handleRealloc(ExecutionState &state,
                            KInstruction *target,
                            std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==2 &&
         "invalid number of arguments to realloc");
  ref<Expr> address = arguments[0];
  ref<Expr> size = arguments[1];

	//butp use
	if(state.isUE() && (address->isContainShadow() || size->isContainShadow()))
	{
		ref<Expr> newaddress=address, oldaddress=address, oldsize=size, newsize=size;
		if(address->isContainShadow())
		{
			oldaddress=address->findShadowExpr(0);
			newaddress=address->findShadowExpr(1);
		}
		if(size->isContainShadow())
		{
			oldsize=size->findShadowExpr(0);
			newsize=size->findShadowExpr(1);
		}
	      Executor::StatePair zeroSize = executor.fork(state,
							   Expr::createIsZero(newsize),
							   true);

	      if (zeroSize.first) { // newsize == 0
		Executor::StatePair zeroSize_old = executor.fork(*zeroSize.first,
							   Expr::createIsZero(oldsize),
							   true);
		if(zeroSize_old.first){ // oldsize == 0 && newsize == 0
		    executor.executeFree(*zeroSize_old.first, address, target);
		}
		if(zeroSize_old.second){ // oldsize !=0 && newsize == 0
		    executor.executeFree(*zeroSize_old.first, newaddress, target);
		    Executor::StatePair zeroPointer = executor.fork(*zeroSize_old.second,
								Expr::createIsZero(oldaddress),
								true);
		    if(zeroPointer.first){ // oldaddress == 0
			zeroPointer.first->intoSPEO();
			executor.executeAlloc(*zeroPointer.first, oldsize, false, target);
			zeroPointer.first->intoUE();
		    }
		    if(zeroPointer.second){ // oldaddress != 0
			zeroPointer.second->intoSPEO();
		      Executor::ExactResolutionList rl;
		      executor.resolveExact(*zeroPointer.second, oldaddress, rl, "realloc");
			zeroPointer.second->intoUE();
		      for (Executor::ExactResolutionList::iterator it = rl.begin(),
			     ie = rl.end(); it != ie; ++it) {
			it->second->intoSPEO();
			executor.executeAlloc(*it->second, oldsize, false, target, false,
					      it->first.second);
			it->second->intoUE();
		      }
		    }
		}
	      }
	      if (zeroSize.second) { // newsize != 0
		Executor::StatePair zeroSize_old = executor.fork(*zeroSize.first,
							   Expr::createIsZero(oldsize),
							   true);
		if(zeroSize_old.first){ // newsize != 0 && oldsize == 0
		    executor.executeFree(*zeroSize_old.first, oldaddress, target);
		    Executor::StatePair zeroPointer = executor.fork(*zeroSize_old.first,
								Expr::createIsZero(newaddress),
								true);
		    if(zeroPointer.first){ // newaddress == 0
				zeroPointer.first->intoSPEN();
			executor.executeAlloc(*zeroPointer.first, newsize, false, target);
			zeroPointer.first->intoUE();
		    }
		    if(zeroPointer.second){ // newaddress != 0
		      Executor::ExactResolutionList rl;
			zeroPointer.second->intoSPEN();
		      executor.resolveExact(*zeroPointer.second, newaddress, rl, "realloc");
			zeroPointer.second->intoUE();

		      for (Executor::ExactResolutionList::iterator it = rl.begin(),
			     ie = rl.end(); it != ie; ++it) {
			it->second->intoSPEN();
			executor.executeAlloc(*it->second, newsize, false, target, false,
					      it->first.second);
			it->second->intoUE();
		      }
		    }
		}
		if(zeroSize_old.second){ //newsize!=0 && oldsize !=0
		    Executor::StatePair zeroPointer_new = executor.fork(*zeroSize_old.second,
								    Expr::createIsZero(newaddress),
								    true);
		    if(zeroPointer_new.first){
			Executor::StatePair zeroPointer_old = executor.fork(*zeroPointer_new.first,
									Expr::createIsZero(oldaddress),
									true);
			if(zeroPointer_old.first){ // newaddress==0 && oldaddress == 0
			    executor.executeAlloc(*zeroPointer_old.first, size, false, target);
			}
			if(zeroPointer_old.second){ //newaddress==0 && oldaddress != 0
				zeroPointer_old.second->intoSPEN();
			    executor.executeAlloc(*zeroPointer_old.second, newsize, false, target);
				zeroPointer_old.second->intoSPEO();
			    Executor::ExactResolutionList rl;
			    executor.resolveExact(*zeroPointer_old.second, oldaddress, rl, "realloc");
				zeroPointer_old.second->intoUE();
			    for (Executor::ExactResolutionList::iterator it = rl.begin(),
				   ie = rl.end(); it != ie; ++it) {
				  it->second->intoSPEO();
			      executor.executeAlloc(*it->second, oldsize, false, target, false,
						    it->first.second);
				  it->second->intoUE();
			    }
			}
		    }
		    if(zeroPointer_new.second){
			Executor::StatePair zeroPointer_old = executor.fork(*zeroPointer_new.second,
									Expr::createIsZero(oldaddress),
									true);
			if(zeroPointer_old.first){ // newaddress != 0 && oldaddress == 0
			    executor.executeAlloc(*zeroPointer_old.first, size, false, target);
			    Executor::ExactResolutionList rl;
				zeroPointer_old.first->intoSPEN();
			    executor.resolveExact(*zeroPointer_old.first, newaddress, rl, "realloc");
				zeroPointer_old.first->intoUE();

			    for (Executor::ExactResolutionList::iterator it = rl.begin(),
				   ie = rl.end(); it != ie; ++it) {
				  it->second->intoSPEN();
			      executor.executeAlloc(*it->second, newsize, false, target, false,
						    it->first.second);
				  it->second->intoUE();
			    }
			}
			if(zeroPointer_old.second){ //newaddress != 0 && oldaddress != 0
				zeroPointer_old.second->intoSPEO();
			    Executor::ExactResolutionList rl;
			    executor.resolveExact(*zeroPointer_old.second, oldaddress, rl, "realloc");
				zeroPointer_old.second->intoUE();
			    for (Executor::ExactResolutionList::iterator it = rl.begin(),
				   ie = rl.end(); it != ie; ++it) {
				  it->second->intoSPEO();
			      executor.executeAlloc(*it->second, oldsize, false, target, false,
						    it->first.second);
				  it->second->intoUE();
			    }
				zeroPointer_old.second->intoSPEN();
			    executor.resolveExact(*zeroPointer_old.second, newaddress, rl, "realloc");
				zeroPointer_old.second->intoUE();
			    for (Executor::ExactResolutionList::iterator it = rl.begin(),
				   ie = rl.end(); it != ie; ++it) {
				  it->second->intoSPEN();
			      executor.executeAlloc(*it->second, newsize, false, target, false,
						    it->first.second);
				  it->second->intoUE();
			    }
			}
		    }
		}
	      }

	}
	else
	{
		//bupt use
		if(address->isContainShadow())
		{
			if(state.isSPEO())
				address=address->findShadowExpr(0);
			else if(state.isSPEN())
				address=address->findShadowExpr(1);
		}
		if(size->isContainShadow())
		{
			if(state.isSPEO())
				size=size->findShadowExpr(0);
			else if(state.isSPEN())
				size=size->findShadowExpr(1);
		}

	  Executor::StatePair zeroSize = executor.fork(state,
						       Expr::createIsZero(size),
						       true);

	  if (zeroSize.first) { // size == 0
	    executor.executeFree(*zeroSize.first, address, target);
	  }
	  if (zeroSize.second) { // size != 0
	    Executor::StatePair zeroPointer = executor.fork(*zeroSize.second,
							    Expr::createIsZero(address),
							    true);

	    if (zeroPointer.first) { // address == 0
	      executor.executeAlloc(*zeroPointer.first, size, false, target);
	    }
	    if (zeroPointer.second) { // address != 0
	      Executor::ExactResolutionList rl;
	      executor.resolveExact(*zeroPointer.second, address, rl, "realloc");

	      for (Executor::ExactResolutionList::iterator it = rl.begin(),
		     ie = rl.end(); it != ie; ++it) {
		executor.executeAlloc(*it->second, size, false, target, false,
				      it->first.second);
	      }
	    }
	  }
	}
}

void SpecialFunctionHandler::handleFree(ExecutionState &state,
                          KInstruction *target,
                          std::vector<ref<Expr> > &arguments) {
  // XXX should type check args
  assert(arguments.size()==1 &&
         "invalid number of arguments to free");
  executor.executeFree(state, arguments[0]);
}

void SpecialFunctionHandler::handleCheckMemoryAccess(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> >
                                                       &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_check_memory_access");

//bupt use

	ref<Expr> address=arguments[0];
	ref<Expr> size=arguments[1];
	ref<Expr> address_old=address, size_old=size, address_new=address, size_new=size;
	bool shadowflag=false;
	if(address->isContainShadow())
	{
		address_old=address->findShadowExpr(0);
		address_new=address->findShadowExpr(1);
		if(state.isSPEO())
			address=address_old;
		else if(state.isSPEN())
			address=address_new;
		else if(state.isUE())
			shadowflag=true;
	}
	if(size->isContainShadow())
	{
		size_old=size->findShadowExpr(0);
		size_new=size->findShadowExpr(1);
		if(state.isSPEO())
			size=size_old;
		else if(state.isSPEN())
			size=size_new;
		else if(state.isUE())
			shadowflag=true;
	}

	if(state.isUE() && shadowflag)
	{

		  bool olderr1=false,olderr2=false,newerr1=false,newerr2=false;
		  address_old = executor.toUnique(state, address_old);
		  size_old = executor.toUnique(state, size_old);
		  if (!isa<ConstantExpr>(address_old) || !isa<ConstantExpr>(size_old)) {
			olderr1=true;
		  } else {
			ObjectPair op;

			if (!state.addressSpace.resolveOne(cast<ConstantExpr>(address_old), op)) {
				olderr2=true;
			} else {
			  ref<Expr> chk =
				op.first->getBoundsCheckPointer(address_old,
						cast<ConstantExpr>(size_old)->getZExtValue());
			  if (!chk->isTrue()) {
				  olderr2=true;
			  }
			}
		  }
		  address_new = executor.toUnique(state, address_new);
		  size_new = executor.toUnique(state, size_new);
		  if (!isa<ConstantExpr>(address_new) || !isa<ConstantExpr>(size_new)) {
			  newerr1=true;
		  } else {
			ObjectPair op;

			if (!state.addressSpace.resolveOne(cast<ConstantExpr>(address_new), op)) {
				newerr2=true;
			} else {
			  ref<Expr> chk =
				op.first->getBoundsCheckPointer(address_new,
						cast<ConstantExpr>(size_new)->getZExtValue());
			  if (!chk->isTrue()) {
				  newerr2=true;
			  }
			}
		  }
		  if(olderr1)
		  {
			if(newerr1)
			{
				executor.terminateStateOnError(state,
										   "check_memory_access requires constant args in both versions",
										   "both.user.err");
			}
			else if(newerr2)
			{

					executor.terminateStateOnError(state,
											   "check_memory_access requires constant args in old version and check_memory_access: memory error in new version",
											   "user.err.ptr.err",
											   executor.getAddressInfo(state, address_new));
			}
			else
			{

				executor.terminateStateOnError(state,
										   "check_memory_access requires constant args only in old version",
										   "old.user.err");
			}
		  }
		  else if(olderr2)
		  {
			if(newerr1)
			{

				executor.terminateStateOnError(state,
											 "check_memory_access: memory error in old version and check_memory_access requires constant args in new version",
											 "ptr.err.user.err",
											 executor.getAddressInfo(state, address_old));
			}
			else if(newerr2)
			{

					std::string err_info="old version: "+executor.getAddressInfo(state, address_old);
					err_info=err_info+"new version: "+executor.getAddressInfo(state, address_new);
					executor.terminateStateOnError(state,
												 "check_memory_access: memory error in both versions",
												 "both.ptr.err",
												 err_info);
			}
			else
			{
			  executor.terminateStateOnError(state,
											 "check_memory_access: memory error only in old version",
											 "old.ptr.err",
											 executor.getAddressInfo(state, address_old));
			}

		  }
		  else
		  {
			if(newerr1)
			{

				executor.terminateStateOnError(state,
										   "check_memory_access requires constant args only in new version",
										   "new.user.err");
			}
			else if(newerr2)
			{

			  executor.terminateStateOnError(state,
											 "check_memory_access: memory error only in new version",
											 "new.ptr.err",
											 executor.getAddressInfo(state, address_new));
			}
		  }
	}
	else
	{
	  ref<Expr> UniAddress = executor.toUnique(state, address);
	  ref<Expr> UniSize = executor.toUnique(state, size);
	  if (!isa<ConstantExpr>(UniAddress) || !isa<ConstantExpr>(UniSize)) {
	    executor.terminateStateOnError(state,
					   "check_memory_access requires constant args",
					   "user.err");
	  } else {
	    ObjectPair op;

	    if (!state.addressSpace.resolveOne(cast<ConstantExpr>(UniAddress), op)) {
	      executor.terminateStateOnError(state,
					     "check_memory_access: memory error",
					     "ptr.err",
					     executor.getAddressInfo(state, UniAddress));
	    } else {
	      ref<Expr> chk =
		op.first->getBoundsCheckPointer(UniAddress,
						cast<ConstantExpr>(UniSize)->getZExtValue());
	      if (!chk->isTrue()) {
		executor.terminateStateOnError(state,
					       "check_memory_access: memory error",
					       "ptr.err",
					       executor.getAddressInfo(state, UniAddress));
	      }
	    }
	  }
	}
}

void SpecialFunctionHandler::handleGetConcreteValue(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_value");
  //jl modify
  //bool hasChangedBefore=false;
  bool hasChangedBefore=true;
  if(state.hasChangedBefore()){
      state.removeHasChanged();
      hasChangedBefore=true;
  }
  ref<Expr> e=arguments[0];
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
        success = executor.solver->getValue(state, old_e, old_value,true);
        if(debug==1){
            errs()<<"getValue get old value: "<<old_value;
            if(old_value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        assert(success && "FIXME: Unhandled solver failure in old version");
        (void) success;
        success = executor.solver->getValue(state, new_e, new_value,true);
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
        executor.bindLocal(target, state, shadowExpr);
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
        success = executor.solver->getValue(state, e, value,true);
        if(debug==1){
            errs()<<"getValue get value: "<<value;
            if(value->isPointer())
                errs()<<" is PointerTy\n";
            else
                errs()<<" is not PointerTy\n";
        }
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        executor.bindLocal(target, state, value);
    }
  }
  else
  {
      e = state.constraints.simplifyExpr(e);
      std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = executor.seedMap.find(&state);
      ref<ConstantExpr> value;
      bool success;
      success = executor.solver->getValue(state, e, value,true);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if(debug==1){
          errs()<<"getValue get value: "<<value;
          if(value->isPointer())
              errs()<<" is PointerTy\n";
          else
              errs()<<" is not PointerTy\n";
      }
      executor.bindLocal(target, state, value);
  }
    if(hasChangedBefore)
        state.markHasChanged();
}

void SpecialFunctionHandler::handleGetValue(ExecutionState &state,
                                            KInstruction *target,
                                            std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_get_value");

  executor.executeGetValue(state, arguments[0], target);
}

void SpecialFunctionHandler::handleDefineFixedObject(ExecutionState &state,
                                                     KInstruction *target,
                                                     std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==2 &&
         "invalid number of arguments to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[0]) &&
         "expect constant address argument to klee_define_fixed_object");
  assert(isa<ConstantExpr>(arguments[1]) &&
         "expect constant size argument to klee_define_fixed_object");

  uint64_t address = cast<ConstantExpr>(arguments[0])->getZExtValue();
  uint64_t size = cast<ConstantExpr>(arguments[1])->getZExtValue();
  MemoryObject *mo = executor.memory->allocateFixed(address, size, state.prevPC->inst);
  executor.bindObjectInState(state, mo, false);
  mo->isUserSpecified = true; // XXX hack;
}

void SpecialFunctionHandler::handleMakeSymbolic(ExecutionState &state,
                                                KInstruction *target,
                                                std::vector<ref<Expr> > &arguments) {
  std::string name;

  // FIXME: For backwards compatibility, we should eventually enforce the
  // correct arguments.
  if (arguments.size() == 2) {
    name = "unnamed";
  } else {
    // FIXME: Should be a user.err, not an assert.
    assert(arguments.size()==3 &&
           "invalid number of arguments to klee_make_symbolic");
    name = readStringAtAddress(state, arguments[2]);
  }

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "make_symbolic");

  for (Executor::ExactResolutionList::iterator it = rl.begin(),
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    mo->setName(name);

    const ObjectState *old = it->first.second;
    ExecutionState *s = it->second;

    if (old->readOnly) {
      executor.terminateStateOnError(*s,
                                     "cannot make readonly object symbolic",
                                     "user.err");
      return;
    }

    // FIXME: Type coercion should be done consistently somewhere.
    bool res;
    bool success __attribute__ ((unused)) =
      executor.solver->mustBeTrue(*s,
                                  EqExpr::create(ZExtExpr::create(arguments[1],
                                                                  Context::get().getPointerWidth()),
                                                 mo->getSizeExpr()),
                                  res);
    assert(success && "FIXME: Unhandled solver failure");

    if (res) {
      executor.executeMakeSymbolic(*s, mo, name);
    } else {
      executor.terminateStateOnError(*s,
                                     "wrong size given to klee_make_symbolic[_name]",
                                     "user.err");
    }
  }
}

void SpecialFunctionHandler::handleMarkGlobal(ExecutionState &state,
                                              KInstruction *target,
                                              std::vector<ref<Expr> > &arguments) {
  assert(arguments.size()==1 &&
         "invalid number of arguments to klee_mark_global");

  Executor::ExactResolutionList rl;
  executor.resolveExact(state, arguments[0], rl, "mark_global");

  for (Executor::ExactResolutionList::iterator it = rl.begin(),
         ie = rl.end(); it != ie; ++it) {
    const MemoryObject *mo = it->first.first;
    assert(!mo->isLocal);
    mo->isGlobal = true;
  }
}

void SpecialFunctionHandler::handleAddOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state,
                                 "overflow on unsigned addition",
                                 "overflow.err");
}

void SpecialFunctionHandler::handleSubOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state,
                                 "overflow on unsigned subtraction",
                                 "overflow.err");
}

void SpecialFunctionHandler::handleMulOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state,
                                 "overflow on unsigned multiplication",
                                 "overflow.err");
}

void SpecialFunctionHandler::handleDivRemOverflow(ExecutionState &state,
                                               KInstruction *target,
                                               std::vector<ref<Expr> > &arguments) {
  executor.terminateStateOnError(state,
                                 "overflow on division or remainder",
                                 "overflow.err");
}
