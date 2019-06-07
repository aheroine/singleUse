//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/ExecutionState.h"

#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"

#include "klee/Expr.h"

#include "Memory.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#else
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#endif
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <iomanip>
#include <sstream>
#include <cassert>
#include <map>
#include <set>
#include <stdarg.h>

using namespace llvm;
using namespace klee;

bool debug_value=0;
extern bool debug_addconst;
namespace {
  cl::opt<bool>
  DebugLogStateMerge("debug-log-state-merge");
}

/***/

extern bool debug;
StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0),
    minDistToUncoveredOnReturn(0), varargs(0), concernFlag(false), argShadow(false) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s)
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    concernFlag(s.concernFlag),
    concernArgsAndGVals(s.concernArgsAndGVals),
    concernArgsAndGValsExpr(s.concernArgsAndGValsExpr),
    varargsMap(s.varargsMap),
    argShadow(s.argShadow),
    addrOfShadow(s.addrOfShadow),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() {
  delete[] locals;
}

/***/

ExecutionState::ExecutionState(KFunction *kf) :
    pc(kf->instructions),
    prevPC(pc),
    pcId(0),

    queryCost(0.),
    weight(1),
    depth(0),

    instsSinceCovNew(0),
    coveredNew(false),
    forkDisabled(false),
    
    //jl change the initial value of haschanged
    //haschanged(false),
    haschanged(true),
    needTestCase(false),
    ctlordata(false),
    ctlAffected(false),
    isInBound(true),
    splitframe(0),
    mergePoint(NULL),
    retPoint(NULL),
    exeFlag(unified_ver),
    splitStatus(false),
    tmode(normal),
    ptreeNode(0) {
  pushFrame(0, kf);
}

ExecutionState::ExecutionState(const std::vector<ref<Expr> > &assumptions)
    : constraints(assumptions),
    queryCost(0.),
    pcId(0),

    //jl change the initial value of haschanged
    //haschanged(false),
    haschanged(true),
    needTestCase(false),
    ctlordata(false),
    ctlAffected(false),
    isInBound(true),
    splitframe(0),
    mergePoint(NULL),
    retPoint(NULL),
    exeFlag(unified_ver),
    splitStatus(false),
    tmode(normal),
    ptreeNode(0) {}

ExecutionState::~ExecutionState() {
  for (unsigned int i=0; i<symbolics.size(); i++)
  {
    const MemoryObject *mo = symbolics[i].first;
    assert(mo->refCount > 0);
    mo->refCount--;
    if (mo->refCount == 0)
      delete mo;
  }

  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    fnAliases(state.fnAliases),
    pc(state.pc),
    prevPC(state.prevPC),
    pcId(state.pcId),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),

    addressSpace(state.addressSpace),
    constraints(state.constraints),

    queryCost(state.queryCost),
    weight(state.weight),
    depth(state.depth),

    pathOS(state.pathOS),
    symPathOS(state.symPathOS),

    instsSinceCovNew(state.instsSinceCovNew),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    coveredLines(state.coveredLines),
    ptreeNode(state.ptreeNode),
    symbolics(state.symbolics),

    haschanged(state.haschanged),
    needTestCase(state.needTestCase),
    ctlordata(state.ctlordata),
    ctlAffected(state.ctlAffected),
    isInBound(state.isInBound),
    splitfunc(state.splitfunc),
    splitframe(state.splitframe),
    mergePoint(state.mergePoint),
    retPoint(state.retPoint),
    exeFlag(state.exeFlag),
    errmsg(state.errmsg),
    suffix(state.suffix),
    divmsg(state.divmsg),
    old_pathSequential(state.old_pathSequential),
    new_pathSequential(state.new_pathSequential),
    oldexit_pathSequential(state.oldexit_pathSequential),
    newexit_pathSequential(state.newexit_pathSequential),
    oldFreed(state.oldFreed),
    newFreed(state.newFreed),
    mergeSet(state.mergeSet),
    splitStatus(state.splitStatus),
    tmode(state.tmode),
    arrayNames(state.arrayNames)
{
  for (unsigned int i=0; i<symbolics.size(); i++)
    symbolics[i].first->refCount++;
}

ExecutionState *ExecutionState::branch() {
  depth++;

  ExecutionState *falseState = new ExecutionState(*this);
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  weight *= .5;
  falseState->weight -= weight;

  return falseState;
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.push_back(StackFrame(caller,kf));
}

void ExecutionState::popFrame() {
  StackFrame &sf = stack.back();
  for (std::vector<const MemoryObject*>::iterator it = sf.allocas.begin(),
         ie = sf.allocas.end(); it != ie; ++it)
    addressSpace.unbindObject(*it);
  stack.pop_back();
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) {
  mo->refCount++;
  symbolics.push_back(std::make_pair(mo, array));
}
///

std::string ExecutionState::getFnAlias(std::string fn) {
  std::map < std::string, std::string >::iterator it = fnAliases.find(fn);
  if (it != fnAliases.end())
    return it->second;
  else return "";
}

void ExecutionState::addFnAlias(std::string old_fn, std::string new_fn) {
  fnAliases[old_fn] = new_fn;
}

void ExecutionState::removeFnAlias(std::string fn) {
  fnAliases.erase(fn);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second;
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second;
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?
  if (symbolics!=b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }

  std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  std::set< ref<Expr> > bConstraints(b.constraints.begin(),
                                     b.constraints.end());
  std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  std::set_intersection(aConstraints.begin(), aConstraints.end(),
                        bConstraints.begin(), bConstraints.end(),
                        std::inserter(commonConstraints, commonConstraints.begin()));
  std::set_difference(aConstraints.begin(), aConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(aSuffix, aSuffix.end()));
  std::set_difference(bConstraints.begin(), bConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(bSuffix, bSuffix.end()));
  if (DebugLogStateMerge) {
    llvm::errs() << "\tconstraint prefix: [";
    for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
                                        ie = commonConstraints.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tA suffix: [";
    for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
                                        ie = aSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tB suffix: [";
    for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
                                        ie = bSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
  }

  // We cannot merge if addresses would resolve differently in the
  // states. This means:
  //
  // 1. Any objects created since the branch in either object must
  // have been free'd.
  //
  // 2. We cannot have free'd any pre-existing object in one state
  // and not the other

  if (DebugLogStateMerge) {
    llvm::errs() << "\tchecking object states\n";
    llvm::errs() << "A: " << addressSpace.objects << "\n";
    llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  }

  std::set<const MemoryObject*> mutated;
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  for (; ai!=ae && bi!=be; ++ai, ++bi) {
    if (ai->first != bi->first) {
      if (DebugLogStateMerge) {
        if (ai->first < bi->first) {
          llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
        } else {
          llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
        }
      }
      return false;
    }
    if (ai->second != bi->second) {
      if (DebugLogStateMerge)
        llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
      mutated.insert(ai->first);
    }
  }
  if (ai!=ae || bi!=be) {
    if (DebugLogStateMerge)
      llvm::errs() << "\t\tmappings differ\n";
    return false;
  }

  // merge stack

  ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  for (std::set< ref<Expr> >::iterator it = aSuffix.begin(),
         ie = aSuffix.end(); it != ie; ++it)
    inA = AndExpr::create(inA, *it);
  for (std::set< ref<Expr> >::iterator it = bSuffix.begin(),
         ie = bSuffix.end(); it != ie; ++it)
    inB = AndExpr::create(inB, *it);

  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if (av.isNull() || bv.isNull()) {
        // if one is null then by implication (we are at same pc)
        // we cannot reuse this local, so just ignore
      } else {
        av = SelectExpr::create(inA, av, bv);
      }
    }
  }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(),
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly &&
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      wos->write(i, SelectExpr::create(inA, av, bv));
    }
  }

  constraints = ConstraintManager();
  for (std::set< ref<Expr> >::iterator it = commonConstraints.begin(),
         ie = commonConstraints.end(); it != ie; ++it)
    constraints.addConstraint(*it);
  constraints.addConstraint(OrExpr::create(inA, inB));

  return true;
}
//bupt use
//note that such merge function must be called by old version: old.USEmerge(new)
bool ExecutionState::USEmerge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?
  if (symbolics!=b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }



  // merge stack

  //if only in B not in A, directly create a new one in A
  //if only in A not in B, modify its value in A to be shadowExpr
  std::set<const MemoryObject*> mutated;//both A and B have but different ObjectHolder
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  //check B's in A
    for (; bi!=be; ++bi)
    {
        MemoryMap::iterator it=addressSpace.objects.find(bi->first);
        if(it!=ae)//both have
        {
            if(debug_value==1){
                std::string mo_info_a, mo_info_b;
                it->first->getAllocInfo(mo_info_a);
                bi->first->getAllocInfo(mo_info_b);
                errs() <<"MO in state a: " << mo_info_a <<"\n";
                errs() <<"MO in state b: " << mo_info_b <<"\n";
                errs() <<"--= both in state a&b =--\n";
                bi->first->allocSite->dump();
                it->first->allocSite->dump();
                errs() << "state's mo address: "<< it->first->address <<"\n"
                    <<"the other state's mo address: "<<bi->first->address<<"\n";
                const ObjectState *aos = addressSpace.findObject(it->first);
                const ObjectState *bos = b.addressSpace.findObject(bi->first);
                ref<Expr> av,bv;
                /*
                errs()<<"a's value in mo:\n";
                for (unsigned i=0; i<it->first->size; i++) {
                    unsigned idx = Context::get().isLittleEndian() ? i : (it->first->size - i - 1);
                    ref<Expr> Byte = aos->read8(idx);
                    if(Byte->isContainShadow()){
                       ref<Expr> Byte=Byte->findShadowExpr(0);
                    }
                    errs()<<Byte<<" ";
                }
                errs()<<"\n";
                errs()<<"b's value in mo:\n";
                for (unsigned i=0; i<bi->first->size; i++) {
                    unsigned idx = Context::get().isLittleEndian() ? i : (bi->first->size - i - 1);
                    ref<Expr> Byte = bos->read8(idx);
                    if(Byte->isContainShadow()){
                       ref<Expr> Byte=Byte->findShadowExpr(1);
                    }
                    errs()<<Byte<<" ";
                }
                errs()<<"\n";
                */
            }
            //check ObjectHolder
            const ObjectState *aos = addressSpace.findObject(it->first);
            const ObjectState *bos = b.addressSpace.findObject(bi->first);
            for (unsigned i=0; i<bi->first->size; i++) {
                ref<Expr> av = aos->read8(i);
                ref<Expr> bv = bos->read8(i);
                if(av->isContainShadow()){
                   av=av->findShadowExpr(0);
                }
                if(bv->isContainShadow()){
                   bv=bv->findShadowExpr(1);
                }
                if(bv != av){
                    if(debug_value==1){
                        errs()<<"offset at "<<i<<"\n";
                        errs()<<"a's value in mo:\n";
                            errs()<<av<<"\n";
                        errs()<<"b's value in mo:\n";
                            errs()<<bv<<"\n";
                        errs()<<"is diff \n";
                        errs()<< "-------- End mutated found ------------\n";
                    }
                    mutated.insert(bi->first);
                    break;
                }
            }
        }
        else//only in B not in A
        {
            //add in A
            if(debug_value==1){
                std::string mo_info;
                bi->first->getAllocInfo(mo_info);
                errs() << mo_info <<"\n";
                const ObjectState *bos = b.addressSpace.findObject(bi->first);
                errs()<< "-------- unique B ------------\n";
            }
            const MemoryObject *mo=bi->first;
            const ObjectState *otherOS = b.addressSpace.findObject(bi->first);
            ObjectState *os=new ObjectState(mo);
            //ObjectState *os=const_cast<ObjectState*>(otherOS);
            addressSpace.bindObject(mo, os);
            if(mo->isLocal)
                stack.back().allocas.push_back(mo);
            ObjectState *wos = addressSpace.getWriteable(mo, os);
            for (unsigned i=0; i<mo->size; i++) {
                ref<Expr> bv = otherOS->read8(i);
                if(bv->isContainShadow()){
                    bv=bv->findShadowExpr(1);
                }
                ref<Expr> av = ShadowExpr::create(ConstantExpr::create(0, bv->getWidth()), bv);
                av->setOriginFlag();
                wos->write(i, av);
            }
            this->oldFreed.push_back(mo);
        }
    }
    for (; ai!=ae; ++ai)
    {
        MemoryMap::iterator it=b.addressSpace.objects.find(ai->first);
        if(it==be)//only in A
        {
            if(debug_value==1){
                std::string mo_info;
                ai->first->getAllocInfo(mo_info);
                errs() << mo_info <<"\n";
                errs()<< "-------- unique A ------------\n";
            }
            const MemoryObject *mo = ai->first;
            const ObjectState *os = addressSpace.findObject(mo);
            ObjectState *wos = addressSpace.getWriteable(mo, os);
            for (unsigned i=0; i<mo->size; i++) {
                ref<Expr> av = wos->read8(i);
                if(av->isContainShadow()){
                    av=av->findShadowExpr(0);
                }
                wos->write(i, ShadowExpr::create(av, ConstantExpr::create(0, av->getWidth())));
            }
            this->newFreed.push_back(mo);
        }
    }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(),
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly &&
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      if(bv->isContainShadow()){
          bv=bv->findShadowExpr(1);
      }
      if(av->isContainShadow()){
          av=av->findShadowExpr(0);
      }
      if(debug_value == 1){
          errs()<<"value in a: " <<av<<"\n"
              <<"value in b: "<<bv<<"\n";
      }
      if(av.isNull() && !bv.isNull()){
            if(debug_value == 1){
                errs()<<"--= are different =--\n";
            }
            wos->write(i, ShadowExpr::create(ConstantExpr::create(0, bv->getWidth()),bv));
      }
      else if(!av.isNull() && bv.isNull()){
            if(debug_value == 1){
                errs()<<"--= are different =--\n";
            }
            wos->write(i, ShadowExpr::create(av, ConstantExpr::create(0, av->getWidth())));
      }
      else if(!av.isNull() && !bv.isNull()){
          if(av==bv){
            if(debug_value == 1){
                errs()<<"--= are the same\n";
            }
            wos->write(i,av);
          }
          else{
            if(debug_value == 1){
                errs()<<"--= are different =--\n";
            }
            wos->write(i, ShadowExpr::create(av, bv));
          }
      }
      else
          continue;
    }
  }



  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    unsigned i=0;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if(av.isNull() && !bv.isNull())
          av=ShadowExpr::create(ConstantExpr::create(0, bv->getWidth()), bv);
      else if(!av.isNull() && bv.isNull())
          av=ShadowExpr::create(av, ConstantExpr::create(0, av->getWidth()));
      else if(!av.isNull() && !bv.isNull()){
          if(av==bv)
            continue;
          else
            av=ShadowExpr::create(av, bv);
      } else
          continue;
    }
  }

  return mergeConstraints(b);
  //return true;
}
//bupt use
bool ExecutionState::mergeConstraints(const ExecutionState &b)
{
    if(debug_addconst==1){
        errs()<<"merge state *"<<this<<"* with *"<<&b<<"*\n";
        errs()<<"position: "<<this->prevPC->info->assemblyLine<<"@"<<this->prevPC->info->line<<"\n";
    }
    std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
    std::set< ref<Expr> > bConstraints(b.constraints.begin(),
                     b.constraints.end());
    std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
    std::set_intersection(aConstraints.begin(), aConstraints.end(),
            bConstraints.begin(), bConstraints.end(),
            std::inserter(commonConstraints, commonConstraints.begin()));
    std::set_difference(aConstraints.begin(), aConstraints.end(),
              commonConstraints.begin(), commonConstraints.end(),
              std::inserter(aSuffix, aSuffix.end()));
    std::set_difference(bConstraints.begin(), bConstraints.end(),
              commonConstraints.begin(), commonConstraints.end(),
              std::inserter(bSuffix, bSuffix.end()));
    //merge constraints
    constraints = ConstraintManager();
    if(debug_addconst==1)
        errs()<<"merge aConstraints\n";
    for (std::set< ref<Expr> >::iterator it = aConstraints.begin(),
     ie = aConstraints.end(); it != ie; ++it)
        constraints.addConstraint(*it);
    if(debug_addconst==2){
        errs()<<"aSuffix constraints:\n";
        for (std::set< ref<Expr> >::iterator it = aSuffix.begin(),
                ie = aSuffix.end(); it != ie; ++it){
            errs()<<(*it)<<"\n";
        /// if(!constraints.addConstraintInMerge(*it)){
        ///     errs()<<"add aConstraints conflict!\n";
        ///     errs()<<this->prevPC->info->file<<":"<<this->prevPC->info->line<<"@"<<this->prevPC->info->assemblyLine<<"\n";
        ///     assert(false);
        ///     return false;
        /// }
        }
    }
    if(debug_addconst==1)
        errs()<<"merge bConstraints\n";
    for (std::set< ref<Expr> >::iterator it = bSuffix.begin(),
            ie = bSuffix.end(); it != ie; ++it){
        if(!constraints.addConstraintInMerge(*it)){
            if(debug==1){
              //errs() <<"constraints size: "<<constraints.size()<<"\n";
              //for(ConstraintManager::constraint_iterator pcit=constraints.begin(),pcie=constraints.end();pcit!=pcie;pcit++){
              //    (*pcit)->dump();
              //}
              errs()<<"conflict expr:\n"
                  <<(*it)<<"\n";
            }
            return false;
        }
    }
    return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << " (";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      out << ai->getName().str();
      // XXX should go through function
      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (isa<ConstantExpr>(value))
        out << "=" << value;
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}
