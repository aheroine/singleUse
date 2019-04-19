#ifndef _CFGPATH_H
#define _CFGPATH_H

#include <vector>
#include <map>
#include <string>

using namespace llvm;
namespace llvm{
    class BasicBlock;
}
class CFGPath{
    public:
        CFGPath():linked(false){};
        typedef std::pair<llvm::BasicBlock*, size_t> BBIndex;
        bool linked;
        std::set<BasicBlock*> blockVisited;
        std::map<BBIndex, bool > visited;
        std::set<BasicBlock*> exitBBs;
        //std::set<BasicBlock*> loopPoint;
        //std::string directChain;
        //std::vector<BasicBlock*> pathChain;
};

#endif
