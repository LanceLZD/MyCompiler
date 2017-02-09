#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include <unordered_map>
#include <string>

using namespace llvm;
using namespace std;

namespace {
    struct CountStaticInstructions : public FunctionPass {
        static char ID;
        CountStaticInstructions() : FunctionPass(ID) {}
        bool runOnFunction(Function &F) override {
            unordered_map<string, int> m;
            for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
                    m[string(I->getOpcodeName(I->getOpcode()))]++;
            }
            for (auto val=m.begin();val!=m.end();val++)
                    errs() << val->first << "\t" << val->second << "\n";
            return false;
        }
    };
}

char CountStaticInstructions::ID = 0;
static RegisterPass<CountStaticInstructions> X("cse231-csi", "Part 1 Problem 1",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
