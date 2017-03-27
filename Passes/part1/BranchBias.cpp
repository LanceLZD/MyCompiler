#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"

using namespace llvm;
using namespace std;

namespace {
    struct BranchBias : public FunctionPass {
        static char ID;
        BranchBias() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            LLVMContext &context = F.getContext();

            Function *printFunc = cast<Function>(F.getParent()->getOrInsertFunction(
                    "printOutBranchInfo",
                    Type::getVoidTy(context),
                    NULL));
            Function *updateFunc = cast<Function>(F.getParent()->getOrInsertFunction(
                    "updateBranchInfo",
                    Type::getVoidTy(context),
                    IntegerType::get(context, 1),
                    NULL));
            for (Function::iterator B = F.begin(), BE = F.end(); B != BE; ++B) {
                for (BasicBlock::iterator I = B->begin(), IE = B->end(); I != IE; ++I) {
                    unsigned tmpOpCode = I->getOpcode();
                    if (tmpOpCode==2) {
                        unsigned num = I->getNumOperands();
                        if (num<=1)
                            continue;
                        IRBuilder<> builder(&*I);
                        Value* args[] = {I->getOperand(0)};
                        builder.CreateCall(updateFunc, args);
                    }
                    else if (tmpOpCode==1) {
                        IRBuilder<> builder(&*I);
                        builder.CreateCall(printFunc);
                    }
                }
            }

            return false;
        }
    };
}

char BranchBias::ID = 0;
static RegisterPass<BranchBias> X("cse231-bb", "Part 1 Problem 3",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
