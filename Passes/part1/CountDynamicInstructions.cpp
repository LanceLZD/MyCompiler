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
#include <unordered_map>

using namespace llvm;
using namespace std;

namespace {
    struct CountDynamicInstructions : public FunctionPass {
        static char ID;
        CountDynamicInstructions() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            LLVMContext &context = F.getContext();
            IntegerType *Ty_i32 = Type::getInt32Ty(context);
            Function *updateInstr = cast<Function>(F.getParent()->getOrInsertFunction(
                "updateInstrInfo",
                Type::getVoidTy(context),
                Ty_i32,
                Ty_i32,
                NULL));
            for (Function::iterator B = F.begin(), BE = F.end(); B != BE; ++B) {
                unordered_map<unsigned, unsigned> m;
                unsigned instrNum = 0;
                for (BasicBlock::iterator I = B->begin(), IE = B->end(); I != IE; ++I) {
                    m[I->getOpcode()]++;
                    if (instrNum==B->size()-1) {
                        for (auto val=m.begin(); val!=m.end(); val++) {
                            IRBuilder<> builder(&*I);
                            unsigned tmpOpCode = (*val).first;
                            unsigned tmpNum = (*val).second;
                            ConstantInt *num = ConstantInt::get(Ty_i32, tmpNum);
                            ConstantInt *OpCode = ConstantInt::get(Ty_i32, tmpOpCode);
                            Value* args[] = {OpCode, num};
                            builder.CreateCall(updateInstr, args);
                        }
                    }
                    instrNum++;
                    if ((*I).getOpcode()==1) {
                        Function *printFunc = cast<Function>(F.getParent()->getOrInsertFunction(
                            "printOutInstrInfo",
                            Type::getVoidTy(context),
                            NULL));
                        IRBuilder<> Builder(&*I);
                        Builder.CreateCall(printFunc);
                    }
                }
            }
            return false;
        }
    };
}

char CountDynamicInstructions::ID = 0;
static RegisterPass<CountDynamicInstructions> X("cse231-cdi", "Part 1 Problem 2",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
