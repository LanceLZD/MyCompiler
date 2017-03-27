#include "llvm/InitializePasses.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"
#include <deque>
#include <map>
#include <utility>
#include <vector>
#include <231DFA.h>
#include <set>
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

namespace llvm {
    class LivenessInfo:public Info {
    private:
        std::set<int> infos;

    public:
        LivenessInfo() {}

        LivenessInfo(LivenessInfo& other){
            for (auto & it:other.getInfos())
                infos.insert(it);
        }

        static bool equals (LivenessInfo *info1, LivenessInfo *info2) {
            std::set<int> i1 = info1->getInfos();
            std::set<int> i2 = info2->getInfos();
            if (i1.size()!=i2.size()) return 0;
            for (auto & it:i1)
                if (i2.count(it)==0) return 0;
            return 1;
        }

        static LivenessInfo* join(LivenessInfo * info1, LivenessInfo * info2, LivenessInfo * result) {
            if (result==info1 || result==info2) {
                if (result==info1 && result!=info2) {
                    for (auto it=(*info2).infos.begin();it!=(*info2).infos.end();it++) {
                        (*result).infos.insert(*it);
                    }
                }
                if (result!=info1 && result==info2) {
                    for (auto it=(*info1).infos.begin();it!=(*info1).infos.end();it++) {
                        (*result).infos.insert(*it);
                    }
                }
            }
            else {
                for (auto it=(*info1).infos.begin();it!=(*info1).infos.end();it++) {
                    (*result).infos.insert(*it);
                }
                for (auto it=(*info2).infos.begin();it!=(*info2).infos.end();it++) {
                    (*result).infos.insert(*it);
                }
            }
            return result;
        }

        void addInfo(int n) {
            infos.insert(n);
        }

        void deleteInfo(int n) {
            infos.erase(n);
        }

        std::set<int> getInfos() {
            std::set<int> newSet;
            for (auto it=infos.begin();it!=infos.end();it++) {
                newSet.insert(*it);
            }
            return newSet;
        }

        void print() {
            for (auto it = infos.begin();it!=infos.end();it++) {
                errs() << *it << "|";
            }
            errs() << "\n";
        }

        ~LivenessInfo() {}
    };

    class LivenessAnalysis:public DataFlowAnalysis<LivenessInfo, false>{
    private:
        bool needToDelete(int k) {
            if (k>=11 && k<=30)
                return 1;
            if (k==32 || k==51 || k==52 || k==55)
                return 1;
            return 0;
        }

        void flowfunction(Instruction * I,std::vector<unsigned> &IncomingEdges,std::vector<unsigned> &OutgoingEdges,std::vector<LivenessInfo *> &Infos) {
            LivenessInfo *result = new LivenessInfo();
            unsigned tmp = getIndexByInstr(I);
            int InstrCode = (*I).getOpcode();
            if (InstrCode==53) {//phi
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                Instruction* phiInstr = I;
                while (isa<PHINode>(phiInstr)) {
                    (*result).deleteInfo(getIndexByInstr(phiInstr));
                    phiInstr = phiInstr->getNextNode();
                }
            }
            else if (needToDelete(InstrCode)) {
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                for (unsigned i=0;i<I->getNumOperands();i++) {
                    auto *opr = I->getOperand(i);
                    if (isa<Instruction>(opr)) {
                        result->addInfo(getIndexByInstr((Instruction*)opr));
                    }
                }
                (*result).deleteInfo(tmp);
            }
            else {
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                for (unsigned i=0;i<I->getNumOperands();i++) {
                    auto *opr = I->getOperand(i);
                    if (isa<Instruction>(opr)) {
                        result->addInfo(getIndexByInstr((Instruction*)opr));
                    }
                }
            }

            for (unsigned i=0;i<OutgoingEdges.size();i++) {
                LivenessInfo *tmpresult = new LivenessInfo();
                for (auto val:result->getInfos()) {
                    tmpresult->addInfo(val);
                }
                Infos[i] = tmpresult;
            }

            if (InstrCode==53) {
                Instruction* phiInstr = I;
                while (isa<PHINode>(phiInstr)) {
                    PHINode *phi = (PHINode *)phiInstr;
                    unsigned numIV = phi->getNumIncomingValues();
                    for (unsigned i=0;i<numIV;i++) {
                        auto *opr = phi->getIncomingValue(i);
                        auto *bb = phi->getIncomingBlock(i);
                        for (unsigned j=0;j<OutgoingEdges.size();j++) {
                            auto *nextb = getInstrByIndex(OutgoingEdges[j])->getParent();
                            if (bb == nextb) {
                                unsigned addByPhi = getIndexByInstr((Instruction*)opr);
                                if (addByPhi != 0)
                                    Infos[j]->addInfo(addByPhi);
                            }
                        }
                    }
                    phiInstr = phiInstr->getNextNode();
                }
            }
            return;
        }

    public:
        LivenessAnalysis(LivenessInfo &bottom, LivenessInfo &initialState):DataFlowAnalysis(bottom, initialState) {}
        ~LivenessAnalysis() {}
    };

    struct LivenessAnalysisPass : public FunctionPass {
        static char ID;
        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            LivenessInfo *bottom = new LivenessInfo();
            LivenessInfo *initialState = new LivenessInfo();
            LivenessAnalysis la(*bottom, *initialState);
            la.runWorklistAlgorithm(&F);
            la.print();
            return false;
        }
    };
}

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", "Liveness analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);


