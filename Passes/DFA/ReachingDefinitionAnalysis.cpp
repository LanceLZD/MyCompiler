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
    class ReachingInfo:public Info {
    private:
        std::set<int> infos;

    public:
        ReachingInfo() {}

        ReachingInfo(ReachingInfo& other){
            for (auto &it:other.getInfos())
                infos.insert(it);
        }

        static bool equals (ReachingInfo *info1, ReachingInfo *info2) {
            std::set<int> i1 = info1->getInfos();
            std::set<int> i2 = info2->getInfos();
            if (i1.size()!=i2.size()) return 0;
            for (auto &it:i1)
                if (i2.count(it)==0) return 0;
            return 1;
        }

        static ReachingInfo* join(ReachingInfo * info1, ReachingInfo * info2, ReachingInfo * result) {
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

        ~ReachingInfo() {}
    };

    class ReachingDefinitionAnalysis:public DataFlowAnalysis<ReachingInfo, true>{
    private:
        bool needToAdd(int k) {
            if (k>=11 && k<=30)
                return 1;
            if (k==32 || k==51 || k==52 || k==55)
                return 1;
            return 0;
        }

        void flowfunction(Instruction * I,std::vector<unsigned> &IncomingEdges,std::vector<unsigned> &OutgoingEdges,std::vector<ReachingInfo *> &Infos) {
            ReachingInfo *result = new ReachingInfo();
            unsigned tmp = getIndexByInstr(I);
            int InstrCode = (*I).getOpcode();
            if (InstrCode==53) {//phi
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                (*result).addInfo(tmp);
                Instruction* phiInstr = I->getNextNode();
                while (isa<PHINode>(phiInstr)) {
                    (*result).addInfo(getIndexByInstr(phiInstr));
                    phiInstr = phiInstr->getNextNode();
                }
            }
            else if (needToAdd(InstrCode)) {
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                (*result).addInfo(tmp);
            }
            else {
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
            }

            for (unsigned i=0;i<OutgoingEdges.size();i++) {
                ReachingInfo *tmpresult = new ReachingInfo();
                for (auto val:result->getInfos()) {
                    tmpresult->addInfo(val);
                }
                Infos[i] = tmpresult;
            }
            return;
        }
    public:
        ReachingDefinitionAnalysis(ReachingInfo &bottom, ReachingInfo &initialState):DataFlowAnalysis(bottom, initialState) {}
        ~ReachingDefinitionAnalysis() {}
    };

    struct ReachingDefinitionAnalysisPass : public FunctionPass {
        static char ID;
        ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            ReachingInfo *bottom = new ReachingInfo();
            ReachingInfo *initialState = new ReachingInfo();
            ReachingDefinitionAnalysis rda(*bottom, *initialState);
            rda.runWorklistAlgorithm(&F);
            rda.print();
            return false;
        }
    };
}

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", "Reaching definition analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);


