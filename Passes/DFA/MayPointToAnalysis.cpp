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
#include <string>

using namespace llvm;
using namespace std;

namespace llvm {
    class MayPointToInfo:public Info {
    private:
        std::map<std::string, std::set<std::string>> infos;

    public:
        MayPointToInfo() {}

        MayPointToInfo(MayPointToInfo& other) {
            for (auto val=other.infos.begin();val!=other.infos.end();val++) {
                for (auto &it:val->second) {
                    infos[val->first].insert(it);
                }
            }
        }

        static bool equalSet(std::set<std::string> s1, std::set<std::string> s2) {
            if (s1.size()!=s2.size())
                return 0;
            for (auto &it:s1)
                if (s2.count(it)==0) return 0;
            return 1;
        }

        static bool equals (MayPointToInfo *info1, MayPointToInfo *info2) {
            std::map<std::string, std::set<std::string>> i1 = info1->getInfos();
            std::map<std::string, std::set<std::string>> i2 = info2->getInfos();
            if (i1.size()!=i2.size())
                return 0;
            for (auto val=i1.begin();val!=i1.end();val++) {
                if (!equalSet(val->second, i2[val->first]))
                    return 0;
            }
            return 1;
        }

        static MayPointToInfo* join(MayPointToInfo * info1, MayPointToInfo * info2, MayPointToInfo * result) {
            for (auto val=info1->infos.begin();val!=info1->infos.end();val++) {
                for (auto &it:val->second) {
                    result->infos[val->first].insert(it);
                }
            }
            for (auto val=info2->infos.begin();val!=info2->infos.end();val++) {
                for (auto &it:val->second) {
                    result->infos[val->first].insert(it);
                }
            }
            return result;
        }

        void addInfo(std::string k, std::string n) {
            infos[k].insert(n);
        }

        std::set<std::string> getInfosByIndex(std::string index) {
            std::set<std::string> newSet;
            for (auto &it:infos[index]) {
                newSet.insert(it);
            }
            return newSet;
        }

        std::map<std::string, std::set<std::string>> getInfos() {
            std::map<std::string, std::set<std::string>> newMap;
            for (auto val=infos.begin();val!=infos.end();val++) {
                for (auto &it:val->second) {
                    newMap[val->first].insert(it);
                }
            }
            return newMap;
        }

        void print() {
            for (auto val=infos.begin();val!=infos.end();val++) {
                errs() << val->first << "->(";
                for (auto &it:val->second) {
                    errs() << it << "/";
                }
                errs() << ")|";
            }
            errs() << "\n";
        }

        ~MayPointToInfo() {}
    };

    class MayPointToAnalysis:public DataFlowAnalysis<MayPointToInfo, true>{
    private:
        bool needToAdd(int k) {
            if (k>=11 && k<=30)
                return 1;
            if (k==32 || k==51 || k==52 || k==55)
                return 1;
            return 0;
        }

        void flowfunction(Instruction * I,std::vector<unsigned> &IncomingEdges,std::vector<unsigned> &OutgoingEdges,std::vector<MayPointToInfo *> &Infos) {
            MayPointToInfo *result = new MayPointToInfo();
            unsigned tmp = getIndexByInstr(I);
            int InstrCode = I->getOpcode();
            if (InstrCode==29) {//alloca
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                result->addInfo("R"+std::to_string(tmp), "M"+std::to_string(tmp));
            }
            else if (InstrCode==30 && isa<PointerType>(I->getType())) {//load
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                auto rv = (Instruction *)I->getOperand(0);
                std::string indexRv = "R" + std::to_string(getIndexByInstr(rv));
                MayPointToInfo *newresult = new MayPointToInfo();
                for (auto &it:result->getInfosByIndex(indexRv)) {
                    for (auto &it2:result->getInfosByIndex(it)) {
                        newresult->addInfo("R"+std::to_string(tmp), it2);
                    }
                }
                result->join(result, newresult, result);
            }
            else if (InstrCode==31) {//store
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                auto rv = (Instruction *)I->getOperand(0);
                auto rp = (Instruction *)I->getOperand(1);
                std::string indexRv = "R" + std::to_string(getIndexByInstr(rv));
                std::string indexRp = "R" + std::to_string(getIndexByInstr(rp));
                MayPointToInfo *newresult = new MayPointToInfo();
                for (auto &it:result->getInfosByIndex(indexRv)) {
                    for (auto &it2:result->getInfosByIndex(indexRp)) {
                        newresult->addInfo(it2, it);
                    }
                }
                result->join(result, newresult, result);
            }
            else if (InstrCode==32) {//getelementptr
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                auto rv = (Instruction *)I->getOperand(0);
                std::string indexRv = "R" + std::to_string(getIndexByInstr(rv));
                MayPointToInfo *newresult = new MayPointToInfo();
                for (auto &it:result->getInfosByIndex(indexRv)) {
                    newresult->addInfo("R"+std::to_string(tmp), it);
                }
                result->join(result, newresult, result);
            }
            else if (InstrCode==47) {//bitcast
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                auto rv = (Instruction *)I->getOperand(0);
                std::string indexRv = "R" + std::to_string(getIndexByInstr(rv));
                MayPointToInfo *newresult = new MayPointToInfo();
                for (auto &it:result->getInfosByIndex(indexRv)) {
                    newresult->addInfo("R"+std::to_string(tmp), it);
                }
                result->join(result, newresult, result);
            }
            else if (InstrCode==53) {//phi
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                MayPointToInfo *newresult = new MayPointToInfo();
                Instruction* phiInstr = I;
                while (isa<PHINode>(phiInstr)) {
                    auto strictPhi = (PHINode *)phiInstr;
                    for (unsigned i=0;i<strictPhi->getNumOperands();i++) {
                        auto *opr = strictPhi->getIncomingValue(i);
                        std::string phiValueIndex = "R" + std::to_string(getIndexByInstr((Instruction*)opr));
                        for (auto &it:result->getInfosByIndex(phiValueIndex)) {
                            newresult->addInfo("R"+std::to_string(tmp), it);
                        }
                    }
                    phiInstr = phiInstr->getNextNode();
                }
            }
            else if (InstrCode==55) {//select
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
                auto rv1 = (Instruction *)I->getOperand(1);
                auto rv2 = (Instruction *)I->getOperand(2);
                std::string indexRv1 = "R" + std::to_string(getIndexByInstr(rv1));
                std::string indexRv2 = "R" + std::to_string(getIndexByInstr(rv2));
                MayPointToInfo *newresult = new MayPointToInfo();
                for (auto &it:result->getInfosByIndex(indexRv1)) {
                    newresult->addInfo("R"+std::to_string(tmp), it);
                }
                for (auto &it:result->getInfosByIndex(indexRv2)) {
                    newresult->addInfo("R"+std::to_string(tmp), it);
                }
                result->join(result, newresult, result);
            }
            else {//others
                for (auto val:IncomingEdges) {
                    result->join(result, getEdgeToInfo(std::make_pair(val, tmp)), result);
                }
            }

            for (unsigned i=0;i<OutgoingEdges.size();i++) {
                MayPointToInfo *tmpresult = new MayPointToInfo();
                auto resultInfo = result->getInfos();
                for (auto val=resultInfo.begin();val!=resultInfo.end();val++) {
                    for (auto &it:val->second) {
                        tmpresult->addInfo(val->first, it);
                    }
                }
                Infos[i] = tmpresult;
            }
            return;
        }
    public:
        MayPointToAnalysis(MayPointToInfo &bottom, MayPointToInfo &initialState):DataFlowAnalysis(bottom, initialState) {}
        ~MayPointToAnalysis() {}
    };

    struct MayPointToAnalysisPass : public FunctionPass {
        static char ID;
        MayPointToAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            MayPointToInfo *bottom = new MayPointToInfo();
            MayPointToInfo *initialState = new MayPointToInfo();
            MayPointToAnalysis mpta(*bottom, *initialState);
            mpta.runWorklistAlgorithm(&F);
            mpta.print();
            return false;
        }
    };
}

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", "May point to analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);


