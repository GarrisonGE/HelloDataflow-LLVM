#include "Liveness.h"

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "Liveness"

using namespace llvm;

namespace {
struct Liveness : public FunctionPass {
    string func_name = "test";
    static char ID;
    Liveness() : FunctionPass(ID) {}  
 
    bool runOnFunction(Function &F) override {

        string file_name = F.getParent()->getSourceFileName();
        //create *.out file
        int index = file_name.find(".");
        file_name = file_name.substr(0,index);
        string c = ".out";
        file_name.append(c);
        ofstream location_out;
        location_out.open(file_name, std::ios::out|std::ios::app);
        if (!location_out.is_open()) return 0;
        string resultOut;

        map<BasicBlock*, set<llvm::StringRef>> UE;// used to store UEVAR of each basic block
        map<BasicBlock*, set<llvm::StringRef>> VK;// used to store VARKILL of each basic block
        map<BasicBlock*, set<llvm::StringRef>> LO;//used to store sets of LIVEOUT of each basic block
        std::list<BasicBlock*> workList;//store the order of basicblock waitting to be computed
        if (F.getName()!= func_name) return 0;
        // errs() << "\n\n==================================== " << "Function Name is:"<< F.getName() << " ====================================" << "\n";

        //compute the set of UEVar and VarKill of each Basic Bolck
        for (BasicBlock &basic_block: F)
        {
        set<StringRef> UEName;//store the name of UE in this block
        set<StringRef> VKName;//store the name of VK in this block
            for(Instruction& inst: basic_block)
            {
                //if a variable is UEVar, it must be loaded before being stored
                if(inst.getOpcode() == Instruction::Load)
                {
                    Value* ptr = dyn_cast<Value>(&inst);//get the left operand 
                    StringRef varName = inst.getOperand(0)->getName();
                    if(VKName.find(varName) == VKName.end()) UEName.insert(varName);

                }
                //if a varibale is VarKill, then its value must be changed, so there must has a store operation for this variable.     
                if(inst.getOpcode() == Instruction::Store)
                {

                    StringRef varName1 = inst.getOperand(1)->getName();

                    VKName.insert(varName1);
                }     

            }
            UE.insert(make_pair(&basic_block,UEName));
            VK.insert(make_pair(&basic_block,VKName));
            
        }
        //compute the sets LIVEOUT of each basic block
        map<BasicBlock*, set<llvm::StringRef>>::iterator lit;
        // push basic bolck into worklist
        for (BasicBlock &basic_block : F) 
        {
            set<StringRef> LIVEOUT;
            LO.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(&basic_block,LIVEOUT));
            workList.push_back(&basic_block);// push back since we calculate the LIVEOUT backward
        }
        while (!workList.empty()) 
        {
            BasicBlock* tmp = workList.front();// basic_block pointer
            workList.pop_front();
            map<BasicBlock*, set<llvm::StringRef>>::iterator it; 
            it = LO.find(tmp);
            set<llvm::StringRef> originLIVEOUT = it->second;// original LIVEOUT
            // compute liveOut
            const auto *TInst = tmp->getTerminator();
            set<llvm::StringRef> resultSet;// result LIVEOUT
            for (int i = 0, NSucc = TInst->getNumSuccessors(); i < NSucc; i++)
            {
                BasicBlock* succ = TInst->getSuccessor(i);// get basic_block pointer
                // get successor's LIVEOUT/VARKILL/UEVAR
                set<llvm::StringRef> LIVEOUT = LO.find(succ)->second;
                set<llvm::StringRef> VarKill = VK.find(succ)->second;
                set<llvm::StringRef> UEVar = UE.find(succ)->second;
                set<llvm::StringRef> subtrSet (LIVEOUT);
                for (set<llvm::StringRef>::iterator setIt = VarKill.begin(); setIt != VarKill.end(); setIt++)
                {
                    subtrSet.erase(*setIt);
                }
                std::set_union(UEVar.begin(), UEVar.end(), subtrSet.begin(),subtrSet.end(), std::inserter(resultSet, resultSet.begin()));
            }
            LO.erase(it);// update the LIVEOUT for this basic_block
            LO.insert(std::pair<BasicBlock*, std::set<llvm::StringRef>>(tmp,resultSet));
            if (resultSet != originLIVEOUT) 
            {
                // if changed, add predecessor to worklist
                for (auto predIt = pred_begin(tmp), predEnd = pred_end(tmp); predIt != predEnd; predIt++) 
                {
                    BasicBlock* pred = *predIt;
                    workList.push_back(pred);
                }
            }
        }
        // output the UEVAR, VARKILL, LIVEOUT sets of each basic block
        for (auto& basic_block : F)
        {
            BasicBlock* key_basic_block = &basic_block;
            set<StringRef> VarKill = VK.find(key_basic_block)->second;
            set<StringRef> UEVar = UE.find(key_basic_block)->second;
            set<StringRef> LIVEOUT = LO.find(key_basic_block)->second;
            errs() << "----- "<< key_basic_block->getName() << " -----\n";
            errs() << "UEVAR: ";
            resultOut.append("----- ");
            resultOut.append(key_basic_block->getName());
            resultOut.append(" -----\n");
            resultOut.append("UEVAR: ");
            for (set<StringRef>::iterator it = UEVar.begin(); it != UEVar.end(); it++) 
            {
                errs() << *it << " ";
                resultOut.append(*it);
                resultOut.append(" ");
            }
            errs() << "\n";
            errs() << "VARKILL: ";
            resultOut.append("\n");
            resultOut.append("VARKILL: ");
            for (set<StringRef>::iterator it = VarKill.begin(); it != VarKill.end(); it++) 
            {
                errs() << *it << " ";
                resultOut.append(*it);
                resultOut.append(" ");
            }
            errs() << "\n";
            errs() << "LIVEOUT: ";
            resultOut.append("\n");
            resultOut.append("LIVEOUT: ");
            for (set<StringRef>::iterator it = LIVEOUT.begin(); it != LIVEOUT.end(); it++) 
            {
                errs() << *it << " ";
                resultOut.append(*it);
                resultOut.append(" ");
            }
            errs()<<"\n";
            resultOut.append("\n\n");
        }
        location_out<<resultOut;
        

    location_out.close();
    return false;
  }
}; 
}  

char Liveness::ID = 0;
static RegisterPass<Liveness> X("Liveness", "Liveness Analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);